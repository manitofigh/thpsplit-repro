// SPDX-License-Identifier: GPL-2.0
/*
 * thpsplit: the deferred thp split shrinker takes each thp off its private
 * list with an unlocked list_del_init(); a partial unmap of the same thp
 * between its two stores queues the thp again and corrupts the queue.
 *
 * usage: thpsplit [SECONDS]   (as root, with thp enabled=always)
 */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <linux/futex.h>
#include <sched.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#define THP_SIZE	(2UL << 20)
#define PAGE		4096UL
#define NR_THP		128
#define CALIB_ROUNDS	15
#define DROP_CACHES	"/proc/sys/vm/drop_caches"
#define TAINT_WARN	512		/* set by the kernel's warnings */

struct shared {
	_Atomic int ready, go, done;
	long long t_go, delay;
};

static struct shared *sh;
static pid_t child_pid;		/* 0 in the child */
static const char *ok = "[+]", *err = "[-]";

static void __attribute__((noreturn)) die(const char *msg)
{
	fprintf(stderr, "%s thpsplit: %s: %s\n", err, msg, strerror(errno));
	if (child_pid > 0)
		kill(child_pid, SIGKILL);
	exit(2);
}

static long long now_ns(void)
{
	struct timespec ts;

	clock_gettime(CLOCK_MONOTONIC, &ts);
	return ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

static int tainted(void)
{
	FILE *f = fopen("/proc/sys/kernel/tainted", "r");
	int t;

	if (!f || fscanf(f, "%d", &t) != 1)
		die("/proc/sys/kernel/tainted");
	fclose(f);
	return t;
}

/* split attempts so far (done or failed): the shrinker reached our thps */
static long splits(void)
{
	FILE *f = fopen("/proc/vmstat", "r");
	char name[64];
	long val, sum = 0;

	if (!f)
		die("/proc/vmstat");
	while (fscanf(f, "%63s %ld", name, &val) == 2)
		if (!strcmp(name, "thp_split_page") ||
		    !strcmp(name, "thp_split_page_failed"))
			sum += val;
	fclose(f);
	return sum;
}

/* futex on shared memory: sleep until *addr == val (in the parent: or the child exits) */
static void wait_for(_Atomic int *addr, int val)
{
	struct timespec ts = { .tv_sec = 1 };
	int cur;

	while ((cur = *addr) != val) {
		syscall(SYS_futex, addr, FUTEX_WAIT, cur, &ts, NULL, 0);
		if (child_pid > 0 && waitpid(child_pid, NULL, WNOHANG) == child_pid) {
			fprintf(stderr, "%s thpsplit: the child exited\n", err);
			exit(2);
		}
	}
}

static void set_wake(_Atomic int *addr, int val)
{
	*addr = val;
	syscall(SYS_futex, addr, FUTEX_WAKE, INT_MAX, NULL, NULL, 0);
}

/* the thp owner: realtime on the shrinker's cpu, so its timer preempts it */
static void child(void)
{
	struct sched_param sp = { .sched_priority = 1 };
	size_t len = (NR_THP + 1) * THP_SIZE;
	struct timespec ts;
	char *map, *thp;
	long long t;
	int n, i;

	prctl(PR_SET_PDEATHSIG, SIGKILL);
	if (sched_setscheduler(0, SCHED_FIFO, &sp))
		die("sched_setscheduler");
	for (n = 1;; n++) {
		/* fresh thps: each one is queued for the shrinker at fault */
		map = mmap(NULL, len, PROT_READ | PROT_WRITE,
			   MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
		if (map == MAP_FAILED)
			die("mmap");
		thp = (char *)(((uintptr_t)map + THP_SIZE - 1) & ~(THP_SIZE - 1));
		for (i = 0; i < NR_THP; i++)
			thp[i * THP_SIZE] = 1;
		set_wake(&sh->ready, n);
		wait_for(&sh->go, n);

		/* preempt the shrinker at the chosen time, partially unmap all */
		t = sh->t_go + sh->delay;
		ts.tv_sec = t / 1000000000LL;
		ts.tv_nsec = t % 1000000000LL;
		clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &ts, NULL);
		for (i = 0; i < NR_THP; i++)
			madvise(thp + (i + 1) * THP_SIZE - PAGE, PAGE, MADV_DONTNEED);
		munmap(map, len);
		set_wake(&sh->done, n);
	}
}

/* the child's exit may still print kernel reports: let them finish */
static void stop_child(void)
{
	kill(child_pid, SIGKILL);
	waitpid(child_pid, NULL, 0);
	child_pid = 0;
	sleep(1);
}

static int cmp_ll(const void *a, const void *b)
{
	long long x = *(const long long *)a, y = *(const long long *)b;

	return (x > y) - (x < y);
}

int main(int argc, char **argv)
{
	int limit = argc > 1 ? atoi(argv[1]) : 600;
	long long calib[CALIB_ROUNDS], window = 0, aim = -1, start, t0;
	int fd, n, taint, misses = 0;
	cpu_set_t cpu0;
	long split0;
	double secs;

	setvbuf(stdout, NULL, _IOLBF, 0);
	if (isatty(STDOUT_FILENO)) {
		ok = "\033[32m[+]\033[0m";
		err = "\033[31m[-]\033[0m";
	}
	/* the report is detected by its taint flag, so it must be clear */
	taint = tainted();
	if (taint & TAINT_WARN) {
		fprintf(stderr, "%s thpsplit: kernel already tainted: reboot the VM first\n", err);
		return 2;
	}
	sh = mmap(NULL, sizeof(*sh), PROT_READ | PROT_WRITE,
		  MAP_SHARED | MAP_ANONYMOUS, -1, 0);
	if (sh == MAP_FAILED)
		die("mmap");
	/* 4: stop the kernel from logging every drop_caches write */
	fd = open(DROP_CACHES, O_WRONLY);
	if (fd < 0 || pwrite(fd, "4", 1, 0) < 0)
		die(DROP_CACHES);
	CPU_ZERO(&cpu0);
	CPU_SET(0, &cpu0);
	if (sched_setaffinity(0, sizeof(cpu0), &cpu0))
		die("sched_setaffinity");
	child_pid = fork();
	if (child_pid < 0)
		die("fork");
	if (child_pid == 0)
		child();

	srand(getpid());
	start = now_ns();
	for (n = 1;; n++) {
		wait_for(&sh->ready, n);
		/*
		 * calibration rounds: the child wakes long after the scan; then
		 * at random points of the drop_caches call, near the last point
		 * where the shrinker was seen working on our thps
		 */
		if (n <= CALIB_ROUNDS)
			sh->delay = 100000000;
		else if (aim < 0)
			sh->delay = rand() % window;
		else
			sh->delay = aim + rand() % (window / 4) - window / 8;
		if (sh->delay < 0)
			sh->delay = 0;
		split0 = splits();
		sh->t_go = now_ns() + 100000;
		set_wake(&sh->go, n);
		while (now_ns() < sh->t_go)
			;

		/* run all shrinkers; the deferred split one scans our thps */
		t0 = now_ns();
		if (pwrite(fd, "2", 1, 0) < 0)
			die(DROP_CACHES);
		if (n <= CALIB_ROUNDS)
			calib[n - 1] = now_ns() - t0;
		wait_for(&sh->done, n);

		if (n == CALIB_ROUNDS) {
			qsort(calib, CALIB_ROUNDS, sizeof(calib[0]), cmp_ll);
			window = calib[CALIB_ROUNDS / 2];
			printf("thpsplit: drop_caches takes %lld us; racing inside it\n",
			       window / 1000);
		} else if (n > CALIB_ROUNDS && splits() != split0) {
			aim = sh->delay;
			misses = 0;
		} else if (++misses == 50) {
			aim = -1;
		}
		secs = (now_ns() - start) / 1e9;
		if (tainted() != taint) {
			printf("%s thpsplit: bug: the kernel reported an error in round %d after %.1f s\n",
			       ok, n, secs);
			printf("LB-RESULT bug rounds=%d seconds=%.1f\n", n, secs);
			stop_child();
			return 0;
		}
		if (secs >= limit) {
			stop_child();
			printf("%s thpsplit: no bug in %d rounds, %.1f s\n", ok, n, secs);
			printf("LB-RESULT none rounds=%d seconds=%.1f\n", n, secs);
			return 1;
		}
		if (n % 500 == 0)
			printf("thpsplit: %d rounds, %.0f s\n", n, secs);
	}
}
