/*
 * seccomp runtime detection
 *
 * Copyright (c) 2013 The Chromium OS Authors <chromium-os-dev@chromium.org>
 * Authors:
 *  Kees Cook <keescook@chromium.org>
 *
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE file.
 */
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <sys/prctl.h>
#include <linux/seccomp.h>

#include "seccomp-bpf.h"
#include "syscall-reporter.h"


/* http://outflux.net/teach-seccomp/ */
static int install_syscall_filter(void)
{
	struct sock_filter filter[] = {
		/* Validate architecture. */
		VALIDATE_ARCHITECTURE,
		/* Grab the system call number. */
		EXAMINE_SYSCALL,
		/* List allowed syscalls. */
		ALLOW_SYSCALL(rt_sigreturn),
#ifdef __NR_sigreturn
		ALLOW_SYSCALL(sigreturn),
#endif
		ALLOW_SYSCALL(exit_group),
		ALLOW_SYSCALL(exit),
		ALLOW_SYSCALL(read),
		ALLOW_SYSCALL(write),
		KILL_PROCESS,
	};
	struct sock_fprog prog = {
		.len = (unsigned short)(sizeof(filter)/sizeof(filter[0])),
		.filter = filter,
	};

#ifdef DEBUG
    printf("installing syscall reporter. Disable this for final build\n");
	if (install_syscall_reporter()) {
		perror("install_syscall_reporter()");
		goto failed;
    }
#endif

	if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)) {
		perror("prctl(NO_NEW_PRIVS)");
		goto failed;
	}
	if (prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog)) {
		perror("prctl(SECCOMP)");
		goto failed;
	}
    
	return 1;

failed:
	if (errno == EINVAL)
		fprintf(stderr, "SECCOMP_FILTER is not available. :(\n");
	return 0;
}

/* src: http://outflux.net/teach-seccomp/autodetect.html */
static int check_seccomp_filter(void)
{
    int ret;

    ret = prctl(PR_GET_SECCOMP, 0, 0, 0, 0);
    if (ret < 0) {
        switch (errno) {
        case ENOSYS:
                printf("seccomp not available: pre-2.6.23\n");
                return 0;
        case EINVAL:
                printf("seccomp not available: not built in\n");
                return 0;
        default:
                fprintf(stderr, "unknown PR_GET_SECCOMP error: %s\n",
                        strerror(errno));
                return 0;
        }
    }
    printf("seccomp available\n");

    ret = prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, NULL, 0, 0);
    if (ret < 0) {
        switch (errno) {
        case EINVAL:
                printf("seccomp filter not available\n");
                return 0;

        case EFAULT:
                printf("seccomp filter available\n");
                return 1;

        default:
                fprintf(stderr, "unknown PR_SET_SECCOMP error: %s\n",
                        strerror(errno));
                return 0;
        }
    }
    printf("PR_SET_SECCOMP unexpectedly succeeded?!\n");
    return 1;
}


int main(void)
{
    if (!check_seccomp_filter()) {
        printf("exiting, seccomp filter not available\n");
        exit(-1);
    }
    

    if (!install_syscall_filter()) {
        printf("install_syscall_filter failed\n");
        exit(-1);
    }
    
    printf("seccomp filter installed\n");
    if (!install_syscall_filter()) {
        printf("install_syscall_filter failed\n");
        exit(-1);
    }
    
}
