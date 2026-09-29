/* Force-included by tests/hostmirror.sh: system headers first, then route
 * the runtime's file-system calls to htif.c's in-memory implementations. */
#ifndef HOSTMIRROR_H
#define HOSTMIRROR_H
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>
int _open(const char *, int, int);
int _close(int);
ssize_t _read(int, void *, size_t);
ssize_t _write(int, const void *, size_t);
off_t _lseek(int, off_t, int);
int _fstat(int, struct stat *);
int _stat(const char *, struct stat *);
int _unlink(const char *);
int mf_rename(const char *, const char *);
#define open(p, f, ...) _open(p, f, 0)
#define close(fd) _close(fd)
#define read(fd, b, n) _read(fd, b, n)
#ifdef MIRROR_WRITE /* only unix.c: extern.c has its own static write() */
#define write(fd, b, n) _write(fd, b, n)
#endif
#define lseek(fd, o, w) _lseek(fd, o, w)
#define fstat(fd, s) _fstat(fd, s)
#define stat(p, s) _stat(p, s)
#define unlink(p) _unlink(p)
#define rename(a, b) mf_rename(a, b)
#define opendir mf_opendir
#define readdir mf_readdir
#define closedir mf_closedir
#endif
