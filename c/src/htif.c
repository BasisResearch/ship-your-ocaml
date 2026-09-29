/* HTIF back end for newlib, with a small in-memory file system.
 *
 * Console output is the riscv-tests HTIF convention (device 1 / command 1
 * through the 64-bit `tohost` mailbox), exit is device 0 with the low
 * payload bit set -- exactly ship-your-interpreter's c/src/htif.c, which
 * the Sail Lean emulator implements.
 *
 * ocamlrun is an ordinary POSIX program: caml_main() open()s the bytecode
 * executable named on its command line, lseek()s to the trailer and
 * read()s the sections. Instead of patching the runtime, this file gives
 * newlib a file system whose files are the blobs linked into the image by
 * embed.S (read-only), plus files the program creates (heap-backed, so
 * e.g. ocamlc can write its .cmi/.cmo outputs). No other OS services
 * exist: no processes, signals or clocks; directories are path prefixes. */
#include <sys/stat.h>
#include <sys/types.h>
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* --- HTIF ---------------------------------------------------------------- */

/* The host locates these by the section name `.tohost` in the ELF. */
volatile uint64_t tohost __attribute__((section(".tohost"), aligned(8)));
volatile uint64_t fromhost __attribute__((section(".tohost"), aligned(8)));

#define HTIF_DEV_CONSOLE (1ULL << 56)
#define HTIF_CMD_WRITE   (1ULL << 48)

/* Each 8-byte store is a complete HTIF command; the sail model processes
 * it synchronously and clears the mailbox, so no ready-polling is needed. */
#ifndef HOST_MIRROR
static void htif_putc(char c) {
    tohost = HTIF_DEV_CONSOLE | HTIF_CMD_WRITE | (uint8_t)c;
}

void _exit(int code) {
    tohost = ((uint64_t)(uint32_t)code << 1) | 1;
    for (;;) {}
}
#else
/* tests/hostmirror.sh: the same file system on a Linux host, console to
 * the host's stdout (see there). */
extern ssize_t write(int, const void *, size_t);
static void htif_putc(char c) { write(1, &c, 1); }
#endif

/* --- in-memory files ----------------------------------------------------- */

struct embedded_file { const char *path; const char *start; const char *end; };
extern const struct embedded_file embedded_files[]; /* embed.S, NULL-terminated */

#define MAX_FILES 64
#define MAX_FDS   32
#define FD_BASE   3

struct mfile {
    char *path;          /* NULL: slot free */
    char *data;
    size_t size, cap;
    int writable;        /* 0: points into the image (embedded) */
};
struct mfd { struct mfile *f; size_t pos; int flags; };

static struct mfile files[MAX_FILES];
static struct mfd fds[MAX_FDS];
static int fs_ready;

static void fs_init(void) {
    if (fs_ready) return;
    fs_ready = 1;
    for (int i = 0; embedded_files[i].path && i < MAX_FILES; i++) {
        files[i].path = (char *)embedded_files[i].path;
        files[i].data = (char *)embedded_files[i].start;
        files[i].size = (size_t)(embedded_files[i].end - embedded_files[i].start);
        files[i].writable = 0;
    }
}

static struct mfile *lookup(const char *path) {
    fs_init();
    for (int i = 0; i < MAX_FILES; i++)
        if (files[i].path && strcmp(files[i].path, path) == 0) return &files[i];
    return NULL;
}

static struct mfile *create(const char *path) {
    for (int i = 0; i < MAX_FILES; i++)
        if (!files[i].path) {
            size_t n = strlen(path) + 1;
            files[i].path = malloc(n);
            if (!files[i].path) return NULL;
            memcpy(files[i].path, path, n);
            files[i].data = NULL;
            files[i].size = files[i].cap = 0;
            files[i].writable = 1;
            return &files[i];
        }
    return NULL;
}

/* Copy-on-write for an embedded file opened for writing. */
static int make_writable(struct mfile *f) {
    if (f->writable) return 0;
    char *d = malloc(f->size ? f->size : 1);
    if (!d) return -1;
    memcpy(d, f->data, f->size);
    f->data = d; f->cap = f->size; f->writable = 1;
    return 0;
}

static struct mfd *getfd(int fd) {
    if (fd < FD_BASE || fd >= FD_BASE + MAX_FDS || !fds[fd - FD_BASE].f) return NULL;
    return &fds[fd - FD_BASE];
}

int _open(const char *path, int flags, int mode) {
    (void)mode;
    struct mfile *f = lookup(path);
    if (!f) {
        if (!(flags & O_CREAT)) { errno = ENOENT; return -1; }
        if (!(f = create(path))) { errno = ENOSPC; return -1; }
    } else if ((flags & O_CREAT) && (flags & O_EXCL)) {
        errno = EEXIST; return -1;
    }
    if ((flags & O_ACCMODE) != O_RDONLY) {
        if (make_writable(f) < 0) { errno = ENOMEM; return -1; }
        if (flags & O_TRUNC) f->size = 0;
    }
    for (int i = 0; i < MAX_FDS; i++)
        if (!fds[i].f) {
            fds[i].f = f; fds[i].pos = 0; fds[i].flags = flags;
            return FD_BASE + i;
        }
    errno = EMFILE;
    return -1;
}

int _close(int fd) {
    struct mfd *d = getfd(fd);
    if (d) d->f = NULL;
    return 0;
}

ssize_t _read(int fd, void *buf, size_t len) {
    struct mfd *d = getfd(fd);
    if (!d) return 0; /* stdin: EOF, no console input over HTIF */
    size_t avail = d->pos < d->f->size ? d->f->size - d->pos : 0;
    if (len > avail) len = avail;
    memcpy(buf, d->f->data + d->pos, len);
    d->pos += len;
    return (ssize_t)len;
}

ssize_t _write(int fd, const void *buf, size_t len) {
    const char *p = buf;
    struct mfd *d = getfd(fd);
    if (!d) { /* stdout and stderr both go to the HTIF console */
        for (size_t i = 0; i < len; i++) htif_putc(p[i]);
        return (ssize_t)len;
    }
    struct mfile *f = d->f;
    if (d->flags & O_APPEND) d->pos = f->size;
    if (d->pos + len > f->cap) {
        size_t cap = f->cap ? f->cap : 256;
        while (cap < d->pos + len) cap *= 2;
        char *nd = realloc(f->data, cap);
        if (!nd) { errno = ENOSPC; return -1; }
        f->data = nd; f->cap = cap;
    }
    if (d->pos > f->size) memset(f->data + f->size, 0, d->pos - f->size);
    memcpy(f->data + d->pos, p, len);
    d->pos += len;
    if (d->pos > f->size) f->size = d->pos;
    return (ssize_t)len;
}

off_t _lseek(int fd, off_t offset, int whence) {
    struct mfd *d = getfd(fd);
    if (!d) { errno = ESPIPE; return -1; }
    off_t base = whence == SEEK_SET ? 0
               : whence == SEEK_CUR ? (off_t)d->pos : (off_t)d->f->size;
    if (base + offset < 0) { errno = EINVAL; return -1; }
    d->pos = (size_t)(base + offset);
    return (off_t)d->pos;
}

static void fill_stat(struct mfile *f, struct stat *st) {
    memset(st, 0, sizeof *st);
    st->st_mode = S_IFREG | 0644;
    st->st_size = (off_t)f->size;
    st->st_nlink = 1;
}

int _fstat(int fd, struct stat *st) {
    struct mfd *d = getfd(fd);
    if (!d) { memset(st, 0, sizeof *st); st->st_mode = S_IFCHR; return 0; }
    fill_stat(d->f, st);
    return 0;
}

int _stat(const char *path, struct stat *st) {
    struct mfile *f = lookup(path);
    if (!f) { errno = ENOENT; return -1; }
    fill_stat(f, st);
    return 0;
}

int _unlink(const char *path) {
    struct mfile *f = lookup(path);
    if (!f) { errno = ENOENT; return -1; }
    if (f->writable) { free(f->data); free(f->path); }
    memset(f, 0, sizeof *f);
    return 0;
}

int rename(const char *from, const char *to) {
    struct mfile *f = lookup(from);
    if (!f) { errno = ENOENT; return -1; }
    struct mfile *g = lookup(to);
    if (g && g != f) _unlink(to);
    size_t n = strlen(to) + 1;
    char *p = malloc(n);
    if (!p) { errno = ENOMEM; return -1; }
    memcpy(p, to, n);
    if (f->writable) free(f->path);
    f->path = p;
    return 0;
}

int _link(const char *from, const char *to) { (void)from; (void)to; errno = EMLINK; return -1; }
int _isatty(int fd) { return fd < FD_BASE; }

/* --- heap -------------------------------------------------------------- */

extern char _end[];       /* from link.ld */
extern char __heap_end[];

void *_sbrk(ptrdiff_t incr) {
    static char *brk;
    if (!brk) brk = _end;
    if (brk + incr > __heap_end) { errno = ENOMEM; return (void *)-1; }
    char *prev = brk;
    brk += incr;
    return prev;
}

/* --- time ------------------------------------------------------------- */

/* There is no clock. newlib's libgloss implements _gettimeofday (and
 * _times, through it) with an `ecall`, which on this bare machine traps
 * with no handler and never returns: these replace them with a clock that
 * stays at 0, so Sys.time and the compiler's Profile timers are
 * deterministic. scripts/check_all.sh fails if an ecall is linked. */
#include <sys/time.h>
#include <sys/times.h>
int _gettimeofday(struct timeval *tv, void *tz) {
    (void)tz;
    if (tv) { tv->tv_sec = 0; tv->tv_usec = 0; }
    return 0;
}
clock_t _times(struct tms *t) {
    if (t) memset(t, 0, sizeof *t);
    return 0;
}

/* --- process ----------------------------------------------------------- */

int _kill(int pid, int sig) { (void)pid; (void)sig; errno = EINVAL; return -1; }
int _getpid(void) { return 1; }
pid_t getppid(void) { return 0; }
uid_t getuid(void) { return 0; }
uid_t geteuid(void) { return 0; }
gid_t getgid(void) { return 0; }
gid_t getegid(void) { return 0; }
int chdir(const char *path) { (void)path; errno = ENOENT; return -1; }
int mkdir(const char *path, mode_t mode) { (void)path; (void)mode; errno = EROFS; return -1; }
int rmdir(const char *path) { (void)path; errno = ENOENT; return -1; }

/* --- directories -------------------------------------------------------- */

/* A directory is a path prefix: readdir lists the distinct first components
 * of the files below it (OCaml 4.14's Load_path indexes include directories
 * with Sys.readdir, so ocamlc needs this to find .cmi files). */
#include "sys/dir.h"
struct baremetal_dir { char path[256]; size_t plen; int next; struct direct ent; };
static struct baremetal_dir dirs[4];

DIR *opendir(const char *name) {
    fs_init();
    size_t n = strlen(name);
    while (n > 1 && name[n - 1] == '/') n--;
    if (n >= sizeof dirs[0].path - 1) { errno = ENAMETOOLONG; return NULL; }
    int found = 0;
    for (int i = 0; i < MAX_FILES && !found; i++)
        if (files[i].path && strncmp(files[i].path, name, n) == 0 &&
            files[i].path[n] == '/')
            found = 1;
    if (!found) { errno = ENOENT; return NULL; }
    for (int i = 0; i < 4; i++)
        if (dirs[i].plen == 0) {
            memcpy(dirs[i].path, name, n);
            dirs[i].path[n] = '/';
            dirs[i].plen = n + 1;
            dirs[i].next = 0;
            return &dirs[i];
        }
    errno = EMFILE;
    return NULL;
}

struct direct *readdir(DIR *d) {
    for (; d->next < MAX_FILES; d->next++) {
        struct mfile *f = &files[d->next];
        if (!f->path || strncmp(f->path, d->path, d->plen) != 0) continue;
        const char *rest = f->path + d->plen;
        size_t k = strcspn(rest, "/");
        if (k == 0 || k >= sizeof d->ent.d_name) continue;
        /* report each child once: skip it if an earlier file had it */
        int dup = 0;
        for (int j = 0; j < d->next && !dup; j++)
            if (files[j].path && strncmp(files[j].path, d->path, d->plen) == 0 &&
                strncmp(files[j].path + d->plen, rest, k) == 0 &&
                (files[j].path[d->plen + k] == '/' || files[j].path[d->plen + k] == 0))
                dup = 1;
        if (dup) continue;
        memcpy(d->ent.d_name, rest, k);
        d->ent.d_name[k] = 0;
        d->next++;
        return &d->ent;
    }
    return NULL;
}

int closedir(DIR *d) { d->plen = 0; return 0; }
