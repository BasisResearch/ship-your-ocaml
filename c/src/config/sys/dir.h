/* Stand-in for <sys/dir.h> (s.h leaves HAS_DIRENT off): the in-memory file
 * system's directories are path prefixes (see htif.c). */
#ifndef BAREMETAL_SYS_DIR_H
#define BAREMETAL_SYS_DIR_H
struct direct { char d_name[256]; };
typedef struct baremetal_dir DIR;
DIR *opendir(const char *name);
struct direct *readdir(DIR *d);
int closedir(DIR *d);
#endif
