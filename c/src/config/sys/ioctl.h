/* Empty stand-in: newlib for bare metal has no <sys/ioctl.h>. unix.c only
 * uses ioctl under #ifdef TIOCGWINSZ, which stays undefined. */
