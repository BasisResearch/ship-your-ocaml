/* OS configuration for the bare-metal RV64 build: newlib over HTIF, no
 * processes, signals, sockets, dynamic loading or clocks. Everything not
 * listed is off, so the runtime takes its portable fallbacks. */
#define OCAML_OS_TYPE "Unix"
#define HAS_C99_FLOAT_OPS 1
#define HAS_WORKING_FMA 1
#define HAS_WORKING_ROUND 1
#define HAS_STDINT_H 1
#define HAS_UNISTD 1
#define HAS_STRERROR 1
#define HAS_FFS 1
