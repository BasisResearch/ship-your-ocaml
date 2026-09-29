/* Machine configuration for the bare-metal RV64 build (rv64i, lp64,
 * little-endian). Hand-written in place of configure's output; matches
 * the host 4.14.4 configuration in every setting that affects the
 * bytecode format (ARCH_SIXTYFOUR, CAML_SAFE_STRING, FLAT_FLOAT_ARRAY,
 * naked pointers allowed). */
#define ARCH_SIXTYFOUR 1
#define SIZEOF_INT 4
#define SIZEOF_LONG 8
#define SIZEOF_PTR 8
#define SIZEOF_SHORT 2
#define SIZEOF_LONGLONG 8
#define ARCH_INT64_TYPE long
#define ARCH_UINT64_TYPE unsigned long
#define ARCH_INT64_PRINTF_FORMAT "l"
#define PROFINFO_WIDTH 0
#define CAML_SAFE_STRING 1
#define FLAT_FLOAT_ARRAY 1
#define SUPPORTS_ALIGNED_ATTRIBUTE 1
