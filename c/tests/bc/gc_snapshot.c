/* Validation-only linker wrapper: observe quick_stat without changing its
   returned OCaml value or allocating any OCaml heap objects. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <caml/mlvalues.h>

value __real_caml_gc_quick_stat(value unit);
value __wrap_caml_gc_quick_stat(value unit) {
  value result = __real_caml_gc_quick_stat(unit);
  const char *path = getenv("BC_GC_SNAPSHOTS");
  if (path) {
    FILE *out = fopen(path, "a");
    if (!out) abort();
    for (int i = 0; i < 17; i++) {
      if (i) fputc(',', out);
      if (i < 3) {
        double d = Double_val(Field(result, i));
        uint64_t bits;
        memcpy(&bits, &d, sizeof bits);
        fprintf(out, "%llu", (unsigned long long)bits);
      } else {
        fprintf(out, "%lld", (long long)Long_val(Field(result, i)));
      }
    }
    fputc('\n', out);
    fclose(out);
  }
  return result;
}
