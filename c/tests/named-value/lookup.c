#include <caml/mlvalues.h>
#include <caml/callback.h>

/* Validation only: expose the vendored runtime's named-root table to OCaml. */
CAMLprim value test_named_value_lookup(value name)
{
  const value *slot = caml_named_value(String_val(name));
  return slot == NULL ? Val_int(-1) : *slot;
}
