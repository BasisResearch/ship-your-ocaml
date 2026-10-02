#include <stdio.h>
#include <caml/callback.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>

static value closure(const char *name) { return *caml_named_value(name); }
static void show(const char *name, value r) {
  if (Is_exception_result(r))
    printf("%s exception:%ld\n", name, (long)Long_val(Field(Extract_exception(r), 1)));
  else printf("%s ok:%ld\n", name, (long)Long_val(r));
}
int main(int argc, char **argv) {
  (void)argc;
  caml_main(argv);
  CAMLparam0();
  CAMLlocal1(r);
  value args[5] = {Val_int(1), Val_int(2), Val_int(3), Val_int(4), Val_int(5)};
  r = caml_callback_exn(closure("one"), Val_int(41)); show("one", r);
  r = caml_callback2_exn(closure("two"), Val_int(40), Val_int(2)); show("two", r);
  r = caml_callback3_exn(closure("three"), Val_int(10), Val_int(12), Val_int(20)); show("three", r);
  r = caml_callbackN_exn(closure("five"), 5, args); show("five", r);
  r = caml_callback_exn(closure("raise1"), Val_int(7)); show("raise1", r);
  r = caml_callback2_exn(closure("raise2"), Val_int(7), Val_int(8)); show("raise2", r);
  r = caml_callback3_exn(closure("raise3"), Val_int(7), Val_int(8), Val_int(9)); show("raise3", r);
  CAMLreturnT(int, 0);
}
