/* Bare-metal entry for ocamlrun (OCaml 4.14.4) under HTIF.
 *
 * Replaces runtime/main.c. The command line and OCAMLRUNPARAM are baked
 * in at build time (there is no host to pass them): argv is
 *   { "ocamlrun", "/prog", OCAML_ARGS... }
 * where /prog is the bytecode executable embedded by embed.S, so
 * caml_main() takes its ordinary `ocamlrun prog args` path: it opens /prog
 * in htif.c's in-memory file system, reads the trailer and sections,
 * fixes up and threads the code, unmarshals the global data and runs
 * caml_interprete on it. The verification cut point (Layer A) is that
 * call to caml_interprete, with the executable loaded.
 *
 * Exit codes are ocamlrun's: 0 ok, 2 uncaught exception, `exit n` = n. */
#define CAML_INTERNALS
#include <stdlib.h>
#include "caml/misc.h"
#include "caml/mlvalues.h"
#include "caml/sys.h"
#include "caml/callback.h"

#ifndef OCAML_ARGS
#define OCAML_ARGS
#endif
#ifndef OCAMLRUNPARAM
#define OCAMLRUNPARAM ""
#endif

extern char **environ;

static char *baked_env[] = { "OCAMLRUNPARAM=" OCAMLRUNPARAM, NULL };
static char *baked_argv[] = { "ocamlrun", "/prog", OCAML_ARGS NULL };

int main(void) {
    environ = baked_env;
    caml_main(baked_argv);
    caml_do_exit(0);
    return 0; /* not reached */
}
