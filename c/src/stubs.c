/* Symbols the 4.14.4 bytecode runtime references but does not define when
 * built without sockets (debugger.c compiles to nothing). */
#define CAML_INTERNALS
#include "caml/mlvalues.h"
#include "caml/misc.h"

/* Called by caml_interprete only for a BREAK instruction, which only the
 * debugger (absent here) plants into the code. */
opcode_t caml_debugger_saved_instruction(code_t pc) {
    (void)pc;
    caml_fatal_error("BREAK instruction without a debugger");
}
