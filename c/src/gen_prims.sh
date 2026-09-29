#!/bin/sh
# prims.c for the bare-metal runtime: the table of C primitives that the
# bytecode's PRIM section is resolved against. Same recipe as the rule in
# vendor/ocaml-4.14.2/runtime/Makefile (run from that directory).
set -e
export LC_ALL=C
cd "$1"
./gen_primitives.sh > "$2.list"
{
  echo '#include "caml/config.h"'
  echo 'typedef intnat value;'
  echo 'typedef value (*c_primitive)(void);'
  echo
  sed -e 's/.*/extern value &(void);/' "$2.list"
  echo
  echo 'c_primitive caml_builtin_cprim[] = {'
  sed -e 's/.*/  &,/' "$2.list"
  echo '  0 };'
  echo
  echo 'char * caml_names_of_builtin_cprim[] = {'
  sed -e 's/.*/  "&",/' "$2.list"
  echo '  0 };'
} > "$2"
