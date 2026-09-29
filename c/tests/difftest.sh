#!/bin/bash
# Differential test: host ocamlrun (4.14.4, same vendored source) vs the
# bare-metal ELF on the Sail Lean emulator. Both run the SAME bytecode
# executable (host ocamlc -o x.byte x.ml). Compares stdout and the exit
# status. Reports Sail steps, the cut-point step (2nd caml_interprete call)
# and the number of minor collections after it (tests/sail_run.py).
#   EMU=... JOBS=8 RUNPARAM=s=4M tests/difftest.sh [files.ml...]
set -u
cd "$(dirname "$0")/.."
JOBS=${JOBS:-8}
RUNPARAM=${RUNPARAM:-}
OCAMLBIN=${OCAMLBIN:-$HOME/toolchains/ocaml-4.14.4/bin}
OUT=build/difftest${RUNPARAM:+-$RUNPARAM}
mkdir -p $OUT
files=("$@"); [ ${#files[@]} -eq 0 ] && files=(tests/difftest/*.ml)
for f in "${files[@]}"; do
  n=$(basename $f .ml)
  (cd $OUT && $OCAMLBIN/ocamlc -o $n.byte $(realpath ../../$f)) || { echo "$n COMPILE-FAIL"; continue; }
  make -s ELF=$OUT/$n.elf BUILD=$OUT/$n.d PROG=$OUT/$n.byte RUNPARAM=$RUNPARAM >/dev/null 2>&1 \
    || { echo "$n BUILD-FAIL"; continue; }
  OCAMLRUNPARAM=$RUNPARAM $OCAMLBIN/ocamlrun $OUT/$n.byte > $OUT/$n.host 2>/dev/null; echo $? > $OUT/$n.host.rc
done
run1() {
  n=$1
  tests/sail_run.py $OUT/$n.elf --json $OUT/$n.json > /dev/null 2>&1
  python3 -c "import json,sys; d=json.load(open('$OUT/$n.json')); sys.stdout.write(d['output']); open('$OUT/$n.emu.rc','w').write(str(d['exit'])+'\n')" > $OUT/$n.emu
}
export -f run1; export OUT
[ -n "${NORUN:-}" ] || for f in "${files[@]}"; do basename $f .ml; done | xargs -P $JOBS -I{} bash -c 'run1 {}'
pass=0; fail=0
printf '%-14s %-6s %-5s %-5s %11s %11s %6s\n' test result host emu sail-steps cut-point minorGC
for f in "${files[@]}"; do
  n=$(basename $f .ml)
  hr=$(cat $OUT/$n.host.rc); er=$(cat $OUT/$n.emu.rc 2>/dev/null || echo '?')
  read steps cut gcs < <(python3 -c "
import json; d=json.load(open('$OUT/$n.json'))
print(d['steps'], d['cut_point_step'], d['minor_gcs_after_cut'])" 2>/dev/null || echo "? ? ?")
  if cmp -s $OUT/$n.host $OUT/$n.emu && [ "$hr" = "$er" ]; then
    r=PASS; pass=$((pass+1)); else r=FAIL; fail=$((fail+1)); fi
  printf '%-14s %-6s %-5s %-5s %11s %11s %6s\n' $n $r $hr $er "$steps" "$cut" "$gcs"
done
echo "pass=$pass fail=$fail"
[ $fail = 0 ]
