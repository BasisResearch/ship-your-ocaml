#!/bin/bash
# ship-your-ocaml gate (the analogue of ship-your-interpreter's
# scripts/check_all.sh, cut to what this repository contains):
#   (a1) build             — `lake build OCaml Vsa VsaIris` (the scaffold and the
#                            whole copied, retargeted machine layer);
#   (a2) no holes          — no sorry/admit/axiom/native_decide in OCaml/;
#   (a3) axioms            — every audited theorem (OCaml/Audit.lean) depends
#                            only on propext, Classical.choice, Quot.sound;
#   (a4) proof discipline  — scripts/check_discipline.py (rules in
#                            scripts/discipline_rules.tsv; O1-O4 cover OCaml/);
#   (a5) generated files   — OCaml/Bytecode/Opcode.lean and OCaml/Vm/Layout.lean
#                            are exactly what their generators emit;
#   (t1) TCB               — tcb/ builds, its lemmas' axioms are standard, and
#                            the quick OS-spec validation accepts every Linux
#                            trace (tcb/validation/quick.sh);
#   (a6) ELF pin           — c/ocamlrun-riscv-htif.elf matches c/ELF.sha256, and
#                            contains no `ecall` (a libgloss syscall stub would
#                            trap with no handler on the bare machine).
#   (a7) code pins         — every byte the retargeted library proofs pin
#                            (Vsa/Sim/Code/*.lean) is the ELF's byte there.
#   (a8) abstraction gate  — scripts/check_abstraction_gate.py: a cluster of hand
#                            proofs (abstractions/clusters.def) at 8+ proofs whose
#                            per-case cost did not fall by a third fails with
#                            "run /abstraction-discovery".
# Heavy steps honour the shared-machine rules (30 GB cap).
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }
# lake builds run under a 30 GB address-space cap; lean needs more virtual
# address space than that for its thread stacks, so the audit runs uncapped
# (it only loads .olean files).

echo "== stage a1: lake build OCaml Vsa VsaIris (under a 30 GB cgroup cap)"
systemd-run --user --scope -q -p MemoryMax=30G lake build OCaml Vsa VsaIris 2>&1 | tail -1 \
  | grep -q "Build completed successfully" || fail "stage a1: build"
echo "stage a1: OK"

echo "== stage a2: no holes in OCaml/"
python3 scripts/check_holes.py || fail "stage a2: hole found"
echo "stage a2: OK"

echo "== stage a3: axiom audit"
out=$(lake env lean OCaml/Audit.lean 2>&1)
echo "$out"
n=$(echo "$out" | grep -c "depends on axioms")
bad=$(echo "$out" | grep "depends on axioms" | grep -vE "axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]$" || true)
[ -z "$bad" ] || fail "stage a3: non-standard axioms: $bad"
[ "$n" -ge 23 ] || fail "stage a3: expected >= 23 audited theorems, got $n"
echo "stage a3: OK ($n theorems audited)"

echo "== stage a4: proof discipline"
python3 scripts/check_discipline.py || fail "stage a4: discipline violation"
echo "stage a4: OK"

echo "== stage a5: generated files are current"
python3 scripts/gen_opcodes.py | cmp -s - OCaml/Bytecode/Opcode.lean || fail "stage a5: Opcode.lean differs from gen_opcodes.py"
python3 scripts/gen_layout.py | cmp -s - OCaml/Vm/Layout.lean || fail "stage a5: Layout.lean differs from gen_layout.py"
echo "stage a5: OK"

echo "== stage a6: ELF pin, and no ecall in the image"
n=$($HOME/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-objdump -d c/ocamlrun-riscv-htif.elf | grep -cw ecall)
[ "$n" = 0 ] || fail "stage a6: $n ecall instruction(s) linked (libgloss syscall stubs trap on the bare machine)"
(cd c && sha256sum -c ELF.sha256) || fail "stage a6: ELF sha256"
echo "stage a6: OK"
echo "== stage a7: retargeted library proofs pin this ELF's bytes"
python3 scripts/check_code_pins.py | tail -1
python3 scripts/check_code_pins.py > /dev/null || fail "stage a7: code pins differ from the ELF"
echo "stage a7: OK"

echo "== stage t1: trusted computing base (tcb/)"
systemd-run --user --scope -q -p MemoryMax=30G lake build TCB tcbcheck 2>&1 | tail -1 | grep -q "Build completed successfully" || fail "stage t1: build TCB"
out=$(lake env lean tcb/Audit.lean 2>&1)
echo "$out"
bad=$(echo "$out" | grep "depends on axioms" | grep -vE "axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]$" || true)
[ -z "$bad" ] || fail "stage t1: non-standard axioms: $bad"
tcb/validation/quick.sh || fail "stage t1: OS-spec validation (quick): a Linux trace was rejected"
echo "stage t1: OK"
echo "== stage a8: abstraction-discovery gate"
python3 scripts/check_abstraction_gate.py || fail "stage a8: run /abstraction-discovery"
echo "stage a8: OK"
echo "ALL STAGES OK"
