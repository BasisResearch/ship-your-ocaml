#!/bin/bash
# ship-your-ocaml gate (the analogue of ship-your-interpreter's
# scripts/check_all.sh, cut to what this repository contains):
#   (a1) build             — `lake build OCaml OCaml.Audit Vsa VsaIris` (the scaffold and the
#                            whole copied, retargeted machine layer);
#   (a2) no holes          — no sorry/admit/axiom/native_decide in OCaml/;
#   (a3) axioms            — every audited theorem (OCaml/Audit.lean) depends
#                            only on propext, Classical.choice, Quot.sound;
#   (a4) proof discipline  — scripts/check_discipline.py (rules in
#                            scripts/discipline_rules.tsv; O1-O4 cover OCaml/);
#   (a5) generated files   — opcode/layout/boot facts, complete ELF decode
#                            coverage, library pins and retargeted specs
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
# Heavy steps honour the shared-machine rules (24 GB cap).
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }
# Apply the lane's shared-machine limit to builds and axiom audits alike.
run_lean() {
  while :; do
    free -g
    avail=$(free -g | awk '/^Mem:/{print $7}')
    [ "$avail" -ge 25 ] && break
    echo "check_all: ${avail} GB available (< 25), waiting" >&2
    sleep 120
  done
  systemd-run --user --scope -q -p MemoryMax=24G "$@"
}

# Lean may wrap a long theorem's axiom list. Normalize only those reports;
# incomplete lists remain malformed and fail the allow-list check below.
normalize_axioms() {
  awk '/depends on axioms: \[/ {
    while ($0 !~ /\]$/ && (getline continuation) > 0) $0 = $0 " " continuation
    gsub(/,[[:space:]]+/, ", ")
  } { print }'
}

echo "== stage a1: lake build OCaml OCaml.Audit Vsa VsaIris (under a 24 GB cgroup cap)"
run_lean lake build OCaml OCaml.Audit Vsa VsaIris runbc bootdump 2>&1 | tail -1 \
  | grep -q "Build completed successfully" || fail "stage a1: build"
echo "stage a1: OK"

echo "== stage a2: no holes in OCaml/"
python3 scripts/check_holes.py || fail "stage a2: hole found"
echo "stage a2: OK"

echo "== stage a3: axiom audit"
out=$(run_lean lake env lean OCaml/Audit.lean 2>&1) || { echo "$out"; fail "stage a3: Lean audit failed"; }
out=$(echo "$out" | normalize_axioms)
echo "$out"
n=$(echo "$out" | grep -c "depends on axioms")
bad=$(echo "$out" | grep "depends on axioms" | grep -vE "axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]$" || true)
[ -z "$bad" ] || fail "stage a3: non-standard axioms: $bad"
[ "$n" -ge 38 ] || fail "stage a3: expected >= 38 audited theorems, got $n"
echo "stage a3: OK ($n theorems audited)"

echo "== stage a4: proof discipline"
python3 scripts/check_discipline.py || fail "stage a4: discipline violation"
echo "stage a4: OK"

echo "== stage a5: generated files are current"
python3 scripts/gen_gc_rows.py --check || fail "stage a5: GC row/code drift"
python3 scripts/gc_cfg.py --check || fail "stage a5: collector CFG drift"
python3 scripts/gen_lazy_force.py --check || fail "stage a5: Lazy.force bytecode drift"
python3 scripts/check_lazy_force.py || fail "stage a5: Lazy.force host/BcSem mismatch"
python3 scripts/gen_opcodes.py | cmp -s - OCaml/Bytecode/Opcode.lean || fail "stage a5: Opcode.lean differs from gen_opcodes.py"
python3 scripts/gen_primitive_census.py --check || fail "stage a5: F1 primitive census drift"
python3 scripts/syi/gen_fn.py --ocaml-constants --check || fail "stage a5: F1 constant summary drift"
python3 scripts/syi/gen_fn.py --ocaml-compare --check || fail "stage a5: F1 comparison summary drift"
python3 scripts/syi/gen_fn.py --ocaml-argv --check || fail "stage a5: F1 argv summary drift"
python3 scripts/syi/gen_fn.py --ocaml-lengths --check || fail "stage a5: F1 string-length summary drift"
python3 scripts/syi/gen_fn.py --ocaml-counter --check || fail "stage a5: F1 counter summary drift"
python3 scripts/syi/gen_fn.py --ocaml-string-scan --check || fail "stage a5: F1 string scan summary drift"
python3 scripts/syi/gen_fn.py --ocaml-string-wrapper --check || fail "stage a5: F1 string wrapper summary drift"
python3 scripts/syi/gen_fn.py --ocaml-allocation --check || fail "stage a5: F1 allocation certificate drift"
python3 scripts/gen_layout.py | cmp -s - OCaml/Vm/Layout.lean || fail "stage a5: Layout.lean differs from gen_layout.py"
python3 scripts/gen_boot_observation.py results/boot/while_min-cut.json | cmp -s - OCaml/Vm/Boot/WhileMinObservation.lean || fail "stage a5: boot observation differs from generator"
python3 scripts/gen_boot_log.py --check || fail "stage a5: boot log certificate drift"
python3 scripts/gen_boot_runtime.py --check || fail "stage a5: boot runtime read drift"
python3 scripts/gen_boot_heap.py --check || fail "stage a5: boot heap certificate drift"
python3 scripts/gen_boot_entry.py --check || fail "stage a5: boot entry certificate drift"
python3 scripts/gen_boot_image.py --check || fail "stage a5: boot image drift"
python3 scripts/gen_boot_dump.py --check || fail "stage a5: boot capture utility drift"
python3 scripts/gen_boot_registers.py --check || fail "stage a5: boot register/snapshot drift"
python3 scripts/gen_startup_rows.py --check || fail "stage a5: startup row/call drift"
python3 scripts/gen_boot_primitives.py --check || fail "stage a5: boot primitive binding drift"
python3 scripts/gen_elf_decode.py --check || fail "stage a5: ELF decode table drift"
python3 scripts/gen_library_pins.py --check || fail "stage a5: A0 library code pin drift"
python3 scripts/gen_library_layout.py --check || fail "stage a5: library layout drift"
python3 scripts/syi/gen_alloc_steps.py --check || fail "stage a5: allocator step/code drift"
python3 scripts/retarget_allocator_specs.py --check || fail "stage a5: allocator composition drift"
python3 scripts/retarget_stdio_specs.py --check || fail "stage a5: stdio composition/image drift"
python3 scripts/retarget_library_sites.py --check || fail "stage a5: A0 library site drift"
python3 scripts/gen_ocaml_image.py | cmp -s - OCaml/Vm/ImageData.lean || fail "stage a5: OCaml image pins differ from generator"
python3 scripts/gen_unary_arms.py --check || fail "stage a5: unary arm bridge drift"
python3 scripts/gen_field_arms.py --check || fail "stage a5: field arm bridge drift"
python3 scripts/gen_conditional_arms.py --check || fail "stage a5: conditional arm bridge drift"
python3 scripts/gen_compare_branch_arms.py --check || fail "stage a5: comparison branch bridge drift"
python3 scripts/gen_binary_arms.py --check || fail "stage a5: binary arm bridge drift"
python3 scripts/gen_equality_arms.py --check || fail "stage a5: equality arm bridge drift"
python3 scripts/gen_push_arms.py --check || fail "stage a5: push arm bridge drift"
python3 scripts/gen_closure_offset_arms.py --check || fail "stage a5: closure-offset arm drift"
python3 scripts/gen_byte_arms.py --check || fail "stage a5: byte arm bridge drift"
python3 scripts/gen_indexed_arms.py --check || fail "stage a5: indexed arm bridge drift"
python3 scripts/gen_global_field_arms.py --check || fail "stage a5: global field arm bridge drift"
python3 scripts/gen_atom_arms.py --check || fail "stage a5: atom arm bridge drift"
python3 scripts/gen_acc_arms.py --check || fail "stage a5: stack arm bridge drift"
python3 scripts/gen_const_arms.py --check || fail "stage a5: constant arm bridge drift"
python3 scripts/gen_arm_pilot.py --check || fail "stage a5: arm pilot drift"
python3 scripts/gen_ccall_returns.py --check || fail "stage a5: represented C_CALL return drift"
python3 scripts/gen_ccall_setups.py --check || fail "stage a5: represented C_CALL setup drift"
python3 scripts/gen_dispatch_table.py --check || fail "stage a5: dispatch table drift"
python3 scripts/gen_primitive_binding_probe.py --check || fail "stage a5: primitive binding probe drift"
python3 scripts/gen_primitive_entries.py --check || fail "stage a5: primitive entry lookup drift"
python3 scripts/gen_alu_pilot.py --check || fail "stage a5: ALU pilot drift"
python3 scripts/test_alu_classes.py || fail "stage a5: ALU classifier checks"
python3 scripts/gen_bc_rules.py --check || fail "stage a5: generated bytecode rules differ"
python3 scripts/gen_bc_demo.py --check || fail "stage a5: generated bytecode demo differs"
python3 scripts/check_bc_audit.py || fail "stage a5: generated bytecode axiom audit"
python3 scripts/gen_executed_ledger.py --check || fail "stage a5: executed compiler ledger drift"
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
run_lean lake build TCB tcbcheck 2>&1 | tail -1 | grep -q "Build completed successfully" || fail "stage t1: build TCB"
out=$(run_lean lake env lean tcb/Audit.lean 2>&1) || { echo "$out"; fail "stage t1: Lean audit failed"; }
out=$(echo "$out" | normalize_axioms)
echo "$out"
bad=$(echo "$out" | grep "depends on axioms" | grep -vE "axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]$" || true)
[ -z "$bad" ] || fail "stage t1: non-standard axioms: $bad"
run_lean tcb/validation/quick.sh || fail "stage t1: OS-spec validation (quick): a Linux trace was rejected"
echo "stage t1: OK"
echo "== stage a8: abstraction-discovery gate"
python3 scripts/check_abstraction_gate.py || fail "stage a8: run /abstraction-discovery"
echo "stage a8: OK"
echo "ALL STAGES OK"
