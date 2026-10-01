#!/usr/bin/env python3
"""Generate OCaml/Vm/Layout.lean from the bare-metal ocamlrun ELF.

    python3 scripts/gen_layout.py [--elf c/ocamlrun-riscv-htif.elf] > OCaml/Vm/Layout.lean

Everything is read from the binary or the vendored headers, nothing typed:
  * symbol addresses (nm): caml_interprete, Caml_state, caml_global_data,
    caml_atom_table, caml_something_to_do, tohost, _exit;
  * Caml_state field offsets: 8 bytes per DOMAIN_STATE entry, in the order
    of runtime/caml/domain_state.tbl;
  * caml_interprete's dispatch loop: the loop head (the `lw` of the opcode
    word through the pc register), the jump-table base and the register
    allocation of the interpreter's C locals at the loop head, recovered
    from the disassembly by pattern (and checked: the script fails if a
    pattern is not found exactly once):
       pc     : the base register of the loop head's `lw a5,0(pc)`
       sp     : the base register of ACC0's `ld accu,0(sp)`
       accu   : ACC0's destination
       env    : ENVACC1's base register (`ld accu,8(env)`)
       extra  : the register APPLY1 tags with `slli r,r,1; addi r,r,1`
"""
import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from gen_primitive_census import primitive_names

ROOT = Path(__file__).resolve().parent.parent
TOOLS = os.path.expanduser(
    "~/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-")
ABI = {"zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4, "t0": 5, "t1": 6, "t2": 7,
       "s0": 8, "s1": 9, "a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15,
       "a6": 16, "a7": 17, "s2": 18, "s3": 19, "s4": 20, "s5": 21, "s6": 22,
       "s7": 23, "s8": 24, "s9": 25, "s10": 26, "s11": 27, "t3": 28, "t4": 29,
       "t5": 30, "t6": 31}


def die(msg):
    sys.exit(f"gen_layout.py: {msg}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--elf", default=str(ROOT / "c/ocamlrun-riscv-htif.elf"))
    ap.add_argument("--census", default=str(ROOT / "results/census.json"))
    a = ap.parse_args()

    nm = subprocess.run([TOOLS + "nm", a.elf], capture_output=True, text=True,
                        check=True).stdout
    sym = {}
    for line in nm.splitlines():
        p = line.split()
        if len(p) == 3:
            sym[p[2]] = int(p[0], 16)
    need = ["caml_interprete", "Caml_state", "caml_global_data", "caml_atom_table",
            "caml_something_to_do", "tohost", "_exit", "caml_main", "main",
            "caml_start_code", "caml_code_size", "caml_int64_ops", "caml_int32_ops",
            "caml_nativeint_ops", "channel_operations", "caml_all_opened_channels"]
    need += primitive_names()
    need += ["main_argv", "caml_exe_name", "oo_last_id"]
    for n in need:
        if n not in sym:
            die(f"symbol {n} not found")

    tbl = (ROOT / "vendor/ocaml-4.14.4/runtime/caml/domain_state.tbl").read_text()
    fields = re.findall(r"^DOMAIN_STATE\([^,]+,\s*(\w+)\)", tbl, flags=re.M)
    off = {f: 8 * i for i, f in enumerate(fields)}

    arms = json.load(open(a.census))["caml_interprete"]
    head = int(arms["loop_head"], 16)
    table = int(arms["table"], 16)
    dis = subprocess.run([TOOLS + "objdump", "-d", a.elf,
                          f"--start-address=0x{sym['caml_interprete']:x}",
                          f"--stop-address=0x{sym['caml_interprete'] + 0x2000:x}"],
                         capture_output=True, text=True, check=True).stdout
    ins = {}
    for line in dis.splitlines():
        m = re.match(r"^\s*([0-9a-f]+):\s+[0-9a-f]{8}\s+(\S+)\s*(.*)$", line)
        if m:
            ins[int(m.group(1), 16)] = (m.group(2), m.group(3).split("#")[0].strip())

    def arm(name, k=0):
        return ins[int(arms["arms"][name]["addr"], 16) + 4 * k]

    mn, ops = ins[head]
    m = re.fullmatch(r"(\w+),0\((\w+)\)", ops)
    if mn != "lw" or not m:
        die(f"loop head {head:#x} is not `lw r,0(pc)`: {mn} {ops}")
    pc_reg = m.group(2)
    mn, ops = arm("ACC0")
    m = re.fullmatch(r"(\w+),0\((\w+)\)", ops)
    if mn != "ld" or not m:
        die(f"ACC0 is not `ld accu,0(sp)`: {mn} {ops}")
    accu_reg, sp_reg = m.group(1), m.group(2)
    mn, ops = arm("ENVACC1")
    m = re.fullmatch(r"(\w+),8\((\w+)\)", ops)
    if mn != "ld" or not m or m.group(1) != accu_reg:
        die(f"ENVACC1 is not `ld accu,8(env)`: {mn} {ops}")
    env_reg = m.group(2)
    mn1, ops1 = arm("APPLY1", 1)
    mn2, ops2 = arm("APPLY1", 2)
    m = re.fullmatch(r"(\w+),(\w+),0x1", ops1)
    if mn1 != "slli" or not m or m.group(1) != m.group(2) or mn2 != "addi" \
            or ops2 != f"{m.group(1)},{m.group(1)},1":
        die(f"APPLY1 does not tag extra_args: {mn1} {ops1}; {mn2} {ops2}")
    extra_reg = m.group(1)

    # Fixed loop registers are established immediately before the loop head.
    bound_mn, bound_ops = ins[head - 28]
    bound_match = re.fullmatch(r"(\w+),(\d+)", bound_ops)
    if bound_mn != "li" or not bound_match:
        die("expected opcode-bound initialization before dispatch")
    bound_reg, bound_value = bound_match.group(1), int(bound_match.group(2))

    def fixed_pair(addr, expected):
        mn1, ops1 = ins[addr]
        mn2, ops2 = ins[addr + 4]
        hi = re.fullmatch(r"(\w+),0x([0-9a-f]+)", ops1)
        lo = re.fullmatch(r"(\w+),(\w+),(-?\d+)", ops2)
        if mn1 != "auipc" or mn2 != "addi" or not hi or not lo:
            die("expected fixed-register auipc/addi pair")
        if hi.group(1) != lo.group(1) or lo.group(1) != lo.group(2):
            die("mismatched fixed-register pair")
        value = addr + (int(hi.group(2), 16) << 12) + int(lo.group(3))
        if value != expected:
            die(f"fixed register value {value:#x} != {expected:#x}")
        return hi.group(1)

    table_reg = fixed_pair(head - 24, table)
    pending_reg = fixed_pair(head - 16, sym["caml_something_to_do"])
    domain_reg = fixed_pair(head - 8, sym["Caml_state"])

    w = sys.stdout.write
    w("/-!\n# Layout of the bare-metal `ocamlrun` (generated)\n\n"
      "Generated by `scripts/gen_layout.py` from `c/ocamlrun-riscv-htif.elf`\n"
      "(symbols, the disassembly of `caml_interprete`) and\n"
      "`runtime/caml/domain_state.tbl` (`Caml_state` field offsets). Do not edit.\n-/\n\n"
      "namespace OCaml.Vm.Layout\n\n")
    for n in need:
        w(f"/-- `{n}` -/\ndef sym_{n.lstrip('_')} : Nat := 0x{sym[n]:x}\n")
    w(f"\n/-- `caml_interprete`'s dispatch loop head (fetch of the opcode word). -/\n"
      f"def loopHead : Nat := 0x{head:x}\n")
    w(f"/-- The switch jump table (`int32` offsets from its own base). -/\n"
      f"def jumpTable : Nat := 0x{table:x}\n\n")
    w("/-! GPR indices holding `caml_interprete`'s locals at `loopHead`. -/\n")
    for k, r in [("pc", pc_reg), ("sp", sp_reg), ("accu", accu_reg), ("env", env_reg),
                 ("extra", extra_reg), ("dispatchTable", table_reg),
                 ("opcodeBound", bound_reg), ("pending", pending_reg), ("domain", domain_reg)]:
        w(f"/-- `{k}` lives in `{r}` -/\ndef reg_{k} : Nat := {ABI[r]}\n")
    w(f"\n/-- Largest opcode accepted by the dispatch bound check. -/\ndef opcodeBound : Nat := {bound_value}\n")
    w("\n/-! `Caml_state` field offsets (bytes). -/\n")
    for f in ["young_limit", "young_ptr", "young_start", "young_end", "young_alloc_start",
              "young_alloc_end", "stack_low", "stack_high", "stack_threshold", "extern_sp",
              "trapsp", "external_raise", "exn_bucket", "backtrace_active",
              "requested_major_slice", "requested_minor_gc", "local_roots"]:
        w(f"def off_{f} : Nat := {off[f]}\n")
    w("\nend OCaml.Vm.Layout\n")


if __name__ == "__main__":
    main()
