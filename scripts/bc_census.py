#!/usr/bin/env python3
"""Bytecode-side census of a bytecode executable (Phase 1, experiment 3).

    python3 scripts/bc_census.py [EXE] [--dumpobj CMD] [--json OUT]
        [--modules Translcore,Matching,Bytegen,Emitcode]

Runs the 4.14.2 `dumpobj` on EXE (default vendor/.../boot/ocamlc) and
reports: code size in words, instruction count, the opcode histogram, the
C primitives called (C_CALLn names), and per-compilation-unit sizes.

Compilation units are delimited by their `SETGLOBAL <Unit>`: the linker
lays units out in link order and each unit's initialisation code ends by
storing its module block, so the code between two SETGLOBALs belongs to the
second unit (its functions and its toplevel code).
"""
import argparse
import collections
import json
import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DUMPOBJ = os.path.expanduser("~/toolchains/build/ocaml-4.14.2/tools/dumpobj")
INST_RE = re.compile(r"^\s*(\d+)\s+([A-Z_0-9]+)(?:\s+(.*))?$")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("exe", nargs="?",
                    default=str(ROOT / "vendor/ocaml-4.14.2/boot/ocamlc"))
    ap.add_argument("--dumpobj", default=DUMPOBJ)
    ap.add_argument("--modules", default="Translcore,Matching,Bytegen,Emitcode")
    ap.add_argument("--json", default=str(ROOT / "results/bc_census.json"))
    a = ap.parse_args()

    out = subprocess.run([a.dumpobj, a.exe], capture_output=True, text=True,
                         check=True).stdout
    insts = []                    # (pc, opcode, operand text)
    for line in out.splitlines():
        m = INST_RE.match(line)
        if m:
            insts.append((int(m.group(1)), m.group(2), m.group(3) or ""))
    code_words = insts[-1][0] + 1 if insts else 0
    ops = collections.Counter(op for _, op, _ in insts)
    prims = collections.Counter()
    for _, op, arg in insts:
        if op.startswith("C_CALL"):
            prims[arg.split()[-1] if arg else "?"] += 1

    units = []                    # (name, first_pc, n_insts, words)
    start_i, start_pc = 0, 0
    for i, (pc, op, arg) in enumerate(insts):
        if op == "SETGLOBAL":
            name = arg.split()[0]
            end_pc = insts[i + 1][0] if i + 1 < len(insts) else code_words
            units.append({"unit": name, "pc": start_pc, "insts": i + 1 - start_i,
                          "words": end_pc - start_pc})
            start_i, start_pc = i + 1, end_pc
    wanted = [m.strip() for m in a.modules.split(",") if m.strip()]
    by_name = {u["unit"]: u for u in units}
    sel = {m: by_name.get(m) for m in wanted}
    sel_ops = {}
    for m, u in sel.items():
        if u:
            c = collections.Counter(op for pc, op, _ in insts
                                    if u["pc"] <= pc < u["pc"] + u["words"])
            sel_ops[m] = len(c)
    res = {
        "exe": a.exe, "code_words": code_words, "insts": len(insts),
        "distinct_opcodes": len(ops), "opcodes": dict(ops.most_common()),
        "distinct_c_primitives": len(prims), "c_primitives": dict(prims.most_common()),
        "units": len(units), "unit_sizes": units,
        "selected": sel, "selected_distinct_opcodes": sel_ops,
        "selected_insts": sum(u["insts"] for u in sel.values() if u),
    }
    Path(a.json).parent.mkdir(parents=True, exist_ok=True)
    Path(a.json).write_text(json.dumps(res, indent=1))
    print(f"{a.exe}: {code_words} code words, {len(insts)} instructions, "
          f"{len(ops)} distinct opcodes, {len(prims)} distinct C primitives, "
          f"{len(units)} compilation units")
    for m, u in sel.items():
        print(f"  {m}: " + (f"{u['insts']} insts, {u['words']} words, "
                            f"{sel_ops[m]} distinct opcodes" if u else "absent"))
    print(f"  selected total: {res['selected_insts']} insts")
    big = sorted(units, key=lambda u: -u["insts"])[:10]
    print("  largest units:", ", ".join(f"{u['unit']} {u['insts']}" for u in big))
    print("  top opcodes:", ", ".join(f"{o} {c}" for o, c in ops.most_common(12)))


if __name__ == "__main__":
    main()
