#!/usr/bin/env python3
"""Run an ocamlrun ELF on the Sail Lean emulator and report milestones.

    tests/sail_run.py ELF [--max-steps N] [--emu PATH] [--json OUT]

Traces the entry PCs of a fixed set of runtime functions (plus the HTIF
exit store in _exit) with the emulator's `--trace-pcs` mode, and reports:
program output, exit code, total steps, and the step index of

  * each call to caml_interprete (the 1st is the table-init call
    caml_init_... makes with prog=NULL; the 2nd runs the loaded program:
    that is the Layer A cut point),
  * the first minor collection after the cut point, and the number of
    minor collections / major slices (a minor collection is counted by its
    one call to caml_oldify_mopup: caml_empty_minor_heap itself is inlined
    into its callers at -O2),
  * the first call to a few load-phase functions (caml_load_code,
    caml_build_primitive_table, caml_input_val).

`step` is the emulator's count of executed instructions (the trace row's
second field), so `steps` = the _exit store's step + 1.
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile

TOOLS = os.path.expanduser(
    "~/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-")
EMU = os.path.expanduser("~/vsa-b3-work/bin/lean_riscv_emulator")

WATCH = ["caml_main", "caml_init_gc", "caml_load_code",
         "caml_build_primitive_table", "caml_input_val", "caml_interprete",
         "caml_gc_dispatch", "caml_oldify_mopup",
         "caml_major_collection_slice",
         "caml_compact_heap", "caml_fatal_error", "caml_raise",
         "caml_do_exit", "_exit"]


def symbols(elf):
    out = subprocess.run([TOOLS + "nm", elf], capture_output=True, text=True,
                         check=True).stdout
    syms = {}
    for line in out.splitlines():
        p = line.split()
        if len(p) == 3 and p[1] in "Tt":
            syms[p[2]] = int(p[0], 16)
    return syms


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("elf")
    ap.add_argument("--max-steps", type=int, default=2_000_000_000)
    ap.add_argument("--emu", default=EMU)
    ap.add_argument("--json")
    a = ap.parse_args()

    syms = symbols(a.elf)
    pcs = {syms[n]: n for n in WATCH if n in syms}
    exit_store = syms["_exit"] + 16    # the `sd` to tohost (src/htif.c)
    pcs[exit_store] = "_exit.sd"
    with tempfile.NamedTemporaryFile("w", suffix=".pcs", delete=False) as f:
        for pc in pcs:
            f.write(f"0x{pc:x}\n")
        pcfile = f.name
    p = subprocess.Popen([a.emu, a.elf, "--trace-pcs", pcfile,
                          "--max-steps", str(a.max_steps)],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True)
    calls = {}
    order = []
    fuel_out = False
    for line in p.stderr:
        if line.startswith("TRACE-FUEL-OUT"):
            fuel_out = True
            continue
        if not line.startswith("T\t"):
            continue
        fs = line.split("\t", 4)
        step, pc = int(fs[1]), int(fs[2], 16)
        name = pcs.get(pc, hex(pc))
        calls.setdefault(name, []).append(step)
        order.append((step, name))
    out = p.stdout.read()
    rc = p.wait()
    os.unlink(pcfile)
    noise = ("TODO: cancel_reservation", "PC = 0x", "htif_tohost = 0x")
    output = "".join(l for l in out.splitlines(True)
                     if not l.startswith(noise))

    interp = calls.get("caml_interprete", [])
    cut = interp[1] if len(interp) > 1 else None
    minor = calls.get("caml_oldify_mopup", [])
    major = calls.get("caml_major_collection_slice", [])
    res = {
        "elf": a.elf, "exit": rc, "fuel_out": fuel_out,
        "steps": calls["_exit.sd"][0] + 1 if "_exit.sd" in calls else None,
        "output": output,
        "cut_point_step": cut,
        "first_minor_gc_step": minor[0] if minor else None,
        "first_minor_gc_after_cut": next((s for s in minor if cut and s > cut), None),
        "minor_gcs": len(minor), "major_slices": len(major),
        "minor_gcs_after_cut": sum(1 for x in minor if cut and x > cut),
        "first": {n: v[0] for n, v in calls.items()},
        "counts": {n: len(v) for n, v in calls.items()},
    }
    print(json.dumps(res, indent=1))
    if a.json:
        with open(a.json, "w") as f:
            json.dump(res, f, indent=1)


if __name__ == "__main__":
    main()
