#!/usr/bin/env python3
"""Observe the second caml_interprete entry; this is data, not a run proof.

Stream Sail's trace without retaining millions of register rows. Keep the
ordered stores (JSONL), entry row, and runtime fields for later reflection.
All addresses and field offsets are read from generated Layout.lean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/syi"))
from difftest_lib import Image


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--elf", required=True, type=Path)
    ap.add_argument("--work", required=True, type=Path)
    ap.add_argument("--layout", type=Path, default=ROOT / "OCaml/Vm/Layout.lean")
    ap.add_argument("--emulator", type=Path,
                    default=Path.home() / "vsa-b3-work/bin/lean_riscv_emulator")
    ap.add_argument("--max-steps", type=int, default=5_000_000)
    args = ap.parse_args()
    layout = dict((k, int(v, 0)) for k, v in re.findall(
        r"^def (\w+) : Nat := (\w+)$",
        args.layout.read_text(), re.M))
    # Reject an ELF whose symbol addresses differ from the generated layout.
    nm = Path.home() / "toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-nm"
    symbols = {p[2]: int(p[0], 16) for line in subprocess.check_output(
        [str(nm), str(args.elf)], text=True).splitlines()
        if len(p := line.split()) == 3}
    for name in ("caml_interprete", "Caml_state", "caml_something_to_do"):
        if symbols[name] != layout["sym_" + name]:
            raise SystemExit(f"ELF layout mismatch: {name}; regenerate layout first")
    image = Image(str(args.elf))
    memory = {}

    def read(addr, size=8):
        return sum(memory.get(addr + i, image.byte(addr + i)) << (8 * i)
                   for i in range(size))

    args.work.mkdir(parents=True, exist_ok=True)
    count = calls = 0
    entry = None
    with (args.work / "stdout.txt").open("w") as stdout, \
            (args.work / "stores.jsonl").open("w") as stores:
        proc = subprocess.Popen([str(args.emulator), str(args.elf), "--trace-all",
                                 "--max-steps", str(args.max_steps)],
                                stdout=stdout, stderr=subprocess.PIPE, text=True)
        try:
            for line in proc.stderr:
                if not line.startswith("T\t"):
                    continue
                row = line.rstrip().split("\t")
                if int(row[2], 16) == layout["sym_caml_interprete"]:
                    calls += 1
                    if calls == 2:
                        entry = row
                        break  # Entry is PRE-step: do not apply this row's store.
                if row[35].startswith("S"):
                    size, addr, value = int(row[35][1:]), int(row[36], 16), int(row[38], 16)
                    stores.write(json.dumps([int(row[1]), addr, size, value]) + "\n")
                    count += 1
                    for i in range(size):
                        memory[addr + i] = (value >> (8 * i)) & 255
        finally:
            if proc.poll() is None:
                proc.terminate()
            proc.wait()
            proc.stderr.close()
    if entry is None:
        raise SystemExit("second caml_interprete entry not reached")
    domain = read(layout["sym_Caml_state"])
    fields = {name.removeprefix("off_"): read(domain + off)
              for name, off in layout.items() if name.startswith("off_")}
    result = {
        "status": "observed candidate; no kernel-checked execution certificate",
        "elf_sha256": hashlib.sha256(image.raw).hexdigest(),
        "cut_step": int(entry[1]), "pc": int(entry[2], 16),
        "gprs": [0] + [int(x, 16) for x in entry[4:35]],
        "stores": count, "domain": domain, "fields": fields,
        "something_to_do": read(layout["sym_caml_something_to_do"], 4),
    }
    (args.work / "cut.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
