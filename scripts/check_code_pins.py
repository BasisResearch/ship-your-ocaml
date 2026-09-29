#!/usr/bin/env python3
"""Check the copied layer's code pins against this repository's ELF.

    python3 scripts/check_code_pins.py [--elf c/ocamlrun-riscv-htif.elf]

Every `mem[(0xADDR : Nat)]? = some (0xBB : BitVec 8)` fact in
`Vsa/Sim/Code/*.lean` (the code-region predicates the library proofs assume)
must be the byte the ELF loads at ADDR. After `scripts/retarget_syi.py` this
is what makes the retargeted proofs about THIS binary. Also reports which
functions the pinned regions cover. Exit 1 on any mismatch.
"""
import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOOLS = str(Path.home() / "toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-")
# Code pins of the WHILE interpreter's own functions (value_*): they are not
# in this ELF at all; copied site proofs import them, and they remain facts
# about the WHILE ELF. Reported, not checked.
WHILE_ONLY = {"Value_bool.lean", "Value_int.lean", "Value_null.lean", "Value_str.lean",
              "Value_truthy.lean"}
PIN = re.compile(r"mem\[\(0x([0-9a-fA-F]+) : Nat\)\]\? = some \(0x([0-9a-fA-F]{2}) : BitVec 8\)")


def load_image(elf):
    """vaddr -> byte for every PT_LOAD file-backed byte."""
    data = Path(elf).read_bytes()
    out = subprocess.run([TOOLS + "readelf", "-lW", elf], capture_output=True, text=True,
                         check=True).stdout
    img = {}
    for line in out.splitlines():
        p = line.split()
        if p and p[0] == "LOAD":
            off, vaddr, filesz = int(p[1], 16), int(p[2], 16), int(p[4], 16)
            for k in range(filesz):
                img[vaddr + k] = data[off + k]
    return img


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--elf", default=str(ROOT / "c/ocamlrun-riscv-htif.elf"))
    a = ap.parse_args()
    img = load_image(a.elf)
    bad, total = [], 0
    for f in sorted((ROOT / "Vsa/Sim/Code").glob("*.lean")):
        pins = PIN.findall(f.read_text())
        if not pins:
            continue
        if f.name in WHILE_ONLY:
            print(f"{f.name:28s} {len(pins):6d} pinned bytes  (WHILE interpreter code, not in this ELF)")
            continue
        mism = [(int(x, 16), int(b, 16)) for x, b in pins if img.get(int(x, 16)) != int(b, 16)]
        total += len(pins)
        status = "ok" if not mism else f"{len(mism)} MISMATCH"
        print(f"{f.name:28s} {len(pins):6d} pinned bytes  {status}")
        bad += [(f.name, x, b, img.get(x)) for x, b in mism]
    print(f"total {total} pinned bytes, {len(bad)} mismatches")
    for n, x, b, got in bad[:20]:
        print(f"  {n}: {x:#x} pinned {b:#04x}, ELF has {got if got is None else hex(got)}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
