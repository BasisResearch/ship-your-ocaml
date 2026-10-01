#!/usr/bin/env python3
"""Compare fixed runtime sections to a program-specific embedded image.

Default mode requires identical text/rodata/data/tohost. --write-pin records the comparison;
--check-pin verifies that recorded evidence, including a recorded mismatch.
Neither pin mode asserts that different binaries share machine-code proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TOOLS = Path.home() / "toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin"


def text_section(elf, section=".text"):
    headers = subprocess.check_output(
        [str(TOOLS / "riscv-none-elf-objdump"), "-h", str(elf)], text=True)
    row = next(line.split() for line in headers.splitlines()
               if len(line.split()) > 2 and line.split()[1] == section)
    with tempfile.TemporaryDirectory(prefix="boot-text-") as tmp:
        dst = Path(tmp) / "text.bin"
        subprocess.run([str(TOOLS / "riscv-none-elf-objcopy"), "--dump-section",
                        f"{section}={dst}", str(elf), str(Path(tmp) / "copy.elf")], check=True)
        data = dst.read_bytes()
    return int(row[3], 16), data


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--proof", type=Path, default=ROOT / "c/ocamlrun-riscv-htif.elf")
    ap.add_argument("--candidate", type=Path, required=True)
    group = ap.add_mutually_exclusive_group()
    group.add_argument("--write-pin", type=Path)
    group.add_argument("--check-pin", type=Path)
    args = ap.parse_args()
    base_a, a = text_section(args.proof)
    base_b, b = text_section(args.candidate)
    differences = [i for i in range(min(len(a), len(b))) if a[i] != b[i]]
    def pin(path, base, data):
        return {"elf_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                "text_base": base, "text_size": len(data),
                "text_sha256": hashlib.sha256(data).hexdigest()}
    record = {"proof": pin(args.proof, base_a, a),
              "candidate": pin(args.candidate, base_b, b),
              "identical": base_a == base_b and a == b,
              "different_bytes": len(differences) + abs(len(a) - len(b)),
              "different_rv64i_words": len({i // 4 for i in differences}),
              "first_differences": [
                  {"offset": i, "proof": a[i], "candidate": b[i]}
                  for i in differences[:32]]}
    record["fixed_data_sections"] = {}
    for name in (".rodata", ".data", ".tohost"):
        x, xs = text_section(args.proof, name)
        y, ys = text_section(args.candidate, name)
        record["fixed_data_sections"][name] = {
            "proof_base": x, "candidate_base": y,
            "proof_size": len(xs), "candidate_size": len(ys),
            "proof_sha256": hashlib.sha256(xs).hexdigest(),
            "candidate_sha256": hashlib.sha256(ys).hexdigest(),
            "identical": x == y and xs == ys}
    record["runtime_identical"] = record["identical"] and all(
        row["identical"] for row in record["fixed_data_sections"].values())
    rendered = json.dumps(record, indent=2) + "\n"
    if args.write_pin:
        args.write_pin.parent.mkdir(parents=True, exist_ok=True)
        args.write_pin.write_text(rendered)
    elif args.check_pin:
        if json.loads(args.check_pin.read_text()) != record:
            raise SystemExit("boot text comparison differs from pin")
    elif not record["runtime_identical"]:
        print(rendered, end="")
        raise SystemExit("fixed runtime sections differ: do not reuse image facts for this ELF")
    print(rendered, end="")


if __name__ == "__main__":
    main()
