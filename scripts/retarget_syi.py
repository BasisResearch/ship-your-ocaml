#!/usr/bin/env python3
"""Retarget ship-your-interpreter's proofs of shared library code to this ELF.

    python3 scripts/retarget_syi.py [--apply] [--report results/retarget.json]

The copied `Vsa/` proofs about newlib/libgcc functions (memcpy, strlen,
__muldi3, …) are stated at the WHILE ELF's addresses. For every function
whose instruction words are BYTE-IDENTICAL in the two ELFs (same code, only
moved), every address inside it maps to the same offset in this ELF's copy.
This tool rewrites those addresses — hex literals (`0x80006bc8`), hex
embedded in identifiers (`memcpy_at_80006c1c`) — in the `.lean` files that
mention them, and nothing else:

* addresses outside every ported function (the RAM base `0x80000000`, RAM
  and HTIF bounds, …) are left alone;
* a file that also mentions an address inside a NON-ported function (code
  that differs between the ELFs: the WHILE interpreter, `_malloc_r`,
  `_svfprintf_r`, …) is not touched at all and is reported: its facts stay
  about the WHILE ELF;
* instruction bytes are not rewritten: for byte-identical functions they are
  the same, which the tool re-checks against both ELFs.

Function ranges come from `nm -S` of both ELFs. Any function's START maps
by name (a call target or a region bound, even when the function's code
changed); an address inside a byte-identical function maps by offset; one
past its end maps to one past its new end.
"""
import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOOLS = os.path.expanduser(
    "~/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-")
OLD_ELF = os.path.expanduser("~/Documents/code/syi/c/while-riscv-htif.elf")
NEW_ELF = str(ROOT / "c/ocamlrun-riscv-htif.elf")

HEX_LIT = re.compile(r"0x(8[0-9a-fA-F]{7})\b")
HEX_ID = re.compile(r"(?<=_)(8[0-9a-f]{7})\b")


def funcs(elf, kinds="Tt"):
    out = subprocess.run([TOOLS + "nm", "-S", elf], capture_output=True, text=True,
                         check=True).stdout
    fs = {}
    for line in out.splitlines():
        p = line.split()
        if len(p) == 4 and p[2] in kinds:
            fs[p[3]] = (int(p[0], 16), int(p[1], 16))
    return fs


def symbol(elf, name):
    out = subprocess.run([TOOLS + "nm", elf], capture_output=True, text=True,
                         check=True).stdout
    for line in out.splitlines():
        p = line.split()
        if len(p) == 3 and p[2] == name:
            return int(p[0], 16)
    raise SystemExit(f"retarget_syi.py: no symbol {name} in {elf}")


def words(elf, start, size):
    out = subprocess.run([TOOLS + "objdump", "-d", elf, f"--start-address={start:#x}",
                          f"--stop-address={start + size:#x}"],
                         capture_output=True, text=True, check=True).stdout
    return re.findall(r"^\s*[0-9a-f]+:\s+([0-9a-f]{8})\s", out, flags=re.M)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--reset", action="store_true",
                    help="first restore the files a previous run rewrote (listed in the "
                         "report) from ship-your-interpreter's originals, so the tool can "
                         "be re-run after the ELF changes")
    ap.add_argument("--report", default=str(ROOT / "results/retarget.json"))
    a = ap.parse_args()

    if a.reset:
        prev = json.loads(Path(a.report).read_text())
        syi = Path(OLD_ELF).parent.parent
        paths = set(prev["rewritten"]) | set(prev.get("mailbox_files", []))
        for rel in sorted(paths):
            Path(ROOT / rel).write_text((syi / rel).read_text())
        print(f"reset {len(paths)} files from {syi}")

    old, new = funcs(OLD_ELF), funcs(NEW_ELF)
    ported, differs = {}, {}
    for name, (s, z) in old.items():
        if name in new and new[name][1] == z and z > 0 and \
                words(OLD_ELF, s, z) == words(NEW_ELF, new[name][0], z):
            ported[name] = (s, z, new[name][0])
        elif z > 0:
            differs[name] = (s, z)

    def owner(addr, table):
        """The function of `table` containing addr (half-open range)."""
        for name, v in table.items():
            if v[0] <= addr < v[0] + v[1]:
                return name
        return None

    old_starts = {v[0]: k for k, v in old.items() if k in new}
    # data objects (e.g. strcmp's `mask`) map by name too
    old_data, new_data = funcs(OLD_ELF, "DdRrBb"), funcs(NEW_ELF, "DdRrBb")
    old_data_starts = {v[0]: k for k, v in old_data.items() if k in new_data}

    def remap(addr):
        # 1. any function's start maps by name (even if its code changed)
        if addr in old_starts:
            return new[old_starts[addr]][0]
        if addr in old_data_starts:
            return new_data[old_data_starts[addr]][0]
        # 2. an address inside a byte-identical function maps by offset
        f = owner(addr, ported)
        if f is not None:
            s0, z, ns = ported[f]
            return ns + (addr - s0)
        # 3. one past the end of a byte-identical function (half-open code
        #    regions), when no function starts there
        for f, (s0, z, ns) in ported.items():
            if addr == s0 + z:
                return ns + z
        return None

    def interior_of_changed(addr):
        f = owner(addr, differs)
        return f if f is not None and addr not in old_starts else None

    files = sorted(set(str(p) for d in ("Vsa", "VsaIris") for p in (ROOT / d).rglob("*.lean")))
    srcs = {f: Path(f).read_text() for f in files}

    def mentioned(src):
        return {int(x, 16) for x in HEX_LIT.findall(src)} | \
               {int(x, 16) for x in HEX_ID.findall(src)}

    # Fixpoint: a file mentioning an address INSIDE changed code keeps its
    # WHILE-ELF facts; then every function it mentions inside must stay too
    # (otherwise it would name lemmas the port renamed). Demote those
    # functions from `ported` and repeat.
    demoted = {}
    while True:
        skipped = {f for f, src in srcs.items()
                   if any(interior_of_changed(x) for x in mentioned(src))}
        bad = {}
        for f in skipped:
            for x in mentioned(srcs[f]):
                g = owner(x, ported)
                if g is not None and x != ported[g][0]:
                    bad.setdefault(g, set()).add(str(Path(f).relative_to(ROOT)))
        if not bad:
            break
        for g, fs in bad.items():
            s0, z, ns = ported.pop(g)
            differs[g] = (s0, z)
            demoted[g] = sorted(fs)

    report = {"ported_functions": {k: {"old": hex(v[0]), "new": hex(v[2]), "size": v[1]}
                                   for k, v in sorted(ported.items())},
              "demoted": demoted, "rewritten": {}, "skipped_mixed": {}}
    for f in files:
        src = srcs[f]
        addrs = mentioned(src)
        hit_ported = {x for x in addrs if remap(x) is not None and
                      (owner(x, ported) is not None or x in old_data_starts or
                       any(x == v[0] + v[1] for v in ported.values()))}
        if not hit_ported:
            continue
        hit_other = {x for x in addrs if interior_of_changed(x)}
        rel = str(Path(f).relative_to(ROOT))
        if hit_other:
            report["skipped_mixed"][rel] = sorted({interior_of_changed(x) for x in hit_other})
            continue
        n = 0

        def sub_lit(m):
            nonlocal n
            v = remap(int(m.group(1), 16))
            if v is None:
                return m.group(0)
            n += 1
            return f"0x{v:08x}"

        def sub_id(m):
            nonlocal n
            v = remap(int(m.group(1), 16))
            if v is None:
                return m.group(0)
            n += 1
            return f"{v:08x}"

        out = HEX_ID.sub(sub_id, HEX_LIT.sub(sub_lit, src))
        report["rewritten"][rel] = {"replacements": n,
                                    "functions": sorted({owner(x, ported) or owner(x, differs) or "?"
                                                         for x in hit_ported})}
        if a.apply and out != src:
            Path(f).write_text(out)

    # The HTIF mailbox: the copied layer's one ELF-layout constant
    # (`Vsa.Sim.tohostAddr`: code lies below it, data above it — true of
    # both ELFs, which share the linker script). Rewritten everywhere, in
    # hex and in the decimal forms the proofs use (tohost, tohost + 8).
    ot, nt = symbol(OLD_ELF, "tohost"), symbol(NEW_ELF, "tohost")
    mailbox = {f"0x{ot:08x}": f"0x{nt:08x}", str(ot): str(nt), str(ot + 8): str(nt + 8)}
    report["mailbox"] = mailbox
    pat = re.compile(r"\b(" + "|".join(re.escape(k) for k in mailbox) + r")\b")
    for f in files:
        rel = str(Path(f).relative_to(ROOT))
        src = Path(f).read_text() if not a.apply else Path(f).read_text()
        if not pat.search(src):
            continue
        out = pat.sub(lambda m: mailbox[m.group(1)], src)
        report.setdefault("mailbox_files", []).append(rel)
        if a.apply:
            Path(f).write_text(out)

    Path(a.report).write_text(json.dumps(report, indent=1))
    print(f"ported functions (byte-identical): {len(ported)}; demoted for consistency: "
          f"{', '.join(sorted(demoted)) or 'none'}")
    print(f"files rewritten: {len(report['rewritten'])} "
          f"({sum(v['replacements'] for v in report['rewritten'].values())} addresses)"
          + ("" if a.apply else "  [dry run: pass --apply]"))
    print(f"mailbox {report['mailbox']} rewritten in {len(report.get('mailbox_files', []))} files")
    print(f"files skipped (mention non-identical code): {len(report['skipped_mixed'])}")
    for k, v in sorted(report["skipped_mixed"].items()):
        print(f"  {k}: {', '.join(v)}")


if __name__ == "__main__":
    main()
