#!/usr/bin/env python3
"""Census of the bare-metal ocamlrun ELF (Phase 1, experiment 3).

    python3 scripts/census.py [--elf c/ocamlrun-riscv-htif.elf]
        [--while-elf ~/Documents/code/syi/c/while-riscv-htif.elf]
        [--json results/census.json]

Reports, over `objdump -d`:
  * functions / instructions in the image, and in the part reachable from
    `main` (direct jal/j/branch edges, closed under address-taken
    functions: C primitive table, custom-operation tables, callbacks);
  * the interpreter-reachable part (roots: caml_interprete and every
    function in caml_builtin_cprim);
  * caml_interprete: size, the switch jump table (opcode -> arm address)
    and per-opcode arm sizes (instructions from the arm's entry to the next
    arm entry in address order, so a shared tail is charged to the arm
    placed before it);
  * instruction classes under ship-your-interpreter's site classifier
    (scripts/disasm_to_sites.py `classify`): how many instructions fall in
    a class the generator layer already has a WP template for, and the
    unsupported ones grouped by reason;
  * functions shared byte-for-byte (modulo PC-relative cross-function
    immediates) with the WHILE proof ELF: the newlib / dlmalloc / libgcc
    code whose proofs transfer as they are.
"""
import argparse
import collections
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts" / "syi"))
from disasm_to_sites import classify  # noqa: E402  (reused from syi)

TOOLS = os.path.expanduser(
    "~/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-")
FUNC_RE = re.compile(r"^([0-9a-f]{16}) <(.+)>:$")
INST_RE = re.compile(r"^\s+([0-9a-f]+):\t([0-9a-f]{8})\s+\t(\S+)(?:\s+(.*))?$")
TARGET_RE = re.compile(r"([0-9a-f]+) <([^>+]+)(?:\+0x[0-9a-f]+)?>")
BRANCHES = {"jal", "j", "beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz",
            "bnez", "blez", "bgez", "bltz", "bgtz", "ble", "bgt", "bleu",
            "bgtu", "tail", "call"}


def disasm(elf):
    out = subprocess.run([TOOLS + "objdump", "-d", str(elf)],
                         capture_output=True, text=True, check=True).stdout
    funcs, cur = {}, None
    for line in out.splitlines():
        m = FUNC_RE.match(line)
        if m:
            cur = m.group(2)
            funcs[cur] = {"start": int(m.group(1), 16), "insts": []}
            continue
        m = INST_RE.match(line)
        if m and cur is not None:
            funcs[cur]["insts"].append((int(m.group(1), 16), int(m.group(2), 16),
                                        m.group(3), m.group(4) or ""))
    return funcs


def sections(elf):
    """name -> (vaddr, bytes) for the allocated data sections."""
    out = subprocess.run([TOOLS + "objdump", "-h", str(elf)],
                         capture_output=True, text=True, check=True).stdout
    data = Path(elf).read_bytes()
    secs = {}
    for line in out.splitlines():
        p = line.split()
        if len(p) >= 7 and p[0].isdigit():
            name, size, vma, off = p[1], int(p[2], 16), int(p[3], 16), int(p[5], 16)
            if name in (".rodata", ".data", ".sdata", ".srodata"):
                secs[name] = (vma, data[off:off + size])
    return secs


def symbols(elf):
    out = subprocess.run([TOOLS + "nm", "-S", str(elf)], capture_output=True,
                         text=True, check=True).stdout
    syms = {}
    for line in out.splitlines():
        p = line.split()
        if len(p) == 4:
            syms[p[3]] = (int(p[0], 16), int(p[1], 16))
        elif len(p) == 3:
            syms[p[2]] = (int(p[0], 16), 0)
    return syms


def read_mem(secs, addr, n):
    for vma, b in secs.values():
        if vma <= addr and addr + n <= vma + len(b):
            return b[addr - vma: addr - vma + n]
    return None


def edges_of(funcs):
    starts = {f["start"]: n for n, f in funcs.items()}
    edges = collections.defaultdict(set)
    addr_taken = set()
    indirect = collections.Counter()
    for name, f in funcs.items():
        for addr, word, mn, ops in f["insts"]:
            tm = TARGET_RE.search(ops)
            if mn in BRANCHES and tm:
                t = starts.get(int(tm.group(1), 16))
                if t and t != name:
                    edges[name].add(t)
            elif mn == "addi" and tm:            # auipc+addi of a function
                t = starts.get(int(tm.group(1), 16))
                if t:
                    edges[name].add(t)
                    addr_taken.add(t)
            elif mn in ("jalr",) or (mn == "jr" and ops.strip() != "ra"):
                indirect[name] += 1
    return starts, edges, addr_taken, indirect


def data_fn_ptrs(secs, starts):
    """Function addresses stored as 8-byte words in data sections."""
    out = set()
    for vma, b in secs.values():
        for i in range(0, len(b) - 7, 8):
            v = int.from_bytes(b[i:i + 8], "little")
            if v in starts:
                out.add(starts[v])
    return out


def closure(roots, edges):
    seen, todo = set(), list(roots)
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        seen.add(n)
        todo.extend(edges.get(n, ()))
    return seen


def opcode_names(instruct_h):
    txt = Path(instruct_h).read_text()
    body = txt[txt.index("enum instructions {") + len("enum instructions {"):]
    body = body[:body.index("}")]
    body = re.sub(r"/\*.*?\*/", "", body, flags=re.S)
    names = [t.strip() for t in body.replace("\n", " ").split(",") if t.strip()]
    return [n for n in names if n != "FIRST_UNIMPLEMENTED_OP"]


def interp_arms(funcs, secs, opnames):
    f = funcs["caml_interprete"]
    insts = f["insts"]
    # dispatch: `lw rX,0(rX); add rX,rX,base; jr rX` with base = &table
    table = None
    for i, (addr, word, mn, ops) in enumerate(insts):
        if mn == "jr" and i >= 3 and insts[i - 2][2] == "lw" \
                and insts[i - 1][2] == "add":
            base_reg = insts[i - 1][3].split(",")[2].strip()
            for a2, w2, m2, o2 in insts[:i]:
                if m2 == "addi" and o2.startswith(base_reg + ","):
                    tm = re.search(r"# ([0-9a-f]+)", o2)
                    if tm:
                        table = int(tm.group(1), 16)
            dispatch = addr
            break
    if table is None:
        return None
    n = len(opnames)
    raw = read_mem(secs, table, 4 * n)
    targets = []
    for k in range(n):
        off = int.from_bytes(raw[4 * k:4 * k + 4], "little", signed=True)
        targets.append((table + off) % (1 << 64))
    # Per-arm CFG walk inside caml_interprete: from the arm entry follow
    # fall-through and intra-function branch/jump targets, stopping at the
    # dispatch loop head (the opcode fetch before the table jump), at other
    # arms' entries (fall-through into a sibling arm, e.g. PUSHACCn -> ACCn)
    # and at returns / indirect jumps. `insts` = instructions reachable
    # from the arm, `own` = those reachable from no other arm.
    at = {a: (w, m, o) for a, w, m, o in insts}
    addrs = sorted(at)
    nxt = {addrs[i]: addrs[i + 1] for i in range(len(addrs) - 1)}
    head = None                      # loop head: the lw of the opcode
    for i in range(len(addrs)):
        if addrs[i] == dispatch:
            head = addrs[i - 8] if i >= 8 else None
            for j in range(i, max(i - 12, 0), -1):
                w, m, o = at[addrs[j]]
                if m == "lw" and o.endswith("(s0)") and o.split(",")[1].startswith("0("):
                    head = addrs[j]
                    break
            break
    entries = set(targets)

    def walk(t):
        seen, todo = set(), [t]
        while todo:
            x = todo.pop()
            if x in seen or x not in at or x == head or (x != t and x in entries):
                continue
            seen.add(x)
            w, m, o = at[x]
            tm = TARGET_RE.search(o)
            tgt = int(tm.group(1), 16) if tm else None
            if m in ("j", "jal") and tgt in at and m == "j":
                todo.append(tgt)
                continue
            if m in ("jr", "ret") or (m == "jalr" and o.startswith("zero")):
                continue
            if m in BRANCHES and m not in ("j", "jal", "call", "tail") and tgt in at:
                todo.append(tgt)
            if x in nxt:
                todo.append(nxt[x])
        return seen

    reach = {t: walk(t) for t in set(targets)}
    owners = collections.Counter(a for s in reach.values() for a in s)
    arms = {}
    for k in range(n):
        s = reach[targets[k]]
        arms[opnames[k]] = {"addr": hex(targets[k]), "insts": len(s),
                            "own": sum(1 for a in s if owners[a] == 1)}
    uniq = set(targets)
    shared = sum(1 for a, c in owners.items() if c > 1)
    return {"dispatch_jr": hex(dispatch), "table": hex(table),
            "n_opcodes": n, "distinct_arm_entries": len(uniq),
            "loop_head": hex(head) if head else None,
            "insts_in_some_arm": len(owners), "insts_shared_by_arms": shared,
            "insts_total": len(insts), "arms": arms}


def norm_words(f):
    """Instruction words with PC-relative cross-function immediates masked:
    `jal`'s J-immediate, `auipc`'s U-immediate, and the 12-bit low half of
    every auipc pair (the I/S-type immediate of an instruction whose rs1 was
    last written by an auipc), so identical functions at different
    addresses compare equal."""
    out, hi = [], set()
    for addr, word, mn, ops in f["insts"]:
        op, rd, rs1 = word & 0x7f, (word >> 7) & 0x1f, (word >> 15) & 0x1f
        w = word
        if op in (0x17, 0x6f):                       # AUIPC, JAL
            w &= 0xfff
        elif rs1 in hi and op in (0x13, 0x03, 0x67):  # addi/load/jalr low half
            w &= 0x000fffff
        elif rs1 in hi and op == 0x23:                # store low half
            w &= 0x01fff07f
        out.append(w)
        if op == 0x17:
            hi.add(rd)
        elif op not in (0x23, 0x63) and rd in hi and not (rs1 == rd and op in (0x13, 0x03)):
            hi.discard(rd)
        elif rd in hi and rs1 == rd and op in (0x13, 0x03):
            hi.discard(rd)
    return out


def shared_with(funcs, other):
    shared, same_name = [], 0
    for n, f in funcs.items():
        if n in other:
            same_name += 1
            if norm_words(f) == norm_words(other[n]):
                shared.append(n)
    return same_name, shared


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--elf", default=str(ROOT / "c/ocamlrun-riscv-htif.elf"))
    ap.add_argument("--while-elf", default=os.path.expanduser(
        "~/Documents/code/syi/c/while-riscv-htif.elf"))
    ap.add_argument("--instruct-h", default=str(
        ROOT / "vendor/ocaml-4.14.2/runtime/caml/instruct.h"))
    ap.add_argument("--json", default=str(ROOT / "results/census.json"))
    a = ap.parse_args()

    funcs = disasm(a.elf)
    secs = sections(a.elf)
    starts, edges, addr_taken, indirect = edges_of(funcs)
    data_ptrs = data_fn_ptrs(secs, starts)
    taken = addr_taken | data_ptrs
    for n in taken:                       # address-taken: reachable roots
        edges["<indirect>"].add(n)
    reach_main = closure(["_start", "<indirect>"], edges) - {"<indirect>"}

    # interpreter-reachable: caml_interprete + all C primitives
    syms = symbols(a.elf)
    prim_tab = syms.get("caml_builtin_cprim")
    prims = set()
    if prim_tab:
        k = 0
        while True:
            w = read_mem(secs, prim_tab[0] + 8 * k, 8)
            if w is None:
                break
            v = int.from_bytes(w, "little")
            if v == 0:
                break
            if v in starts:
                prims.add(starts[v])
            k += 1
    reach_interp = closure(["caml_interprete"] + sorted(prims), edges)

    def count(names):
        return sum(len(funcs[n]["insts"]) for n in names if n in funcs)

    cls = collections.Counter()
    unsup = collections.Counter()
    unsup_mn = collections.Counter()
    mnem = collections.Counter()
    for n in reach_main:
        for addr, word, mn, ops in funcs[n]["insts"]:
            mnem[mn] += 1
            rows = classify(addr, word, f"{mn} {ops}", {addr: "taken"})
            r = rows[-1]
            if r.cls is None:
                why = r.comment.split("[")[-1].rstrip("]")
                unsup[why] += 1
                unsup_mn[mn] += 1
            else:
                cls[r.cls] += 1

    arms = interp_arms(funcs, secs, opcode_names(a.instruct_h))

    res = {
        "elf": a.elf,
        "image": {"functions": len(funcs), "insts": count(funcs)},
        "reachable_from_main": {"functions": len(reach_main),
                                "insts": count(reach_main)},
        "interp_reachable": {"functions": len(reach_interp),
                             "insts": count(reach_interp),
                             "c_primitives": len(prims)},
        "address_taken_functions": len(taken),
        "indirect_jump_sites": sum(indirect.values()),
        "mnemonics": dict(mnem.most_common()),
        "site_classes": dict(cls.most_common()),
        "site_supported_insts": sum(cls.values()),
        "unsupported_by_reason": dict(unsup.most_common()),
        "unsupported_by_mnemonic": dict(unsup_mn.most_common()),
        "caml_interprete": arms,
    }
    if os.path.exists(a.while_elf):
        other = disasm(a.while_elf)
        same_name, shared = shared_with(funcs, other)
        res["shared_with_while_elf"] = {
            "while_elf": a.while_elf,
            "while_functions": len(other),
            "same_name": same_name,
            "identical": len(shared),
            "identical_insts": count(shared),
            "identical_reachable": len(set(shared) & reach_main),
            "identical_reachable_insts": count(set(shared) & reach_main),
            "names": sorted(shared),
        }
    Path(a.json).parent.mkdir(parents=True, exist_ok=True)
    Path(a.json).write_text(json.dumps(res, indent=1))

    print(f"image: {res['image']}")
    print(f"reachable from main: {res['reachable_from_main']}")
    print(f"interpreter-reachable: {res['interp_reachable']}")
    print(f"address-taken functions: {len(taken)}; "
          f"indirect jump sites: {res['indirect_jump_sites']}")
    tot = sum(mnem.values())
    print(f"site-classifier: {res['site_supported_insts']}/{tot} "
          f"({100*res['site_supported_insts']/tot:.1f}%) in an existing class")
    print("  unsupported by mnemonic:",
          ", ".join(f"{m} {c}" for m, c in unsup_mn.most_common(15)))
    if arms:
        big = sorted(arms["arms"].items(), key=lambda kv: -kv[1]["insts"])
        print(f"caml_interprete: {arms['insts_total']} insts, "
              f"{arms['n_opcodes']} opcodes, {arms['distinct_arm_entries']} "
              f"distinct arm entries")
        print("  largest arms:", ", ".join(f"{k} {v['insts']}" for k, v in big[:12]))
        sizes = sorted(v["insts"] for v in arms["arms"].values())
        print(f"  median arm {sizes[len(sizes)//2]} insts; {arms['insts_in_some_arm']} "
              f"insts reachable from some arm, {arms['insts_shared_by_arms']} shared "
              f"by several (GC/raise/signal/callback paths)")
    if "shared_with_while_elf" in res:
        s = res["shared_with_while_elf"]
        print(f"shared with WHILE ELF: {s['identical']} identical functions "
              f"({s['identical_insts']} insts) of {s['same_name']} same-named; "
              f"{s['identical_reachable']} reachable "
              f"({s['identical_reachable_insts']} insts)")


if __name__ == "__main__":
    main()
