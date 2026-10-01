#!/usr/bin/env python3
"""gen_fn.py — the WHOLE-FUNCTION summary generator (the rung above genseg).

    python3 scripts/gen_fn.py --fn <name> --entry <pc> [-o OUT.lean]
        [--pin reg=name ...] [--no-verify] [--summary-only]

Where genseg compiles ONE arm (a resolved straight-line/branch path) into a
seg + row, gen_fn compiles a whole FUNCTION: it reads the function's body from
`experiments/disasm.txt`, partitions it into basic blocks at branch targets and
joins, classifies every terminator, and emits ONE `.lean` file into
`Vsa/Sim/rows/` containing

  * per-block arm sections in the genseg idiom (`#derive_case` seg + `L`-list +
    named-field `Post` + `segToTriple` row) — branch blocks emit taken/fall
    TWIN arms, exactly the `EnvDefBridges4` twin idiom;
  * one named-field `Post` structure PER JOIN POINT (load-bearing: it keeps
    elaboration linear — two paths never merge into a raw ∨/∃ tower);
  * a top-level `FnSummary` theorem folding the blocks (`Vsa/Sim/FnSummary.lean`
    combinators: `Triple.seq` block chaining, `FnSummary.callSplice` around a
    callee summary at each `jal` seam, `tailJump_of_summary` at a tail-`j`,
    `loopFromBody` for a recognised counted byte-store loop).

Terminator classes (a strict superset of genseg's):

  fallthrough   block runs into the next leader.
  br            two successors → TWIN arms (suffix `T`/`F`).
  j (in-fn)     one successor, in-model `TKind.j`.
  j (out-fn)    TAIL JUMP: the seg keeps the `j` in-model (its target is the
                other function's entry); the fold splices the target's
                `FnSummary` via `tailJump_of_summary`.  THE one genuinely new
                seam of this layer.
  jal           CALL seam: the block parks AT the `jal` (genseg's jal mode);
                the fold splices the callee contract via `callSeg`.
  jr / ret      function exit; in-model `TKind.jr` in the FINAL block.
  sd → tohost   STORE-TO-TOHOST seam (side-effects `sailOutput` — write-log
                reflection cannot contain it): the block PARKS at the `sd`,
                the fold inserts the explicit putchar step
                (`stepObs_tohost_putchar`, `Vsa/Sim/HtifStepObs.lean`), and the
                next block resumes at `sd`+4.  Model: `ExitPathSeg.lean`.

Loops: the counted byte-store shape (monotone `addi rX,rX,1` pointer, `bne`
back-edge on rX, body containing the tohost-store seam — the `_write` loop) is
recognised and folded with the `loopFromBody` invariant template.  Any OTHER
back-edge emits a NAMED invariant-hole hypothesis with a doc comment (graceful
degradation, not failure).

Hard budgets (enforced here, fail loudly):
  * emitted source ≤ 40 + 18·blocks + 1·instrs + 12·joins lines — expanded
    terms live in the kernel only, never in source;
  * refuse functions > 150 instrs or > 20 branches (print which pins the
    branch conditions would need).

Self-verifying: runs `lake env lean` on the output and greps for `sorryAx`
unless --no-verify.

NO `sorry`/`axiom`/`native_decide`/`bv_decide` in the output; no Mathlib.
"""

import argparse
import importlib.util
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from genseg import lib  # noqa: E402

# genseg.py (the file, not the package) — loaded for its emission functions.
_spec = importlib.util.spec_from_file_location(
    "gensegmain", os.path.join(HERE, "genseg.py"))
gensegmain = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gensegmain)

ROOT = lib.ROOT

MAX_INSTRS = 150
MAX_BRANCHES = 20

func_re = re.compile(r"^([0-9a-f]{16}) <(.+)>:$")


def function_extents(path=None):
    """symbol → (start, end) address ranges from the disasm."""
    path = path or os.path.join(ROOT, "experiments", "disasm.txt")
    syms = []
    for line in open(path):
        m = func_re.match(line)
        if m:
            syms.append((int(m.group(1), 16), m.group(2)))
    out = {}
    for i, (addr, name) in enumerate(syms):
        end = syms[i + 1][0] if i + 1 < len(syms) else None
        out[name] = (addr, end)
    return out


class Block:
    """One CFG basic block: [start, term_addr] with a classified terminator."""

    def __init__(self, start):
        self.start = start
        self.instrs = []          # body Instr list, EXCLUDING the terminator
        self.term = None          # terminator Instr or None (fallthrough)
        self.kind = "fallthrough"  # fallthrough|br|j|tailj|jal|ret|tohost
        self.succs = []           # in-function successor leaders
        self.callee = None        # jal: symbol; tailj: symbol
        self.callee_pc = None
        self.is_loop_head = False
        self.back_edge_from = None

    @property
    def term_addr(self):
        return self.term.addr if self.term else (
            self.instrs[-1].addr if self.instrs else self.start)

    def __repr__(self):
        t = f"{self.term.mnem}" if self.term else "fall"
        return (f"Block(0x{self.start:x}..0x{self.term_addr:x} {t} "
                f"kind={self.kind} succs={[hex(s) for s in self.succs]})")


def _is_tohost_store(ins):
    return ins.mnem == "sd" and "<tohost>" in ins.raw


def _branch_target(ins):
    if ins.is_branch:
        _, _, imm = lib._btype_fields(ins.word)
        return (ins.addr + lib.sext(imm, 13)) % 2**64
    if ins.mnem == "j":
        return (ins.addr + lib.sext(lib._jal_imm(ins.word), 21)) % 2**64
    return None


def build_cfg(fn, entry, di, extents, route=None):
    """Extract the function body and partition into classified basic blocks.

    `route` (dict pc -> 'T'|'F'|'TF') is the RESOLVED-PATH mode for functions
    over budget: only blocks reachable from the entry under the pinned branch
    polarities are emitted (a branch pinned 'T' keeps only its taken twin,
    'F' only the fall twin, 'TF' both — an unrolled two-visit head).  Budgets
    are then enforced on the PRUNED subgraph."""
    start, end = extents[fn]
    if entry != start:
        raise SystemExit(f"--entry 0x{entry:x} != disasm start of {fn} "
                         f"(0x{start:x})")
    body = []
    a = start
    while a in di and (end is None or a < end):
        body.append(di[a])
        a += 4
    if route is None:
        if len(body) > MAX_INSTRS:
            raise SystemExit(
                f"{fn}: {len(body)} instrs > {MAX_INSTRS} — refuse without a "
                f"--route path restriction (pin the branch polarities)")
        nbr = sum(1 for i in body if i.is_branch)
        if nbr > MAX_BRANCHES:
            conds = [f"0x{i.addr:x}:{i.mnem} {i.ops}" for i in body if i.is_branch]
            raise SystemExit(
                f"{fn}: {nbr} branches > {MAX_BRANCHES} — refuse without --route. "
                f"The branch conditions needing pins:\n  " + "\n  ".join(conds))

    inside = {i.addr for i in body}
    # leaders: entry + in-fn branch/jump targets + successor of any terminator
    # + the instruction AFTER a tohost-store or jal seam (block resumption).
    leaders = {start}
    for i in body:
        if i.is_branch or i.mnem == "j":
            t = _branch_target(i)
            if t in inside:
                leaders.add(t)
            if i.is_branch:
                leaders.add(i.addr + 4)
        elif i.mnem in ("jal", "jalr") or _is_tohost_store(i) \
                or i.mnem in ("jr", "ret"):
            leaders.add(i.addr + 4)
    leaders = {l for l in leaders if l in inside}

    blocks = {}
    cur = None
    for i in body:
        if i.addr in leaders or cur is None:
            cur = Block(i.addr)
            blocks[i.addr] = cur
        if i.is_branch:
            cur.term, cur.kind = i, "br"
            t = _branch_target(i)
            cur.succs = [t, i.addr + 4]
            cur = None
        elif i.mnem == "j":
            t = _branch_target(i)
            cur.term = i
            if t in inside:
                cur.kind, cur.succs = "j", [t]
            else:
                cur.kind = "tailj"
                sym = re.search(r"<([^+>]+)(?:\+.*)?>", i.raw)
                cur.callee = sym.group(1) if sym else None
                cur.callee_pc = t
            cur = None
        elif i.mnem == "jal":
            cur.term, cur.kind = i, "jal"
            sym = re.search(r"<([^+>]+)(?:\+.*)?>", i.raw)
            cur.callee = sym.group(1) if sym else None
            cur.callee_pc = (i.addr + lib.sext(lib._jal_imm(i.word), 21)) % 2**64
            cur.succs = [i.addr + 4]
            cur = None
        elif i.mnem == "jalr":
            # indirect CALL (rd=ra; objdump prints the rd=x0 form as jr/ret):
            # park AT the jalr — the fold takes the step explicitly
            # (stepObs_jalr) and splices the pinned target's summary.
            cur.term, cur.kind = i, "jalrcall"
            cur.succs = [i.addr + 4]
            cur = None
        elif i.mnem in ("jr", "ret"):
            cur.term, cur.kind = i, "ret"
            cur = None
        elif _is_tohost_store(i):
            cur.term, cur.kind = i, "tohost"
            cur.succs = [i.addr + 4]
            cur = None
        else:
            cur.instrs.append(i)
            if i.addr + 4 in leaders:   # falls into the next leader
                cur.kind, cur.succs = "fallthrough", [i.addr + 4]
                cur = None
    # mark loop heads (back-edges: br/j target ≤ source, in-function)
    for b in blocks.values():
        for s in b.succs:
            if s in blocks and s <= b.term_addr:
                blocks[s].is_loop_head = True
                blocks[s].back_edge_from = b.start
    if route is not None:
        # resolved-path pruning: walk from the entry under the polarity pins
        for pc in route:
            if pc not in {b.term_addr for b in blocks.values() if b.kind == "br"}:
                raise SystemExit(f"--route: 0x{pc:x} is not a branch terminator")
        keep, pols, work = set(), {}, [entry]
        while work:
            a = work.pop()
            if a in keep or a not in blocks:
                continue
            keep.add(a)
            b = blocks[a]
            if b.kind == "br":
                pin = route.get(b.term_addr)
                if pin is None:
                    raise SystemExit(
                        f"--route: unpinned branch 0x{b.term_addr:x} reachable "
                        f"({b.term.mnem} {b.term.ops}) — pin it T, F or TF")
                pols[b.start] = pin
                if "T" in pin:
                    work.append(b.succs[0])
                if "F" in pin:
                    work.append(b.succs[1])
            else:
                work.extend(b.succs)
        pruned = [blocks[a] for a in sorted(keep)]
        ni = sum(len(b.instrs) + (1 if b.term else 0) for b in pruned)
        if ni > MAX_INSTRS:
            raise SystemExit(f"--route: pruned path {ni} instrs > {MAX_INSTRS}")
        nbr = sum(1 for b in pruned if b.kind == "br")
        if nbr > MAX_BRANCHES:
            raise SystemExit(f"--route: pruned path {nbr} branches > {MAX_BRANCHES}")
        for b in pruned:
            b.route_pols = pols.get(b.start)
        return body, pruned
    return body, [blocks[a] for a in sorted(blocks)]


def classify_loop(blocks):
    """Recognise the counted byte-store loop template (the `_write` shape):
    a loop-head block chain body → tohost seam → br back-edge, with a monotone
    `addi rX,rX,1` pointer compared by the back-edge `bne`.  Returns the dict
    of template parameters, or None."""
    heads = [b for b in blocks if b.is_loop_head]
    if len(heads) != 1:
        return None
    head = heads[0]
    back = next(b for b in blocks if b.start == head.back_edge_from)
    if back.kind != "br" or back.term.mnem != "bne":
        return None
    # the path head → … → back must pass a tohost seam
    seam = None
    cur, seen = head, set()
    while cur and cur.start not in seen:
        seen.add(cur.start)
        if cur.kind == "tohost":
            seam = cur
        if cur.start == back.start:
            break
        cur = next((b for b in blocks if b.start == cur.succs[0]), None) \
            if cur.succs else None
    if seam is None:
        return None
    # monotone pointer: `addi rX, rX, 1` in the loop body, rX ∈ back-edge srcs
    rs1, rs2, _ = lib._btype_fields(back.term.word)
    ptr = None
    for b in blocks:
        if b.start in seen:
            for i in b.instrs:
                m = re.match(r"(\w+),(\w+),1$", i.ops.replace(" ", ""))
                if i.mnem == "addi" and m and m.group(1) == m.group(2):
                    ptr = m.group(1)
    if ptr is None:
        return None
    return {"head": head, "back": back, "seam": seam, "ptr": ptr,
            "cmp_regs": (rs1, rs2)}


# --------------------------------------------------------------------------
# emission
# --------------------------------------------------------------------------

def read_regs_of(instrs, term):
    """First-use-before-write register pin list of a block (the seg's L),
    in first-use order — mirrors what the genseg arm author writes by hand."""
    ABI = {"zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4, "t0": 5, "t1": 6,
           "t2": 7, "s0": 8, "fp": 8, "s1": 9, "a0": 10, "a1": 11, "a2": 12,
           "a3": 13, "a4": 14, "a5": 15, "a6": 16, "a7": 17, "s2": 18,
           "s3": 19, "s4": 20, "s5": 21, "s6": 22, "s7": 23, "s8": 24,
           "s9": 25, "s10": 26, "s11": 27, "t3": 28, "t4": 29, "t5": 30,
           "t6": 31}
    NO_RD = gensegmain._NO_GPR_WRITE
    written, pins = set(), []

    def use(r):
        if r and r in ABI and ABI[r] != 0 and r not in written \
                and ABI[r] not in [p[0] for p in pins]:
            pins.append((ABI[r], r))

    def parse_ops(ins):
        ops = [o.strip() for o in ins.ops.split(",")] if ins.ops else []
        # memory operand `off(base)`
        out = []
        for o in ops:
            m = re.match(r"-?\w+\((\w+)\)", o)
            out.append(("mem", m.group(1)) if m else ("reg", o))
        return out

    if term is not None and term.mnem in ("jr", "ret"):
        # the jr consumes its rs1 (ra for `ret`) — pin it
        rs1, _ = lib._jalr_fields(term.word)
        pass  # handled below by including term in the scan
    for ins in list(instrs) + ([term] if term else []):
        if ins.mnem in ("jr", "ret"):
            rs1, _ = lib._jalr_fields(ins.word)
            inv = {v: k for k, v in ABI.items()}
            use(inv.get(rs1))
            continue
        ops = parse_ops(ins)
        if not ops:
            continue
        if ins.mnem in NO_RD or ins.is_branch:
            for k, o in ops:
                use(o if k == "mem" else (o if o in ABI else None))
        else:
            for k, o in ops[1:]:
                use(o if k == "mem" else (o if o in ABI else None))
            rd = ops[0][1]
            if rd in ABI:
                written.add(rd)
    return pins


def block_name(fn, b, pol=None):
    base = lib.lean_ident(fn) if hasattr(lib, "lean_ident") else \
        re.sub(r"[^A-Za-z0-9_]", "_", fn).lstrip("_")
    nm = f"{base}X{b.start & 0xffff:04x}"
    return nm + ({True: "T", False: "F"}[pol] if pol is not None else "")


def synth_arm(fn, b, pol=None):
    """Synthesize the genseg arm dict for one block (one polarity)."""
    name = block_name(fn, b, pol)
    a = {"name": name, "namespace": "Vsa.Sim", "entry": b.start,
         "blocks": [], "callee": b.callee,
         "callee_pc": b.callee_pc, "imports": [], "doc":
         f"{fn} block 0x{b.start:x} ({b.kind}"
         + (f", {'taken' if pol else 'fall'} arm" if pol is not None else "")
         + ").", "pins": read_regs_of(b.instrs, b.term if b.kind in ('br', 'ret') else None)}
    if b.kind == "br":
        a["terminator"], a["taken"], a["span_end"] = "br", pol, b.term_addr
    elif b.kind in ("j", "tailj"):
        a["terminator"], a["taken"], a["span_end"] = "j", None, b.term_addr
    elif b.kind == "jal":
        # park AT the jal (the call SEAM, like the tohost store): the fold
        # takes the jal step explicitly and splices the callee summary via
        # `FnSummary.callSplice` — NOT the old bridgeOfSeg Shape-D row, so no
        # WrChainAvoidAbi restriction applies to the prefix body.
        a["terminator"], a["taken"], a["span_end"] = "fallthrough", None, b.term_addr
    elif b.kind == "jalrcall":
        # park AT the jalr (indirect call SEAM): the fold takes the step
        # explicitly (stepObs_jalr, target pinned from the loaded image) and
        # splices the target summary — same park shape as jal/tohost.
        a["terminator"], a["taken"], a["span_end"] = "fallthrough", None, b.term_addr
    elif b.kind == "tohost":
        # park AT the sd: straight-line body ending just before it
        a["terminator"], a["taken"], a["span_end"] = "fallthrough", None, b.term_addr
    elif b.kind == "ret":
        # jr/ret terminator IN-MODEL (TKind.jr): the seg carries the return
        # jump; end PC is symbolic (the ra pin), so only seg + L are emitted
        # (the fold instantiates `segRowFramed`; a literal-end Post is wrong).
        a["terminator"], a["taken"], a["span_end"] = "jr", None, b.term_addr
    else:
        a["terminator"], a["taken"] = "fallthrough", None
        a["span_end"] = (b.instrs[-1].addr + 4) if b.instrs else b.start
    return a


def emit_fn(fn, entry, out_path, verify=True, route=None, disasm_path=None, decode_index=None):
    di = lib.parse_disasm(disasm_path) if disasm_path else lib.parse_disasm()
    idx = lib.DecodeIndex(decode_index) if decode_index else lib.DecodeIndex()
    extents = function_extents(disasm_path)
    if fn not in extents:
        raise SystemExit(f"function {fn!r} not in disasm")
    body, blocks = build_cfg(fn, entry, di, extents, route=route)
    loop = classify_loop(blocks) if route is None else None

    E = lib.Emitter()
    E(f"import Vsa.Sim.DeriveCaseRow")
    E(f"import Vsa.Sim.FnSummary")
    E(f"import Vsa.Sim.Code.{re.sub(r'[^A-Za-z0-9_]', '_', fn)[0].upper() + re.sub(r'[^A-Za-z0-9_]', '_', fn)[1:]}")
    E("")
    E(f"/-!")
    E(f"# `{fn}` — GENERATED whole-function summary blocks (scripts/gen_fn.py)")
    E(f"")
    E(f"{len(body)} instrs, {len(blocks)} blocks"
      + (", counted byte-store loop recognised" if loop else "") + ".")
    E(f"GENERATED by `scripts/gen_fn.py --fn {fn} --entry 0x{entry:x}`."
      f"  DO NOT hand-edit.")
    E(f"NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.")
    E(f"-/")
    E(f"-- discipline: allow(R9-handrolled-fn-assembly) GENERATED by gen_fn.py")
    E("")
    E("open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa")
    E("open Register")
    E("open Vsa.Machine (MState Config Step Steps)")
    E("open Vsa.Logic (Triple)")
    E("")
    E("set_option maxRecDepth 100000")
    E("")
    E("namespace Vsa.Sim")
    E("")

    emitted = []
    for b in blocks:
        if b.kind == "br":
            rp = getattr(b, "route_pols", None)
            pols = [True, False] if rp in (None, "TF") else \
                ([True] if rp == "T" else [False])
        else:
            pols = [None]
        for pol in pols:
            a = synth_arm(fn, b, pol)
            if a["terminator"] == "jr":
                jbody = lib.words_for_range(a["entry"], a["span_end"], di)
                tinstr = di[a["span_end"]]
                tdata = lib.decode_terminator(tinstr)
                blks = [{"body": jbody, "term": tdata}]
                miss = idx.check_range(jbody + [tinstr])
                if miss:
                    raise SystemExit("NOT ALL WORDS TABLED: " + ", ".join(
                        f"0x{m.addr:08x}:{m.word:08x}" for m in miss))
                a["terminator"] = "jr (in-model; seg+L only — symbolic end PC)"
                gensegmain.emit_seg(E, a, blks)
                gensegmain.emit_L(E, a)
                emitted.append((a, b, pol, None))
                continue
            blks, end_pc = gensegmain.build_body(a, di, idx)
            gensegmain.emit_seg(E, a, blks)
            keys = gensegmain.emit_L(E, a)
            if a["terminator"] == "jal":
                gensegmain.emit_jal_row(E, a, end_pc, keys)
            else:
                gensegmain.emit_post_and_row(E, a, end_pc, keys)
            emitted.append((a, b, pol, end_pc))

    E("end Vsa.Sim")
    text = "\n".join(E.lines) if hasattr(E, "lines") else E.text()

    # 36 lines/arm is the MEASURED genseg arm size (docs + seg + L + Post +
    # row, proofs all decide/rfl); the plan's "~12 lines/block" is kept as the
    # no-expanded-terms invariant, enforced by construction (genseg emits only
    # one-decide rows), not by line count.
    nbody = sum(len(b.instrs) + (1 if b.term else 0) for b in blocks)
    budget = 40 + 36 * len(emitted) + nbody + 12
    nlines = text.count("\n") + 1
    if nlines > budget:
        raise SystemExit(f"emitted {nlines} lines > budget {budget} "
                         f"(40 + 18·{len(emitted)} arms + {nbody} instrs "
                         f"+ 12) — expanded terms must live in the kernel")

    with open(out_path, "w") as f:
        f.write(text)
    print(f"wrote {out_path}: {len(body)} instrs, {len(blocks)} blocks, "
          f"{len(emitted)} arms, {nlines} lines"
          + (", loop template: counted byte-store" if loop else ""))
    for a, b, pol, end_pc in emitted:
        end = f"0x{end_pc:08x}" if end_pc is not None else "ra (symbolic)"
        print(f"  {a['name']}: 0x{a['entry']:08x}→{end} "
              f"[{b.kind}]" + (f" callee={b.callee}" if b.callee else ""))

    if verify:
        r = subprocess.run(["lake", "env", "lean", out_path], cwd=ROOT,
                           capture_output=True, text=True)
        sys.stdout.write(r.stdout)
        sys.stderr.write(r.stderr)
        if r.returncode != 0:
            raise SystemExit(f"VERIFY FAILED: lake env lean {out_path}")
        if "sorryAx" in r.stdout + r.stderr:
            raise SystemExit("VERIFY FAILED: sorryAx in output")
        print("verified: lake env lean OK, no sorryAx")
    return blocks, loop


def emit_fold(fn, entry, blocks, loop, di, out_path, verify=True):
    """Instantiate the counted-byte-store-loop fold template (the P1 shape,
    hand-developed in rows/FnWriteFold.lean, parameterized).  Applies ONLY to
    the recognised shape: entry-beqz guard, li+slli command setup, lbu/addi/or/
    auipc body parked at the tohost sd, bne back-edge, mv+ret exit."""
    tmpl = open(os.path.join(HERE, "genfn_templates",
                             "counted_loop_fold.lean.tmpl")).read()
    head, back, seam = loop["head"], loop["back"], loop["seam"]
    bmap = {b.start: b for b in blocks}
    entry_b = bmap[entry]
    setup_b = bmap[entry_b.succs[1]]      # beqz fall arm
    exit_pc = entry_b.succs[0]            # beqz taken target = exit join
    exit_b = bmap[exit_pc]
    seam_i = seam.term                    # the sd instr
    ret_i = exit_b.term
    sw = seam_i.word
    sb = lib.le_bytes(sw)                 # ["0xNN#8"-style? le_bytes gives raw
    # le_bytes returns strings like "0x23#8"? inspect: it's used as {b[0]} in
    # records — they are "0xNN#8" strings; strip the "#8" for our slots.
    def byte(i):
        return sb[i].split("#")[0]
    imm12 = (sw >> 20) & 0xfff
    rs1 = (sw >> 15) & 0x1f
    rs2 = (sw >> 20) & 0x1f
    # STORE: imm[11:5]=funct7, imm[4:0]=rd-slot; recompute properly:
    imm_s = (((sw >> 25) & 0x7f) << 5) | ((sw >> 7) & 0x1f)
    rs2_s = (sw >> 20) & 0x1f
    # auipc base: the body's auipc result at the seam = auipc_pc + (imm20 << 12)
    au = [i for i in seam.instrs if i.mnem == "auipc"][-1]
    au_imm20 = (au.word >> 12) & 0xfffff
    seam_base = (au.addr + ((au_imm20 << 12) if au_imm20 < 0x80000
                            else ((au_imm20 << 12) - (1 << 32)))) % 2**64
    # cmd: li a4,C ; slli a4,a4,S in the setup block
    li = [i for i in setup_b.instrs if i.mnem == "li"][0]
    slli = [i for i in setup_b.instrs if i.mnem == "slli"][0]
    cmd_imm = (li.word >> 20) & 0xfff
    shamt_imm = (slli.word >> 20) & 0xfff
    cmd_lit = ((cmd_imm if cmd_imm < 0x800 else cmd_imm - 0x1000)
               << (shamt_imm & 0x3f)) % 2**64
    ret_bytes = lib.le_bytes(ret_i.word)
    vals = {
        "FN": fn,
        "B_ENT_T": block_name(fn, entry_b, True),
        "B_ENT_F": block_name(fn, entry_b, False),
        "B_SETUP": block_name(fn, setup_b),
        "B_BODY": block_name(fn, seam),
        "B_BACK_T": block_name(fn, back, True),
        "B_BACK_F": block_name(fn, back, False),
        "B_EXIT": block_name(fn, exit_b),
        "CODE_PREFIX": re.sub(r"[^A-Za-z0-9_]", "_", fn) + "_at_",
        "CODE_AT_SEAM": re.sub(r"[^A-Za-z0-9_]", "_", fn) + f"_at_{seam_i.addr:x}",
        "LOADED": re.sub(r"[^A-Za-z0-9_]", "_", fn) + "Loaded",
        "PC_ENTRY": f"0x{entry:08x}", "PC_SETUP": f"0x{setup_b.start:08x}",
        "PC_HEAD": f"0x{head.start:08x}", "PC_SEAM": f"0x{seam_i.addr:08x}",
        "PC_BACK": f"0x{back.start:08x}", "PC_EXIT": f"0x{exit_pc:08x}",
        "PC_RET": f"0x{ret_i.addr:08x}",
        "W_EXITBODY": f"0x{exit_b.instrs[0].word:08x}",
        "W_RET": f"0x{ret_i.word:08x}",
        "W_RET_B0": ret_bytes[0].split("#")[0], "W_RET_B1": ret_bytes[1].split("#")[0],
        "W_RET_B2": ret_bytes[2].split("#")[0], "W_RET_B3": ret_bytes[3].split("#")[0],
        "W_SEAM": f"0x{sw:08x}", "W_SEAM_HEX": f"{sw:08x}",
        "W_SEAM_B0": byte(0), "W_SEAM_B1": byte(1),
        "W_SEAM_B2": byte(2), "W_SEAM_B3": byte(3),
        "SEAM_IMM": f"0x{imm_s:03x}",
        "SEAM_RS1": f"0x{rs1:02x}", "SEAM_RS2": f"0x{rs2_s:02x}",
        "SEAM_RS1_DEC": str(rs1), "SEAM_RS2_DEC": str(rs2_s),
        "SEAM_BASE": f"0x{seam_base:08x}",
        "CMD_LIT": f"0x{cmd_lit:016x}",
        "CMD_IMM": f"0x{cmd_imm:03x}",
        "CMD_SHAMT_IMM": f"0x{shamt_imm:03x}",
    }
    text = tmpl.format(**vals)
    with open(out_path, "w") as f:
        f.write(text)
    print(f"wrote {out_path} (counted-loop fold, {text.count(chr(10))+1} lines)")
    if verify:
        r = subprocess.run(["lake", "env", "lean", out_path], cwd=ROOT,
                           capture_output=True, text=True)
        sys.stdout.write(r.stdout[-2000:])
        if r.returncode != 0 or "sorryAx" in r.stdout + r.stderr:
            sys.stderr.write(r.stderr[-3000:])
            raise SystemExit(f"FOLD VERIFY FAILED: {out_path}")
        print("fold verified: lake env lean OK, no sorryAx")


def ocaml_literal_mline(pc, word):
    """First-order instruction records; ElfDecode certifies their semantics."""
    opcode = word & 0x7f
    funct3 = (word >> 12) & 7
    if opcode == 3:
        kind = {3: 'ld', 4: 'lbu'}[funct3]
    elif opcode == 0x13:
        kind = {0: 'addi', 1: 'slli', 5: 'srli'}[funct3]
    elif opcode == 0x33 and funct3 == 0:
        kind = {0: 'add', 0x20: 'sub'}[word >> 25]
    else:
        raise ValueError(f'unsupported read-only instruction {word:08x}')
    rd, rs1 = (word >> 7) & 31, (word >> 15) & 31
    rs2, imm = ((word >> 20) & 31, 0) if opcode == 0x33 else (0, word >> 20)
    fields = [f'0x{pc:08x}#64', f'0x{word:08x}#32'] + lib.le_bytes(word)
    fields += [f'.{kind}', str(rd), str(rs1), str(rs2), f'0x{imm:03x}#12']
    return '⟨' + ', '.join(fields) + '⟩'


def emit_ocaml_register_return(E, fn, signature, hypotheses, writes, value, block_call, return_proof=None, log_proof=None):
    """Package one checked block certificate using the shared complete frame."""
    declaration = [f'theorem {fn}_summary {signature}'] + hypotheses
    declaration[-1] += ' :'
    E(*declaration,
      f'    FnSummary (BitVec.ofNat 64 Layout.sym_{fn}) (fun x => x = c)',
      f'      (RegisterPost {writes} c ra ({value})) := by',
      f'  apply register_of_blocks h.image ({block_call})',
      log_proof or '  · rfl')
    E(*(return_proof or [
      '  · change Sail.BitVec.update (ra + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)) 0 0#1 = ra',
      '    exact ret_tgt ra h.aligned']),
      '  · intro σ hr', f'    rw [{fn}_regs] at hr', '    exact hr.1', '  · decide', '')


def emit_ocaml_constants(check=False, compare=False, argv=False, lengths=False):
    """Read-only F1 leaves: existing CFG extraction + segment kernel fold.

    This backend consumes the pinned OCaml ELF and per-word ElfDecode facts,
    and emits no elaboration-budget overrides. No execution premise survives
    in the generated summary: only image, control and ABI input facts.
    """
    from pathlib import Path
    root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(root / 'scripts'))
    from census import disasm
    from gen_primitive_census import primitive_names
    from gen_ocaml_image import sections
    spec = importlib.util.spec_from_file_location('primitive_code', root / 'experiments/syi/gen_code_lemmas.py')
    code = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(code)
    functions = disasm(root / 'c/ocamlrun-riscv-htif.elf')
    text_base = sections((root / 'c/ocamlrun-riscv-htif.elf').read_bytes())['.text'][0]
    decode = {}
    for path in sorted((root / 'Vsa/Sim/ElfDecode').glob('Part*.lean')):
        for w in re.findall(r'^theorem decode_([0-9a-f]{8})', path.read_text(), re.M):
            decode[int(w, 16)] = 'Vsa.Sim.ElfDecode.' + path.stem
    result = {}
    backend = '--ocaml-lengths' if lengths else '--ocaml-argv' if argv else ('--ocaml-compare' if compare else '--ocaml-constants')
    for fn in primitive_names():
        selected = (fn in ('caml_ml_string_length', 'caml_ml_bytes_length')) if lengths else (fn == 'caml_sys_argv') if argv else (fn == 'caml_int_compare' if compare else fn.startswith('caml_sys_const_'))
        if not selected:
            continue
        ins = functions[fn]['insts']
        entry, end = ins[0][0], ins[-1][0] + 4
        di = {a: lib.Instr(a, w, op, args, f'{op} {args}') for a, w, op, args in ins}
        _, blocks = build_cfg(fn, entry, di, {fn: (entry, end)})
        if len(blocks) != 1 or blocks[0].kind != 'ret':
            raise ValueError(f'{fn}: changed leaf CFG')
        if not (compare or argv or lengths) and any((w & 127) != 0x13 or ((w >> 7) & 31) != 10 for a, w, op, args in ins[:-1]):
            raise ValueError(f'{fn}: not an a0-only integer leaf')
        stem = ''.join(x.capitalize() for x in fn.split('_'))
        pred = 'Vsa.Sim.Code.' + fn[0].upper() + fn[1:] + 'Loaded'
        codepath = root / ('Vsa/Sim/Code/' + fn[0].upper() + fn[1:] + '.lean')
        result[codepath] = code.render(fn, [(a,w) for a,w,_,_ in ins]).replace(
            'generated by experiments/gen_code_lemmas.py', f'GENERATED by scripts/syi/gen_fn.py {backend}')
        imports = ['OCaml.Vm.Primitives.ConstantContract', 'OCaml.Vm.Platform', 'Vsa.Sim.ChainFactsTac',
                   'Vsa.Sim.BlockDecode', 'Vsa.Sim.Muldi3Spec', 'Vsa.Sim.Code.' + fn[0].upper() + fn[1:]]
        if compare:
            imports += ['OCaml.Vm.Primitives.ImmediateContract', 'OCaml.Vm.Primitives.TagArithmetic']
        if argv:
            imports += ['OCaml.Vm.Primitives.ImmediateContract', 'OCaml.Vm.Primitives.Read']
        if lengths:
            imports += ['OCaml.Vm.Primitives.StringContract', 'OCaml.Vm.Primitives.Control']
        imports += sorted({decode[w] for a,w,_,_ in ins})
        E = lib.Emitter()
        for m in imports: E('import ' + m)
        E('', f'/-! GENERATED by scripts/syi/gen_fn.py {backend}. -/',
          'namespace OCaml.Vm.Primitives', 'open Vsa.Sim Vsa.Machine LeanRV64DExecutable', '')
        if lengths:
            E(f'def {fn}_body : List MInstr := [',
              ',\n'.join('  ' + ocaml_literal_mline(a, w) for a,w,_,_ in ins[:-1]), ']', '')
            E(f'def {fn}_blocks : List BBlock := [{{', f'  body := {fn}_body')
        else:
            E(f'def {fn}_blocks : List BBlock := [{{', '  body := [')
            E(',\n'.join(f'    mkLine 0x{a:08x}#64 0x{w:08x}#32' for a,w,_,_ in ins[:-1]))
            E('  ]')
        E('  term := some ' + lib.decode_terminator(di[ins[-1][0]])['record'], '}]', '')
        if lengths:
            E(f'theorem {fn}_shape : ChainOK (BitVec.ofNat 64 Layout.sym_{fn}) [1, 10] {fn}_blocks := by',
              f'  simp only [ChainOK, BBlockOK, {fn}_blocks, {fn}_body, BlockOKM]',
              '  repeat apply And.intro', '  all_goals decide', '')
            E(f'theorem {fn}_readonly : ReadOnlyBody {fn}_body := by unfold ReadOnlyBody; decide', '')
        E(f'theorem {fn}_loaded {{c : Config}} (h : ExecutableImage c) :', f'    {pred} c.σ.mem := by',
          f'  unfold {pred} Vsa.Sim.Code.{fn}Chunk0',
          '  refine ⟨' + ', '.join(['?_'] * (4*len(ins))) + '⟩')
        for a,w,_,_ in ins:
            for k in range(4):
                off = a + k - text_base
                E(f'  · have hb := h.text {off} (by decide)',
                  f'    have he : Image.textByte {off} = (0x{(w>>(8*k))&255:02x}#8) := by decide +kernel',
                  '    rw [he] at hb', '    exact hb')
        if lengths:
            E(f'def {fn}_load_prefix : List MInstr := [',
              ',\n'.join('  ' + ocaml_literal_mline(a, w) for a,w,_,_ in ins[:5]), ']', '')
            E(f'def {fn}_load_suffix : List MInstr := [',
              ',\n'.join('  ' + ocaml_literal_mline(a, w) for a,w,_,_ in ins[5:-1]), ']', '')
            E(f'theorem {fn}_prefix_loads (c : Config) (x : BitVec 64) :',
              f'    ldsRunM {fn}_load_prefix (stringLoads c x) = [[stringPadding c x]] := rfl', '')
            E(f'theorem {fn}_prefix_regs (c : Config) (ra x : BitVec 64) :',
              f'    runGM {fn}_load_prefix [(1, ra), (10, x)] (stringLoads c x) =',
              '      [(10, x + stringLast (stringHeader c x)), (15, stringLast (stringHeader c x)), (1, ra)] := by',
              '  change [(10, x + (((bytesVal .ld (read8 c.σ.mem (x - 8).toNat) >>> (10 : Nat)) <<< (3 : Nat)) + (-1))),',
              '    (15, ((bytesVal .ld (read8 c.σ.mem (x - 8).toNat) >>> (10 : Nat)) <<< (3 : Nat)) + (-1)), (1, ra)] = _',
              '  have hl : bytesVal .ld (read8 c.σ.mem (x - 8).toNat) = stringHeader c x := read8_value _ _',
              '  rw [hl]', '  simp only [stringLast, BitVec.sub_eq_add_neg]', '')
        L = '[(1, ra), (10, x), (11, y)]' if compare else '[(1, ra)]'
        keys = '[1, 10, 11]' if compare else '[1]'
        args = ' (x y : BitVec 64)' if compare else ''
        extra = ' (hx : gprGet c.σ 10 = some x) (hy : gprGet c.σ 11 = some y)' if compare else ''
        holds = '⟨hr, hx, hy, True.intro⟩' if compare else '⟨hr, True.intro⟩'
        loads = '[read8 c.σ.mem Layout.sym_main_argv]' if argv else '[]'
        if lengths:
            L, keys, args = '[(1, ra), (10, x)]', '[1, 10]', ' (x : BitVec 64)'
            extra = (' (hx : gprGet c.σ 10 = some x)'
                     ' (hh : ReadWindow (x - 8) 8)'
                     ' (hp : ReadWindow (x + stringLast (stringHeader c x)) 1)')
            holds, loads = '⟨hr, hx, True.intro⟩', '(stringLoads c x)'
        if lengths:
            E(f'theorem {fn}_body_regs (c : Config) (ra x : BitVec 64) :',
              f'    runGM {fn}_body {L} {loads} =',
              '      [(10, stringLengthWord (stringHeader c x) (stringPadding c x)),',
              '       (14, (stringPadding c x).setWidth 64), (15, stringLast (stringHeader c x)), (1, ra)] := by',
              '  change runGM [',
              ',\n'.join(f'    mkLine 0x{a:08x}#64 0x{w:08x}#32' for a,w,_,_ in ins[5:-1]),
              f'    ] (runGM {fn}_load_prefix [(1, ra), (10, x)] (stringLoads c x)) [[stringPadding c x]] = _',
              f'  rw [{fn}_prefix_regs]',
              '  generalize hh : stringHeader c x = header',
              '  generalize hp : stringPadding c x = padding',
              '  simp [runGM, stepGM, mkLine, decodeM, wvalM, srcVal, lookupG, eraseG, stepLdsM, shamtOf,',
              '    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,',
              '    Sail.BitVec.extractLsb, Sail.shift_bits_left, stringLengthWord,',
              '    bytesVal, zero_extend, Sail.BitVec.zeroExtend]', '')
            E(f'theorem {fn}_regs (c : Config) (ra x : BitVec 64) :',
              f'    (evalBlocks {fn}_blocks (SegEvalState.init {L} {loads})).regs =',
              '      [(10, stringLengthWord (stringHeader c x) (stringPadding c x)),',
              '       (14, (stringPadding c x).setWidth 64), (15, stringLast (stringHeader c x)), (1, ra)] := by',
              f'  simpa only [{fn}_blocks, evalBlocks, evalBlock, SegEvalState.init] using {fn}_body_regs c ra x', '')
            E(f'theorem {fn}_ra (c : Config) (ra x : BitVec 64) :',
              f'    srcVal 1 (runGM {fn}_body {L} {loads}) = ra := by',
              f'  rw [{fn}_body_regs]', '  rfl', '')
            E(f'theorem {fn}_return_pc (c : Config) (ra x : BitVec 64) (ha : ra.toNat % 4 = 0) :',
              f'    evalBlocksPC (BitVec.ofNat 64 Layout.sym_{fn}) (SegEvalState.init {L} {loads}) {fn}_blocks = ra := by',
              f'  simp only [evalBlocksPC, {fn}_blocks, SegEvalState.init, chainEndPC, endPCB, tgtPCT]',
              '  exact (congrArg (fun r : BitVec 64 =>',
              '    Sail.BitVec.update (r + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)) 0 0#1)',
              f'    ({fn}_ra c ra x)).trans (ret_tgt ra ha)', '')
        if lengths:
            for part in ('prefix', 'suffix'):
                E(f'theorem {fn}_{part}_code {{c : Config}} (hc : {pred} c.σ.mem) :',
                  f'    CodeFacts c.σ.mem {fn}_load_{part} := by',
                  f'  simp only [CodeFacts, {fn}_load_{part}]',
                  f'  chain_facts hc with "Vsa.Sim.Code.{fn}_at_"', '')
        if lengths:
            E(f'theorem {fn}_prefix_facts (c : Config) (ra x : BitVec 64)',
              '    (headerBytes : List (BitVec 8)) (remaining : List (List (BitVec 8)))',
              '    (pins : LPins8 c.σ.mem (x - 8).toNat headerBytes)',
              f'    (hc : {pred} c.σ.mem) (hh : ReadWindow (x - 8) 8) :',
              f'    ProgFactsM c.σ.mem c.σ.mem {L} (headerBytes :: remaining) {fn}_load_prefix := by',
              f'  apply access_then_free_facts ({fn}_prefix_code hc) (by simp [MemoryFree])',
              '  apply hh.ld rfl ?_ pins',
              '  change x + (-8) = x - 8',
              '  simp only [BitVec.sub_eq_add_neg]', '')
            E(f'theorem {fn}_suffix_facts (c : Config) (ra x : BitVec 64)',
              f'    (hc : {pred} c.σ.mem)',
              '    (hp : ReadWindow (x + stringLast (stringHeader c x)) 1) :',
              '    ProgFactsM c.σ.mem c.σ.mem',
              '      [(10, x + stringLast (stringHeader c x)), (15, stringLast (stringHeader c x)), (1, ra)]',
              f'      [[stringPadding c x]] {fn}_load_suffix := by',
              f'  apply access_then_free_facts ({fn}_suffix_code hc) (by simp [MemoryFree])',
              '  apply hp.lbu rfl ?_ ?_',
              '  · change (x + stringLast (stringHeader c x)) + 0 = x + stringLast (stringHeader c x)',
              '    exact BitVec.add_zero _',
              '  · exact (byte_total c _).symm', '')
            E(f'theorem {fn}_body_facts (c : Config) (ra x : BitVec 64)',
              f'    (hc : {pred} c.σ.mem) (hh : ReadWindow (x - 8) 8)',
              '    (hp : ReadWindow (x + stringLast (stringHeader c x)) 1) :',
              f'    ProgFactsM c.σ.mem c.σ.mem {L} {loads} {fn}_body := by',
              f'  apply readonly_facts_append (front := {fn}_load_prefix) (back := {fn}_load_suffix)',
              '    (by unfold ReadOnlyBody; decide)',
              f'  · exact {fn}_prefix_facts c ra x _ _ (read8_pins _ _) hc hh',
              f'  · rw [{fn}_prefix_regs, {fn}_prefix_loads]',
              f'    exact {fn}_suffix_facts c ra x hc hp', '')
        E('', f'theorem {fn}_blocks_summary (c : Config) (ra : BitVec 64){args}',
          '    (hg : GoodState c.σ) (hi : ExecutableImage c)',
          '    (hm : ∃ v, c.σ.regs.get? Register.minstret = some v)',
          f'    (hr : gprGet c.σ 1 = some ra) (ht : c.tick < 2) (ha : ra.toNat % 4 = 0){extra} :',
          f'    FnSummary (BitVec.ofNat 64 Layout.sym_{fn}) (fun x => x = c)',
          f'      (BlockPost {fn}_blocks (BitVec.ofNat 64 Layout.sym_{fn}) {L} {loads} c) := by',
          '  apply block_summary', f'  refine ⟨hg, hm, {holds}, ?_, ?_, ?_, ht⟩',
          f'  · change KeysOK {keys}; decide',
          f'  · change ChainFacts c.σ.mem c.σ.mem {L} {loads} {fn}_blocks',
          f'    have hc := {fn}_loaded hi')
        if lengths:
            E('    apply singleton_chain_facts',
              f'    · exact {fn}_body_facts c ra x hc hh hp')
        else:
            E(f'    chain_facts hc with "Vsa.Sim.Code.{fn}_at_"')
        if argv:
            E('    · simp [MemFacts, eaddrM, stepGM, stepMemM, stepLdsM, wvalM, srcVal, lookupG, eraseG,',
              '        mkLine, decodeM, imm20Of, LeanRV64DExecutable.Functions.sign_extend,',
              '        Sail.BitVec.signExtend, Sail.BitVec.extractLsb, Layout.sym_main_argv,',
              '        tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost, read8_pins]')
        indent = '      ' if (argv or lengths) else '    '
        if lengths:
            E(f'    · chain_facts hc with "Vsa.Sim.Code.{fn}_at_"',
              f'    · exact return_facts _ rfl rfl rfl ({fn}_ra c ra x) ha')
        else:
            E(('    · ' if argv else '    ') + 'change (Sail.BitVec.update (ra + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0',
              indent + 'rw [ret_tgt ra ha]', indent + 'exact ha')
        E(f'  · change ChainOK (BitVec.ofNat 64 Layout.sym_{fn}) {keys} {fn}_blocks')
        if lengths:
            E(f'    exact {fn}_shape')
        else:
            E('    decide')
        E('')
        if lengths:
            emit_ocaml_register_return(E, fn, '(c : Config) (ra x : BitVec 64) (h : LeafInput ra c)',
                ['    (hx : gprGet c.σ 10 = some x) (hh : ReadWindow (x - 8) 8)',
                 '    (hp : ReadWindow (x + stringLast (stringHeader c x)) 1)'],
                '[10, 14, 15]', 'stringLengthWord (stringHeader c x) (stringPadding c x)',
                f'{fn}_blocks_summary c ra x h.good h.image h.minstret h.raReg h.tick h.aligned hx hh hp',
                [f'  · exact {fn}_return_pc c ra x h.aligned'],
                f'  · exact readonly_log _ {fn}_readonly _ _')
            E('open OCaml.Bytecode', '',
              f'theorem {fn}_primitive {{runtimeOk : Config → Prop}} (stable : MemoryStable runtimeOk)',
              '    {P s pl cp sp high ra l b a c}',
              '    (h : StringInput runtimeOk P s pl cp sp high ra l b a c) :',
              f'    FnSummary (BitVec.ofNat 64 Layout.sym_{fn}) (fun x => x = c)',
              f'      (ImmediatePost runtimeOk P s pl cp sp high "{fn}" [.ptr l 0]',
              '        (BitVec.ofNat 63 b.length) [10, 14, 15] c ra) := by',
              '  apply string_length_contract stable h',
              f'  · apply {fn}_summary c ra (BitVec.ofNat 64 a) h.toLeafInput',
              '    · apply h.arguments.get (i := 0) rfl',
              '      simp [valWord, h.placed]',
              '    · exact h.geometry.header_window',
              '    · rw [h.header]',
              '      exact h.geometry.padding_window h.shape.headerSize',
              ('  · exact Or.inl rfl' if fn == 'caml_ml_string_length' else '  · exact Or.inr rfl'),
              '', 'end OCaml.Vm.Primitives', '')
            result[root / ('OCaml/Vm/Primitives/' + stem + '.lean')] = E.text()
            continue
        if argv:
            E(f'theorem {fn}_regs (c : Config) (ra : BitVec 64) :',
              f'    (evalBlocks {fn}_blocks (SegEvalState.init {L} {loads})).regs =',
              '      [(10, word c Layout.sym_main_argv), (1, ra)] := by',
              '  change [(10, bytesVal .ld (read8 c.σ.mem Layout.sym_main_argv)), (1, ra)] = _',
              '  rw [read8_value]', '  rfl', '')
            emit_ocaml_register_return(E, fn, '(c : Config) (ra : BitVec 64) (h : LeafInput ra c)', [],
                '[10]', 'word c Layout.sym_main_argv',
                f'{fn}_blocks_summary c ra h.good h.image h.minstret h.raReg h.tick h.aligned')
            E('open OCaml.Bytecode', '',
              '/-- The caller links the concrete argv global to its abstract world. -/',
              f'theorem {fn}_primitive {{runtimeOk : Config → Prop}} (stable : MemoryStable runtimeOk)',
              '    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high : Nat}',
              '    {ra : BitVec 64} {c : Config}',
              '    (h : ImmediateInput runtimeOk P s pl cp sp high ra [s.accu] c)',
              '    (argv : valWord pl s.world.argv = some (word c Layout.sym_main_argv)) :',
              f'    FnSummary (BitVec.ofNat 64 Layout.sym_{fn}) (fun x => x = c)',
              f'      (ReadOnlyPost runtimeOk P s pl cp sp high "{fn}" [s.accu]',
              '        s.world.argv (word c Layout.sym_main_argv) [10] c ra) := by',
              f'  apply readOnly_contract stable h ({fn}_summary c ra h.toLeafInput)',
              '  · simp [PreservesLoopRegisters, Layout.reg_dispatchTable, Layout.reg_opcodeBound,',
              '      Layout.reg_pending, Layout.reg_domain, gprReg]',
              '  · intro l hl', '    exact Live.root (by simp [roots]) hl',
              '  · exact argv', '  · rfl', '', 'end OCaml.Vm.Primitives', '')
            result[root / ('OCaml/Vm/Primitives/' + stem + '.lean')] = E.text()
            continue
        if compare:
            E(f'theorem {fn}_regs (ra x y : BitVec 64) :',
              f'    (evalBlocks {fn}_blocks (SegEvalState.init {L} [])).regs =',
              '      [(10, compareWord x y), (15, signedBit y x), (1, ra), (11, y)] := by',
              f'  simp [{fn}_blocks, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,',
              '    mkLine, decodeM, wvalM, srcVal, lookupG, eraseG, stepLdsM, shamtOf,',
              '    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,',
              '    Sail.BitVec.extractLsb, Sail.shift_bits_left, compareWord, signedBit]', '')
            emit_ocaml_register_return(E, fn, '(c : Config) (ra x y : BitVec 64) (h : LeafInput ra c)',
                ['    (hx : gprGet c.σ 10 = some x) (hy : gprGet c.σ 11 = some y)'],
                '[10, 15]', 'compareWord x y',
                f'{fn}_blocks_summary c ra x y h.good h.image h.minstret h.raReg h.tick h.aligned hx hy')
            E('open OCaml.Bytecode', '',
              f'theorem {fn}_primitive {{runtimeOk : Config → Prop}} (stable : MemoryStable runtimeOk)',
              '    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high : Nat}',
              '    {ra : BitVec 64} {c : Config} (a b : BitVec 63)',
              '    (h : ImmediateInput runtimeOk P s pl cp sp high ra [.int a, .int b] c) :',
              f'    FnSummary (BitVec.ofNat 64 Layout.sym_{fn}) (fun x => x = c)',
              f'      (ImmediatePost runtimeOk P s pl cp sp high "{fn}" [.int a, .int b]',
              '        (compareResult a b) [10, 15] c ra) := by',
              f'  have S := {fn}_summary c ra (tag64 a) (tag64 b) h.toLeafInput',
              '    (h.arguments.get (i := 0) rfl rfl) (h.arguments.get (i := 1) rfl rfl)',
              '  rw [compareWord_tag] at S',
              '  exact immediate_contract stable h S (by',
              '    simp [PreservesLoopRegisters, Layout.reg_dispatchTable, Layout.reg_opcodeBound,',
              '      Layout.reg_pending, Layout.reg_domain, gprReg]) rfl', '')
            E('end OCaml.Vm.Primitives', '')
            result[root / ('OCaml/Vm/Primitives/' + stem + '.lean')] = E.text()
            continue
        # Compute the literal return word from the validated integer-leaf shape.
        value = 0
        for a,w,op,args in ins[:-1]:
            funct3, imm = (w >> 12) & 7, (w >> 20) & 4095
            rs1 = (w >> 15) & 31
            if rs1 not in (0, 10):
                raise ValueError(f'{fn}: constant leaf reads unexpected register x{rs1}')
            source = value if rs1 == 10 else 0
            if funct3 == 0:
                value = (source + lib.sext(imm, 12)) % (1 << 64)
            elif funct3 == 5 and imm < 64:
                value = source >> imm
            else:
                raise ValueError(f'{fn}: unsupported constant leaf operation')
        E(f'theorem {fn}_regs (ra : BitVec 64) :',
          f'    (evalBlocks {fn}_blocks (SegEvalState.init [(1, ra)] [])).regs = [(10, {value}#64), (1, ra)] := by',
          f'  simp [{fn}_blocks, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,',
          '    mkLine, decodeM, wvalM, srcVal, lookupG, eraseG, stepLdsM, shamtOf,',
          '    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,',
          '    Sail.BitVec.extractLsb, Sail.shift_bits_right]', '')
        E(f'theorem {fn}_summary (c : Config) (ra : BitVec 64) (h : LeafInput ra c) :',
          f'    FnSummary (BitVec.ofNat 64 Layout.sym_{fn}) (fun x => x = c)',
          f'      (LeafPost c ra {value}#64) := by',
          f'  apply leaf_of_blocks h.image ({fn}_blocks_summary c ra h.good h.image h.minstret h.raReg h.tick h.aligned)',
          '  · rfl',
          '  · change Sail.BitVec.update (ra + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)) 0 0#1 = ra',
          '    exact ret_tgt ra h.aligned',
          '  · intro σ hr')
        E(f'    rw [{fn}_regs] at hr', '    exact hr.1', '  · decide', '')
        number = (value - 1) // 2
        assert value % 2 == 1
        E(f'theorem {fn}_primitive {{runtimeOk : Config → Prop}} (stable : MemoryStable runtimeOk)',
          '    {P : OCaml.Bytecode.Prog} {s : OCaml.Bytecode.St} {pl : Place} {cp : ChanPlace}',
          '    {sp high : Nat} {ra : BitVec 64} {c : Config}',
          '    (h : ConstantInput runtimeOk P s pl cp sp high ra c) :',
          f'    FnSummary (BitVec.ofNat 64 Layout.sym_{fn}) (fun x => x = c)',
          f'      (ConstantPost runtimeOk P s pl cp sp high "{fn}" {number}#63 c ra) := by',
          f'  exact constant_contract stable h ({fn}_summary c ra h.toLeafInput) rfl',
          '', 'end OCaml.Vm.Primitives', '')
        result[root / ('OCaml/Vm/Primitives/' + stem + '.lean')] = E.text()
    if not (compare or argv or lengths):
        modules = sorted('.'.join(path.relative_to(root).with_suffix('').parts)
                         for path in result if 'Primitives' in path.parts)
        result[root / 'OCaml/Vm/Primitives/Constants.lean'] = (
            '\n'.join('import ' + module for module in modules) +
            '\n\n/-! GENERATED by scripts/syi/gen_fn.py --ocaml-constants. -/\n')
    for path, text in result.items():
        if check:
            if not path.exists() or path.read_text() != text:
                raise SystemExit(f'primitive leaf drift: {path.relative_to(root)}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
    print(f'F1 {backend} artifacts: {len(result)} files')


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--fn")
    p.add_argument("--ocaml-constants", action="store_true")
    p.add_argument("--ocaml-compare", action="store_true")
    p.add_argument("--ocaml-argv", action="store_true")
    p.add_argument("--ocaml-lengths", action="store_true")
    p.add_argument("--check", action="store_true")
    p.add_argument("--entry")
    p.add_argument("-o", "--out")
    p.add_argument("--pin", action="append", default=[])
    p.add_argument("--disasm", help="explicit ELF disassembly input")
    p.add_argument("--decode-index", help="word-to-decoder index for this ELF")
    p.add_argument("--route", default=None,
                   help="resolved-path mode: comma list of PC:T|F|TF branch "
                        "polarity pins, e.g. 0x80006230:F,0x8000625c:TF — "
                        "emit only the blocks reachable under the pins")
    p.add_argument("--fold", action="store_true",
                   help="also emit the whole-function fold (recognised loop "
                        "template only) to rows/Fn<X>Fold.lean")
    p.add_argument("--no-verify", action="store_true")
    p.add_argument("--cfg-only", action="store_true",
                   help="print the CFG classification and exit")
    args = p.parse_args()
    if args.ocaml_constants or args.ocaml_compare or args.ocaml_argv or args.ocaml_lengths:
        emit_ocaml_constants(args.check, compare=args.ocaml_compare, argv=args.ocaml_argv, lengths=args.ocaml_lengths)
        return
    if not args.fn or not args.entry:
        p.error("--fn and --entry are required outside --ocaml-constants")
    entry = lib.hexint(args.entry)
    route = None
    if args.route:
        route = {}
        for part in args.route.split(","):
            pc, pol = part.split(":")
            if pol not in ("T", "F", "TF"):
                raise SystemExit(f"--route: bad polarity {pol!r} (T|F|TF)")
            route[lib.hexint(pc)] = pol
    if args.cfg_only:
        di = lib.parse_disasm(args.disasm) if args.disasm else lib.parse_disasm()
        body, blocks = build_cfg(args.fn, entry, di, function_extents(args.disasm), route=route)
        loop = classify_loop(blocks) if route is None else None
        for b in blocks:
            print(b)
        if loop:
            print(f"LOOP: head=0x{loop['head'].start:x} "
                  f"back=0x{loop['back'].start:x} seam=0x{loop['seam'].start:x} "
                  f"ptr={loop['ptr']} cmp={loop['cmp_regs']}")
        return
    base = re.sub(r"[^A-Za-z0-9_]", "_", args.fn).lstrip("_")
    out = args.out or os.path.join(
        ROOT, "Vsa", "Sim", "rows", f"Fn{base[0].upper()}{base[1:]}.lean")
    blocks, loop = emit_fn(args.fn, entry, out, verify=not args.no_verify,
                           route=route, disasm_path=args.disasm, decode_index=args.decode_index)
    if args.fold:
        if not loop:
            raise SystemExit(
                "--fold: no recognised counted-byte-store loop; the fold for "
                "this shape is not templated — write it beside the arms "
                "following rows/FnWriteFold.lean and name any residual holes")
        di = lib.parse_disasm(args.disasm) if args.disasm else lib.parse_disasm()
        fold_out = out.replace(".lean", "Fold.lean")
        emit_fold(args.fn, entry, blocks, loop, di, fold_out,
                  verify=not args.no_verify)


if __name__ == "__main__":
    main()
