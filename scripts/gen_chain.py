#!/usr/bin/env python3
"""Generate chain modules: one straight route through generated `#derive_case` rows.

A chain module states, for each block of the route, its register state (by
`simp`), its write log, its load list and its scalar access plan, then folds
them into a named `Route` structure, a `run` summary over `block_summary`,
and the chain's `log` and `registers`. The register and address shapes come
from a small symbolic evaluation of the block words here; the Lean proofs
check them. Inputs are the generated row modules only.

Usage: scripts/gen_chain.py [--check]
"""
import argparse
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent

ABI = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4',
       'a5', 'a6', 'a7', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4',
       't5', 't6']

# (published module, namespace, doc, [(row module, Seg name, code predicate, pin prefix)])
REF = ('OCaml/Vm/Gc/Generated/ReallocRef.lean', 'Code.Caml_realloc_ref_tableLoaded',
       'Vsa.Sim.Code.caml_realloc_ref_table_at_')
GEN = ('OCaml/Vm/Gc/Generated/Realloc.lean', 'Code.Realloc_generic_table_isra_0Loaded',
       'Vsa.Sim.Code.realloc_generic_table_isra_0_at_')
CHAINS = [
    ('OCaml/Vm/Gc/Generated/ReallocEntry.lean', 'OCaml.Vm.Gc.ReallocEntry',
     '`caml_realloc_ref_table` on an unallocated table (`base == NULL`): the\n'
     'tail jump, the frame saves, and the first size computation up to the\n'
     '`__muldi3` call at `9774`.',
     [(REF, 'caml_realloc_ref_tableXa654Seg'), (GEN, 'realloc_generic_table_isra_0X961cTSeg'),
      (GEN, 'realloc_generic_table_isra_0X9750Seg')], (GEN, 0x80009774)),
    ('OCaml/Vm/Gc/Generated/ReallocAllocCall.lean', 'OCaml.Vm.Gc.ReallocAllocCall',
     'The `caml_stat_alloc_noexc` call at `9778`, right after the size product.',
     [], (GEN, 0x80009778)),
    ('OCaml/Vm/Gc/Generated/ReallocInstall.lean', 'OCaml.Vm.Gc.ReallocInstall',
     'After `caml_stat_alloc_noexc` returns a nonnull block: the old base is\n'
     'NULL (no free), then `base` and `ptr` are installed and the threshold\n'
     'size product is set up for the `__muldi3` call at `97a4`.',
     [(GEN, 'realloc_generic_table_isra_0X977cFSeg'), (GEN, 'realloc_generic_table_isra_0X9784TSeg'),
      (GEN, 'realloc_generic_table_isra_0X9790Seg')], (GEN, 0x800097a4)),
    ('OCaml/Vm/Gc/Generated/ReallocLimit.lean', 'OCaml.Vm.Gc.ReallocLimit',
     'After the threshold product: `threshold` and `limit` are installed and\n'
     'the end product is set up for the `__muldi3` call at `97c0`.',
     [(GEN, 'realloc_generic_table_isra_0X97a8Seg')], (GEN, 0x800097c0)),
    ('OCaml/Vm/Gc/Generated/ReallocReturn.lean', 'OCaml.Vm.Gc.ReallocReturn',
     'After the end product: `end` is installed, the frame restored, and the\n'
     'function returns.',
     [(GEN, 'realloc_generic_table_isra_0X97c4Seg')], None),
]

MOD = ('OCaml/Vm/Gc/Generated/Modify.lean', 'Code.Caml_modifyLoaded', 'Vsa.Sim.Code.caml_modify_at_')


def mod(*segs):
    return [(MOD, f'caml_modifyX{x}Seg') for x in segs]


# caml_modify as a DAG of segments: slot class -> old-value class -> value class -> return.
CHAINS += [
    ('OCaml/Vm/Gc/Generated/BarrierYoung.lean', 'OCaml.Vm.Gc.BarrierYoung',
     '`caml_modify` on a slot in the minor heap: store and return.', mod('a9a8F', 'a9bcF', 'a9c4'), None),
    ('OCaml/Vm/Gc/Generated/BarrierAbove.lean', 'OCaml.Vm.Gc.BarrierAbove',
     '`caml_modify`: the slot is at or above `young_end` (major).', mod('a9a8T'), None),
    ('OCaml/Vm/Gc/Generated/BarrierBelow.lean', 'OCaml.Vm.Gc.BarrierBelow',
     '`caml_modify`: the slot is at or below `young_start` (major).', mod('a9a8F', 'a9bcT'), None),
    ('OCaml/Vm/Gc/Generated/BarrierOldImm.lean', 'OCaml.Vm.Gc.BarrierOldImm',
     'Major slot: frame, store, and the old value is an immediate.', mod('a9ccT'), None),
    ('OCaml/Vm/Gc/Generated/BarrierOldHigh.lean', 'OCaml.Vm.Gc.BarrierOldHigh',
     'Major slot: the old value is a block at or above `young_end`; not marking.',
     mod('a9ccF', 'a9ecT', 'aa00F'), None),
    ('OCaml/Vm/Gc/Generated/BarrierOldLow.lean', 'OCaml.Vm.Gc.BarrierOldLow',
     'Major slot: the old value is a block at or below `young_start`; not marking.',
     mod('a9ccF', 'a9ecF', 'a9f8F', 'aa00F'), None),
    ('OCaml/Vm/Gc/Generated/BarrierOldYoung.lean', 'OCaml.Vm.Gc.BarrierOldYoung',
     'Major slot: the old value is young, so the slot is already remembered.',
     mod('a9ccF', 'a9ecF', 'a9f8T'), None),
    ('OCaml/Vm/Gc/Generated/BarrierValImm.lean', 'OCaml.Vm.Gc.BarrierValImm',
     'The new value is an immediate.', mod('aa0cT'), None),
    ('OCaml/Vm/Gc/Generated/BarrierValHigh.lean', 'OCaml.Vm.Gc.BarrierValHigh',
     'The new value is a block at or above `young_end`.', mod('aa0cF', 'aa14T'), None),
    ('OCaml/Vm/Gc/Generated/BarrierValLow.lean', 'OCaml.Vm.Gc.BarrierValLow',
     'The new value is a block at or below `young_start`.', mod('aa0cF', 'aa14F', 'aa20T'), None),
    ('OCaml/Vm/Gc/Generated/BarrierInsert.lean', 'OCaml.Vm.Gc.BarrierInsert',
     'The new value is young and the remembered set has room: insert.',
     mod('aa0cF', 'aa14F', 'aa20F', 'aa28F', 'aa38'), None),
    ('OCaml/Vm/Gc/Generated/BarrierFull.lean', 'OCaml.Vm.Gc.BarrierFull',
     'The new value is young and the remembered set is full or unallocated: grow it.',
     mod('aa0cF', 'aa14F', 'aa20F', 'aa28T', 'aa7c'), (MOD, 0x8000aa84)),
    ('OCaml/Vm/Gc/Generated/BarrierReload.lean', 'OCaml.Vm.Gc.BarrierReload',
     'After `caml_realloc_ref_table`: reload and insert, then return.', mod('aa88', 'aa38', 'aa44'), None),
    ('OCaml/Vm/Gc/Generated/BarrierReturn.lean', 'OCaml.Vm.Gc.BarrierReturn',
     'Restore `ra` and return.', mod('aa44'), None),
]

SIMP = ('runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, imm20Of, shamtOf, '
        'Functions.sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb, Sail.shift_bits_right, '
        'Sail.shift_bits_left')
ADDR = ('eaddrM, mkLine, decodeM, srcVal, lookupG, eraseG, stepGM, stepLdsM, wvalM, imm20Of, shamtOf, '
        'Functions.sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb, Sail.shift_bits_right, '
        'Sail.shift_bits_left')


def sext(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


class E:
    """A symbolic 64-bit value: a literal or a Lean expression. `exact` is the
    evaluator's own form inside the current block (`mv` leaves `x + 0`), used
    for the block's store log; `text` is the simp-normal form of block states."""
    def __init__(self, text=None, lit=None, atom=True, exact=None):
        self.text, self.lit, self.atom, self.exact = text, lit, atom, exact

    def ex(self):
        return self.exact if self.exact is not None else self.lean()

    def exp(self):
        if self.exact is not None:
            return f'({self.exact})'
        return self.p()

    def lean(self):
        if self.lit is not None:
            return f'0x{self.lit:x}#64'
        return self.text

    def p(self):
        s = self.lean()
        return s if self.atom or self.lit is not None else f'({s})'


def bv(i):
    return f'{i}#64' if i >= 0 else f'-{-i}#64'


def decode(word):
    op, rd, f3 = word & 0x7f, (word >> 7) & 31, (word >> 12) & 7
    rs1, rs2, f7 = (word >> 15) & 31, (word >> 20) & 31, word >> 25
    if op == 0x17:
        return ('auipc', rd, sext(word & 0xfffff000, 32))
    if op == 0x13 and f3 == 0:
        return ('addi', rd, rs1, sext(word >> 20, 12))
    if op == 0x13 and f3 == 1:
        return ('slli', rd, rs1, (word >> 20) & 63)
    if op == 0x13 and f3 == 5 and (word >> 26) == 0:
        return ('srli', rd, rs1, (word >> 20) & 63)
    if op == 0x13 and f3 == 7:
        return ('andi', rd, rs1, sext(word >> 20, 12))
    if op == 0x33 and f3 == 0 and f7 == 0:
        return ('add', rd, rs1, rs2)
    if op == 0x03 and f3 == 3:
        return ('ld', rd, rs1, sext(word >> 20, 12))
    if op == 0x03 and f3 == 2:
        return ('lw', rd, rs1, sext(word >> 20, 12))
    if op == 0x23 and f3 == 3:
        return ('sd', rs2, rs1, sext(((word >> 25) << 5) | ((word >> 7) & 31), 12))
    raise SystemExit(f'gen_chain: unsupported word {word:08x}')


def parse_seg(path, seg):
    text = (ROOT / path).read_text()
    m = re.search(r'#derive_case ' + re.escape(seg) + r' chain\n  \[(.*?)\][^\n]*\n(    terminator ⟨([^⟩]*)⟩)?',
                  text, re.S)
    if not m:
        raise SystemExit(f'gen_chain: no row {seg} in {path}')
    instrs = [(int(pc, 16), int(w, 16)) for pc, w in
              re.findall(r'\((0x[0-9a-f]+)#64, (0x[0-9a-f]+)#32\)', m.group(1))]
    term = None
    if m.group(3):
        fields = [f.strip() for f in m.group(3).split(',')]
        term = dict(pc=int(fields[0].split('#')[0], 16), word=int(fields[1].split('#')[0], 16),
                    kind=fields[6], rs1=int(fields[7]), rs2=int(fields[8]))
    return instrs, term


class Chain:
    def __init__(self, blocks):
        self.blocks = blocks            # [(rowinfo, seg, instrs, term)]
        self.inputs = []                # register numbers, first-read order
        self.loads = 0
        self.stores = 0
        self.kind = {}

    def simulate(self):
        # pre-pass: registers read before written
        written = set()
        for _, _, instrs, term in self.blocks:
            for _, w in instrs:
                d = decode(w)
                reads = {'auipc': [], 'addi': [d[2]] if d[0] == 'addi' else [], }.get(d[0])
                if d[0] in ('addi', 'slli', 'srli', 'andi', 'ld', 'lw'):
                    reads = [d[2]]
                elif d[0] == 'add':
                    reads = [d[2], d[3]]
                elif d[0] == 'sd':
                    reads = [d[1], d[2]]
                else:
                    reads = []
                for r in reads:
                    if r and r not in written and r not in self.inputs:
                        self.inputs.append(r)
                if d[0] != 'sd' and d[1]:
                    written.add(d[1])
            if term:
                for r in ([term['rs1'], term['rs2']] if term['kind'].startswith('.br') else
                          [term['rs1']] if term['kind'] == '.jr' else []):
                    if r and r not in written and r not in self.inputs:
                        self.inputs.append(r)
        self.written = sorted(written)
        state = [(r, E(ABI[r])) for r in self.inputs]
        self.states = [list(state)]
        self.per = []   # per-block: dict(loads=[k], ops=[...], log=[(addr,val)])
        k = 0
        for _, _, instrs, term in self.blocks:
            ops, log, loads = [], [], []
            for pc, w in instrs:
                d = decode(w)

                def val(r):
                    if r == 0:
                        return E(lit=0)
                    for q, e in state:
                        if q == r:
                            return e
                    raise SystemExit(f'gen_chain: x{r} unknown at {pc:x}')

                def put(r, e):
                    nonlocal state
                    if r:
                        state = [(r, e)] + [(q, x) for q, x in state if q != r]
                kind = d[0]
                if kind == 'auipc':
                    put(d[1], E(lit=(pc + d[2]) % 2**64))
                    ops.append(('alu',))
                elif kind == 'addi':
                    s = val(d[2])
                    if s.lit is not None:
                        put(d[1], E(lit=(s.lit + d[3]) % 2**64))
                    elif d[3] == 0:
                        put(d[1], E(s.text, atom=s.atom, exact=f'{s.exp()} + BitVec.ofNat 64 0'))
                    else:
                        put(d[1], E(f'{s.p()} + {bv(d[3])}', atom=False))
                    ops.append(('alu',))
                elif kind == 'andi':
                    s = val(d[2])
                    put(d[1], E(f'{s.p()} &&& {bv(d[3])}', atom=False))
                    ops.append(('alu',))
                elif kind in ('slli', 'srli'):
                    s = val(d[2])
                    sym = '<<<' if kind == 'slli' else '>>>'
                    put(d[1], E(f'{s.p()} {sym} {d[3]}', atom=False))
                    ops.append(('alu',))
                elif kind == 'add':
                    a, b = val(d[2]), val(d[3])
                    if a.lit is not None and b.lit is not None:
                        put(d[1], E(lit=(a.lit + b.lit) % 2**64))
                    else:
                        put(d[1], E(f'{a.p()} + {b.p()}', atom=False))
                    ops.append(('alu',))
                elif kind in ('ld', 'sd', 'lw'):
                    base = val(d[2])
                    if base.lit is not None:
                        addr = E(lit=(base.lit + d[3]) % 2**64)
                    elif d[3] >= 0:
                        addr = E(f'{base.exp()} + BitVec.ofNat 64 {d[3]}', atom=False)
                    else:
                        raise SystemExit(f'gen_chain: negative offset at {pc:x}')
                    if kind in ('ld', 'lw'):
                        k += 1
                        loads.append(k)
                        ops.append((kind, k, addr))
                        self.kind[k] = kind
                        put(d[1], E(f'v{k}'))
                    else:
                        self.stores += 1
                        v = val(d[1])
                        entry = (addr, E(v.ex(), lit=v.lit, atom=v.atom and v.exact is None))
                        log.append(entry)
                        ops.append(('sd', self.stores, addr))
            state = [(q, E(x.text, lit=x.lit, atom=x.atom)) for q, x in state]
            self.per.append(dict(loads=loads, ops=ops, log=log, term=term,
                                 before=list(self.states[-1])))
            # register state with load values as variables v_k
            self.states.append(list(state))
        self.loads = k


LOADKIND = {}


def bval(j):
    """The value of the j-th load of the current chain."""
    return f'(bytesVal .{LOADKIND[j]} b{j})'


def bindv(t):
    return re.sub(r'\bv(\d+)\b', lambda m: bval(int(m.group(1))), t)


def localize(t, first):
    """Within block lemmas, loads of the block itself are byte lists `b_k`."""
    return re.sub(r'\bv(\d+)\b', lambda m: m.group(0) if int(m.group(1)) < first
                  else bval(int(m.group(1))), t)


def regs_text(state):
    return '[' + ', '.join(f'({r}, {e.lean()})' for r, e in state) + ']'


def emit(module, ns, doc, spec, decode_modules):
    blocks = []
    for (path, pred, prefix), seg in spec:
        instrs, term = parse_seg(path, seg)
        blocks.append(((path, pred, prefix), seg, instrs, term))
    ch = Chain(blocks)
    ch.simulate()
    LOADKIND.clear()
    LOADKIND.update(ch.kind)
    n = len(blocks)
    inputs = [ABI[r] for r in ch.inputs]
    inp = ' '.join(inputs)
    words = set()
    for _, _, instrs, term in blocks:
        words |= {f'{w:08x}' for _, w in instrs}
        if term:
            words.add(f'{term["word"]:08x}')
    rows = sorted({p[0] for p, _, _, _ in blocks})
    imports = ['import ' + r[:-5].replace('/', '.') for r in rows]
    imports += ['import OCaml.Vm.Gc.ChainGen', 'import OCaml.Vm.Gc.ChainPlan', 'import OCaml.Vm.Primitives.Blocks',
                'import Vsa.Sim.ChainFactsTac', 'import Vsa.Sim.Muldi3Spec']
    imports += ['import ' + m for m in sorted({decode_modules[w] for w in words})]
    seg_names = [seg for _, seg, _, _ in blocks]
    entry = blocks[0][2][0][0] if blocks[0][2] else blocks[0][3]['pc']
    L = []
    E_ = L.append
    E_('\n'.join(imports))
    E_('')
    E_(f'/-! GENERATED by scripts/gen_chain.py. {doc} -/')
    E_('')
    E_('set_option maxRecDepth 100000')
    E_('set_option linter.unusedVariables false')
    E_('')
    E_(f'namespace {ns}')
    E_('open Vsa.Sim Vsa.Machine OCaml.Vm.Primitives OCaml.Vm.Gc LeanRV64DExecutable')
    E_('')
    for i, seg in enumerate(seg_names):
        E_(f'def block{i} : BBlock := {seg}.getD 0 {{ body := [], term := none }}')
    E_('def blocks := [' + ', '.join(f'block{i}' for i in range(n)) + ']')
    E_(f'def pc : BitVec 64 := 0x{entry:x}#64')
    E_('')
    vs = lambda k: ' '.join(f'v{j}' for j in range(1, k + 1))
    bs = lambda lo, hi: ' '.join(f'b{j}' for j in range(lo, hi + 1))
    vals = lambda lo, hi: ' '.join(bval(j) for j in range(lo, hi + 1))
    # state definitions
    loaded = [0]
    for i in range(n):
        loaded.append(loaded[-1] + len(ch.per[i]['loads']))
    for i in range(n + 1):
        args = (inp + ' ' + vs(loaded[i])).strip()
        E_(f'def state{i} ({args} : BitVec 64) : GRegs := {regs_text(ch.states[i])}')
    E_('')
    E_(f'def regs ({inp} : BitVec 64) : GRegs := state0 {inp}')
    keys = [r for r, _ in ch.states[0]]
    E_(f'theorem chain_ok : ChainOK pc {keys} blocks := by decide')
    E_('')
    # code facts
    preds = []
    for (path, pred, prefix), _, _, _ in blocks:
        if pred not in preds:
            preds.append(pred)
    pname = {p: f'code{j}' for j, p in enumerate(preds)}
    E_('theorem code_facts {mem : Std.ExtHashMap Nat (BitVec 8)} ' +
       ' '.join(f'({pname[p]} : {p} mem)' for p in preds) + ' :\n    ChainCode mem blocks := by')
    E_('  intro b member')
    E_('  simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at member')
    E_('  rcases member with ' + ' | '.join(['rfl'] * n))
    for i, ((path, pred, prefix), seg, _, _) in enumerate(blocks):
        E_(f'  · constructor')
        E_(f'    all_goals simp only [block{i}, {seg}, List.getD_cons_zero, CodeFacts]')
        E_(f'    all_goals chain_facts {pname[pred]} with "{prefix}"')
    E_('')
    # per block lemmas
    stored = []  # memory def name per block start
    for i in range(n):
        per = ch.per[i]
        lo, hi = loaded[i] + 1, loaded[i + 1]
        sargs = (inp + ' ' + vs(loaded[i])).strip()
        st = f'state{i} {sargs}'
        nxt_args = (inp + ' ' + ' '.join(f'v{j}' for j in range(1, loaded[i] + 1)) + ' ' + vals(lo, hi)).strip()
        ldsl = ''.join(f'b{j}::' for j in range(lo, hi + 1)) + 'lds'
        bvars = f' ({bs(lo, hi)} : List (BitVec 8))' if hi >= lo else ''
        hdr = f'({sargs} : BitVec 64){bvars} (lds : List (List (BitVec 8)))'
        E_(f'theorem block{i}_regs {hdr} :')
        E_(f'    runGM block{i}.body ({st}) ({ldsl}) = state{i+1} {nxt_args} := by')
        E_(f'  simp [block{i}, {seg_names[i]}, state{i}, state{i+1}, {SIMP}]')
        E_(f'theorem block{i}_loads{bvars} (lds : List (List (BitVec 8))) :')
        E_(f'    ldsRunM block{i}.body ({ldsl}) = lds := rfl')
        logt = localize('[' + ', '.join(f'(({a.lean()}).toNat, 8, {v.lean()})' for a, v in per['log']) + ']', lo)
        E_(f'theorem block{i}_log {hdr} :')
        E_(f'    wlogM block{i}.body ({st}) ({ldsl}) = {logt} := by')
        E_('  rfl')
        # access
        prem = []
        script = []
        stores_in_block = []
        for idx, op in enumerate(per['ops']):
            if op[0] in ('ld', 'lw'):
                k, addr = op[1], localize(op[2].lean(), lo)
                w, P = (8, 'LPins8') if op[0] == 'ld' else (4, 'LPins4')
                prem.append(f'(read{k} : ReadWindow ({addr}) {w})')
                prem.append(f'(pins{k} : {P} mem ({addr}).toNat b{k})')
                for j, saddr in stores_in_block:
                    prem.append(f'(apart{k}_{j} : ({addr}).toNat + {w} ≤ ({saddr}).toNat ∨ '
                                f'({saddr}).toNat + 8 ≤ ({addr}).toNat)')
                lines = [f'  · apply read{k}.{op[0]} rfl (by first | rfl | simp [{ADDR}, state{i}])']
                lp = 'lpins8' if op[0] == 'ld' else 'lpins4'
                for prev in reversed(per['ops'][:idx]):
                    if prev[0] == 'sd':
                        lines.append(f'    refine {lp}_stepMemM_apart rfl (by first | rfl | simp [{ADDR}, state{i}]) ?_ apart{k}_{prev[1]}')
                    else:
                        lines.append(f'    apply {lp}_stepMemM_keep rfl')
                lines.append(f'    exact pins{k}')
                script += lines
            elif op[0] == 'sd':
                j, addr = op[1], localize(op[2].lean(), lo)
                prem.append(f'(write{j} : WriteWindow ({addr}) 8)')
                script.append(f'  · exact write{j}.sd rfl (by first | rfl | simp [{ADDR}, state{i}])')
                stores_in_block.append((j, addr))
        E_(f'theorem block{i}_access (mem : Std.ExtHashMap Nat (BitVec 8)) {hdr}' +
           ''.join('\n    ' + p for p in prem) + ' :')
        E_(f'    AccessPlan mem ({st}) ({ldsl}) block{i}.body := by')
        E_(f'  simp only [block{i}, {seg_names[i]}, List.getD_cons_zero, AccessPlan]')
        E_(f'  chain_facts True.intro')
        L.extend(script)
        # control
        term = per['term']
        nstate = ch.states[i + 1]

        def rv(r):
            if r == 0:
                return E(lit=0)
            for q, e in nstate:
                if q == r:
                    return e
        if term is None or term['kind'] == '.j':
            E_(f'theorem block{i}_control {hdr} :')
            E_(f'    TermFactsO (runGM block{i}.body ({st}) ({ldsl})) block{i}.term := by')
            E_(f'  simp [block{i}, {seg_names[i]}, TermFactsO, TermFactsT]')
            per['control'] = None
        elif term['kind'].startswith('.br'):
            _, op, taken = term['kind'].split()
            a, b = rv(term['rs1']).lean(), rv(term['rs2']).lean()
            t = taken == 'true'
            if op in ('bop.BEQ', 'bop.BNE'):
                eq = (op == 'bop.BEQ') == t
                cond = f'{a} = {b}' if eq else f'{a} ≠ {b}'
                tac = 'simpa'
            elif op in ('bop.BGEU', 'bop.BLTU'):
                ge = (op == 'bop.BGEU') == t
                cond = f'({b}).toNat ≤ ({a}).toNat' if ge else f'({a}).toNat < ({b}).toNat'
                tac = 'omega'
            else:
                raise SystemExit(f'gen_chain: branch {op}')
            per['control'] = cond
            E_(f'theorem block{i}_control {hdr} (control : {localize(cond, lo)}) :')
            E_(f'    TermFactsO (runGM block{i}.body ({st}) ({ldsl})) block{i}.term := by')
            E_(f'  rw [block{i}_regs]')
            simps = (f'block{i}, {seg_names[i]}, TermFactsO, TermFactsT, state{i+1}, srcVal, lookupG, guardB, '
                     'Functions.zopz0zKzJ_u, Functions.zopz0zI_u, Sail.BitVec.toNatInt')
            if tac == 'simpa':
                E_(f'  simpa [block{i}, {seg_names[i]}, TermFactsO, TermFactsT, state{i+1}, srcVal, lookupG, guardB] using control')
            else:
                E_(f'  simp [{simps}]')
                E_('  omega')
        elif term['kind'] == '.jr':
            per['control'] = f'({rv(term["rs1"]).lean()}).toNat % 4 = 0'
            per['target'] = rv(term['rs1']).lean()
            target = localize(rv(term['rs1']).lean(), lo)
            E_(f'theorem block{i}_control {hdr} (control : ({target}).toNat % 4 = 0) :')
            E_(f'    TermFactsO (runGM block{i}.body ({st}) ({ldsl})) block{i}.term := by')
            E_(f'  rw [block{i}_regs]')
            E_(f'  change (Sail.BitVec.update (srcVal {term["rs1"]} (state{i+1} {nxt_args}) +')
            E_(f'    Functions.sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0')
            E_(f'  rw [show srcVal {term["rs1"]} (state{i+1} {nxt_args}) = {target} from rfl, ret_tgt _ control]')
            E_(f'  exact control')
        E_('')
    return L, ch, loaded, inputs, n


def emit_fold(L, ch, loaded, inputs, n):
    E_ = L.append
    inp = ' '.join(inputs)
    K = ch.loads
    ball = ' '.join(f'b{j}' for j in range(1, K + 1))
    vals_all = lambda hi: ' '.join(bval(j) for j in range(1, hi + 1))
    E_('/-! ### The chain -/')
    E_('')
    E_('theorem writeLog_nil\' (m : Std.ExtHashMap Nat (BitVec 8)) : writeLog m [] = m := rfl')
    E_('')
    lst = '[' + ', '.join(f'b{j}' for j in range(1, K + 1)) + ']'
    bdecl = f' ({ball} : List (BitVec 8))' if K else ''
    E_(f'def loads{bdecl} : List (List (BitVec 8)) := {lst}')
    # memory before each block
    for i in range(n + 1):
        args = (inp + ' ' + vals_all(loaded[i])).strip()
        if i == 0:
            E_(f'def mem0 (mem : Std.ExtHashMap Nat (BitVec 8)){bdecl} ({inp} : BitVec 64) :'
               ' Std.ExtHashMap Nat (BitVec 8) := mem')
            continue
        per = ch.per[i - 1]
        sub = lambda s: s
        logt = '[' + ', '.join(f'(({a.lean()}).toNat, 8, {v.lean()})' for a, v in per['log']) + ']'
        # replace load variables v_j by their byte values
        bind = bindv
        E_(f'def mem{i} (mem : Std.ExtHashMap Nat (BitVec 8)){bdecl} ({inp} : BitVec 64) :'
           f' Std.ExtHashMap Nat (BitVec 8) :=')
        if per['log']:
            E_(f'  writeLog (mem{i-1} mem {ball} {inp}) {bind(logt)}')
        else:
            E_(f'  mem{i-1} mem {ball} {inp}')
    E_('')

    bind = bindv
    # Route
    E_('/-- The route\'s scalar observations: each load\'s window and byte pins at its')
    E_('block-start memory, each store\'s window, and each branch choice. -/')
    E_(f'structure Route (mem : Std.ExtHashMap Nat (BitVec 8)) ({inp} : BitVec 64){bdecl} : Prop where')
    fields = {}
    for i in range(n):
        per = ch.per[i]
        memi = f'(mem{i} mem {ball} {inp})'
        stores = []
        for op in per['ops']:
            if op[0] in ('ld', 'lw'):
                k, a = op[1], bind(op[2].lean())
                w, P = (8, 'LPins8') if op[0] == 'ld' else (4, 'LPins4')
                E_(f'  read{k} : ReadWindow ({a}) {w}')
                E_(f'  pins{k} : {P} {memi} ({a}).toNat b{k}')
                for j, sa in stores:
                    E_(f'  apart{k}_{j} : ({a}).toNat + {w} ≤ ({sa}).toNat ∨ ({sa}).toNat + 8 ≤ ({a}).toNat')
            elif op[0] == 'sd':
                j, a = op[1], bind(op[2].lean())
                E_(f'  write{j} : WriteWindow ({a}) 8')
                stores.append((j, a))
        if per['control']:
            E_(f'  control{i} : {bind(per["control"])}')
    E_('')
    # access
    E_(f'theorem access {{mem : Std.ExtHashMap Nat (BitVec 8)}} {{{inp} : BitVec 64}}'
       + (f' {{{ball} : List (BitVec 8)}}' if K else '') +
       f'\n    (r : Route mem {inp} {ball}) : ChainAccess mem (regs {inp}) (loads {ball}) blocks := by')
    E_('  simp only [loads, regs]')
    for i in range(n):
        per = ch.per[i]
        lo, hi = loaded[i] + 1, loaded[i + 1]
        sargs = (inp + ' ' + vals_all(loaded[i])).strip()
        bl = ' '.join(f'b{j}' for j in range(lo, hi + 1))
        args = []
        stores = []
        for op in per['ops']:
            if op[0] in ('ld', 'lw'):
                args += [f'r.read{op[1]}', f'r.pins{op[1]}'] + [f'r.apart{op[1]}_{j}' for j in stores]
            elif op[0] == 'sd':
                args.append(f'r.write{op[1]}')
                stores.append(op[1])
        ctrl = f' r.control{i}' if per['control'] else ''
        tail = '_'
        E_(f'  apply ChainAccess.cons ⟨block{i}_access (mem{i} mem {ball} {inp}) {sargs} {bl} {tail} {" ".join(args)},')
        E_(f'    block{i}_control {sargs} {bl} {tail}{ctrl}⟩')
        if not per['log']:
            E_(f'  rw [block{i}_log, block{i}_regs, block{i}_loads, writeLog_nil\']')
        else:
            E_(f'  rw [block{i}_log, block{i}_regs, block{i}_loads]')
        if i + 1 < n:
            E_(f'  change ChainAccess (mem{i+1} mem {ball} {inp}) _ _ _')
    E_('  exact ChainAccess.nil')
    E_('')
    # Input / run
    E_(f'structure Input ({inp} : BitVec 64){bdecl} (c : Config) : Prop where')
    E_('  good : GoodState c.σ')
    E_('  tick : c.tick < 2')
    E_('  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w')
    return fields


def finish(L, ch, loaded, inputs, n, preds):
    E_ = L.append
    inp = ' '.join(inputs)
    K = ch.loads
    ball = ' '.join(f'b{j}' for j in range(1, K + 1))
    bdecl = f' {{{ball} : List (BitVec 8)}}' if K else ''
    for j, p in enumerate(preds):
        E_(f'  code{j} : {p} c.σ.mem')
    E_(f'  registers : GHolds c.σ (regs {inp})')
    E_(f'  route : Route c.σ.mem {inp} {ball}')
    E_('')
    keys = [r for r, _ in ch.states[0]]
    codes = ' '.join(f'input.code{j}' for j in range(len(preds)))
    E_(f'/-- **The chain run.** -/')
    E_(f'theorem run {{{inp} : BitVec 64}}{bdecl} {{c : Config}} (input : Input {inp} {ball} c) :')
    E_(f'    FnSummary pc (fun d => d = c) (BlockPost blocks pc (regs {inp}) (loads {ball}) c) :=')
    E_(f'  block_summary blocks pc _ _ c')
    E_(f'    ⟨input.good, input.minstret, input.registers, by change KeysOK {keys}; decide,')
    E_(f'      chainPlan_facts (code_facts {codes}) (access input.route), chain_ok, input.tick⟩')
    E_('')
    vals_all = ' '.join(bval(j) for j in range(1, K + 1))
    biv = (f' ({ball} : List (BitVec 8))' if K else '')
    lemmas = ', '.join(f'block{i}_regs, block{i}_loads, block{i}_log' for i in range(n))
    full = []
    for i in range(n):
        for a, v in ch.per[i]['log']:
            full.append(f'(({a.lean()}).toNat, 8, {v.lean()})')
    fl = bindv('[' + ', '.join(full) + ']')
    E_(f'theorem log ({inp} : BitVec 64){biv} :')
    E_(f'    (evalBlocks blocks (SegEvalState.init (regs {inp}) (loads {ball}))).log =')
    E_(f'      {fl} := by')
    E_(f'  simp only [blocks, loads, regs, evalBlocks, evalBlock, SegEvalState.init, {lemmas},')
    E_(f'    List.nil_append, List.cons_append, List.append_nil]')
    E_(f'theorem registers ({inp} : BitVec 64){biv} :')
    E_(f'    (evalBlocks blocks (SegEvalState.init (regs {inp}) (loads {ball}))).regs =')
    E_(f'      state{n} {inp} {vals_all} := by')
    E_(f'  simp only [blocks, loads, regs, evalBlocks, evalBlock, SegEvalState.init, {lemmas}]')
    endpc = None
    E_(f'theorem written : ∀ n ∈ wrChain blocks, n ∈ {ch.written} := by decide')
    E_('')


def call_text(call, decode_modules):
    """The direct call a chain parks at: instruction data, shape, decode, pins."""
    (path, pred, prefix), pc = call
    fn = prefix.split('Vsa.Sim.Code.')[1][:-len('_at_')]
    pinfile = ROOT / ('Vsa/Sim/Code/' + pred.split('.')[1][:-len('Loaded')] + '.lean')
    m = re.search(r'theorem ' + re.escape(f'{fn}_at_{pc:x}') + r' .*?\n(.*?):=', pinfile.read_text(), re.S)
    bs = [int(b, 16) for b in re.findall(r'some \((0x[0-9a-f]+) : BitVec 8\)', m.group(1))]
    word = bs[0] | bs[1] << 8 | bs[2] << 16 | bs[3] << 24
    assert word & 0xfff == 0x0ef, f'not jal ra at {pc:x}'
    imm = (((word >> 31) & 1) << 20) | (((word >> 12) & 0xff) << 12) | (((word >> 20) & 1) << 11) | \
        (((word >> 21) & 0x3ff) << 1)
    target = (pc + sext(imm, 21)) % 2**64
    w = f'{word:08x}'
    return [
        f'def call : CallInstr := ⟨0x{pc:x}#64, 0x{w}#32, ' + ', '.join(f'0x{b:02x}#8' for b in bs) + f', 0x{imm:x}#21⟩',
        'theorem call_shape : CallShape call := by constructor <;> decide',
        'theorem call_decode : CallDecode call := by',
        '  intro s hm hp he',
        f'  exact Vsa.Sim.ElfDecode.decode_{w} s hm hp he',
        f'theorem call_target : call.target = 0x{target:x}#64 := by decide',
        f'theorem call_link : call.link = 0x{(pc + 4) % 2**64:x}#64 := by decide',
        f'theorem call_pins {{c : Config}} (h : {pred} c.σ.mem) : CallPins call c := by',
        f'  obtain ⟨h0, h1, h2, h3⟩ := Code.{fn}_at_{pc:x} h',
        '  exact ⟨h0, h1, h2, h3⟩',
        '',
    ], decode_modules[w]


def generate():
    decodes = {}
    for p in sorted((ROOT / 'Vsa/Sim/ElfDecode').glob('Part*.lean')):
        for w in re.findall(r'^theorem decode_([0-9a-f]{8})', p.read_text(), re.M):
            decodes[w] = 'Vsa.Sim.ElfDecode.' + p.stem
    out = {}
    for module, ns, doc, spec, call in CHAINS:
        if not spec:
            text, dm = call_text(call, decodes)
            L = [f'import {call[0][0][:-5].replace("/", ".")}', 'import OCaml.Vm.Primitives.Call', f'import {dm}', '',
                 f'/-! GENERATED by scripts/gen_chain.py. {doc} -/', '', f'namespace {ns}',
                 'open Vsa.Sim Vsa.Machine OCaml.Vm.Primitives LeanRV64DExecutable', ''] + text
            L.append(f'end {ns}')
            out[ROOT / module] = '\n'.join(L) + '\n'
            continue
        L, ch, loaded, inputs, n = emit(module, ns, doc, spec, decodes)
        emit_fold(L, ch, loaded, inputs, n)
        preds = []
        for (path, pred, prefix), _ in spec:
            if pred not in preds:
                preds.append(pred)
        finish(L, ch, loaded, inputs, n, preds)
        last = ch.per[-1]
        inp = ' '.join(inputs)
        K = ch.loads
        bl = ' '.join(f'b{j}' for j in range(1, K + 1))
        if call is None and 'target' in last:
            vals = ' '.join(bval(j) for j in range(1, K + 1))
            target = bindv(last['target'])
            rs1 = last['term']['rs1']
            inner = f'(state0 {inp})'
            for i in range(n):
                rem = [f'b{j}' for j in range(loaded[i] + 1, K + 1)]
                inner = f'(runGM block{i}.body {inner} [{", ".join(rem)}])'
            L.extend([
                '/-- The `ret` target. -/',
                f'theorem endpoint ({inp} : BitVec 64){f" ({bl} : List (BitVec 8))" if K else ""} (control : ({target}).toNat % 4 = 0) :',
                f'    evalBlocksPC pc (SegEvalState.init (regs {inp}) (loads {bl})) blocks = {target} := by',
                f'  change Sail.BitVec.update (srcVal {rs1} {inner} +',
                '    Functions.sign_extend (m := 64) (0#12)) 0 0#1 = _',
                f'  rw [{", ".join(f"block{i}_regs" for i in range(n))}]',
                f'  rw [show srcVal {rs1} (state{n} {inp} {vals}) = {target} from rfl, ret_tgt _ control]',
                ''])
        elif call is None:
            (path, _, _), seg = spec[-1]
            base = seg[:-len('Seg')]
            m = re.search(r'The `' + re.escape(base) + r'` row post: parked at the computed end PC `(0x[0-9a-f]+)#64`',
                          (ROOT / path).read_text())
            L.extend([
                '/-- Where the chain falls through. -/',
                f'theorem endpoint ({inp} : BitVec 64) (lds : List (List (BitVec 8))) :',
                f'    evalBlocksPC pc (SegEvalState.init (regs {inp}) lds) blocks = {m.group(1)}#64 := rfl',
                ''])
        if call:
            text, dm = call_text(call, decodes)
            L[0] += '\nimport OCaml.Vm.Primitives.Call\nimport ' + dm
            inp = ' '.join(inputs)
            K = ch.loads
            lds = ' '.join(f'b{j}' for j in range(1, K + 1))
            L.extend(text)
            L.append(f'theorem endpoint ({inp} : BitVec 64) (lds : List (List (BitVec 8))) :')
            L.append(f'    evalBlocksPC pc (SegEvalState.init (regs {inp}) lds) blocks = call.pc := rfl')
            L.append('')
        L.append(f'end {ns}')
        out[ROOT / module] = '\n'.join(L) + '\n'
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    out = generate()
    bad = []
    for path, text in out.items():
        if args.check:
            if not path.exists() or path.read_text() != text:
                bad.append(path)
        else:
            path.write_text(text)
            print(path.relative_to(ROOT))
    if bad:
        for p in bad:
            print(f'drift: {p.relative_to(ROOT)}')
        sys.exit(1)


if __name__ == '__main__':
    main()
