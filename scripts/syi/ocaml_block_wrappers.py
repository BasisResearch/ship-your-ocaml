"""Generated effect wrappers (`<block>_fast`) of generated block certificates.

A wrapper turns `<block>_summary` into a `WriteRegistersPost`: the block's
exact store log, target pc, a0 and output registers. Its premises are the
memory windows of the block's accesses, in body order, the image separation
of its stores, the branch condition of its route, and for a return through a
reloaded ra, the saved word. The spec of a block (`fast`) gives

* `mem`: one `(address, mode)` per load/store in body order; mode `'window'`
  makes a window premise, `'global'` discharges a fixed RAM window by
  `decide`, and `'view'` (a load after the block's own stores) reads through
  the store log;
* `log`: the store log, a Lean list of `WEntry` over `R`;
* `taken`: the routed outcome of a branch (its condition becomes the premise
  `ok : guardB op v1 v2 = taken` over the block's output registers);
* `ra`: the load index of a reloaded return address.
"""
import re


def _signed(v, bits):
    return v - (1 << bits) if v >> (bits - 1) else v


def _imm_i(word):
    return _signed(word >> 20, 12)


def _imm_s(word):
    return _signed(((word >> 25) << 5) | ((word >> 7) & 31), 12)


def _branch_target(word, pc):
    imm = (((word >> 31) & 1) << 12) | (((word >> 7) & 1) << 11) | (((word >> 25) & 0x3f) << 5) | (((word >> 8) & 0xf) << 1)
    return pc + _signed(imm, 13)


def _jal_target(word, pc):
    imm = (((word >> 31) & 1) << 20) | (((word >> 12) & 0xff) << 12) | (((word >> 20) & 1) << 11) | (((word >> 21) & 0x3ff) << 1)
    return pc + _signed(imm, 21)


LOADS = {(3, 2): ('lw', 4), (3, 3): ('ld', 8), (3, 4): ('lbu', 1)}
STORES = {(0x23, 0): ('sb', 1), (0x23, 2): ('sw', 4), (0x23, 3): ('sd', 8)}


def _access(i):
    key = (i.word & 0x7f, (i.word >> 12) & 7)
    if key in LOADS:
        return ('load',) + LOADS[key]
    if key in STORES:
        return ('store',) + STORES[key]
    return None


def _writes(instrs):
    out = set()
    for i in instrs:
        if i.word & 0x7f in (0x03, 0x13, 0x1b, 0x17, 0x37, 0x33, 0x3b):
            rd = (i.word >> 7) & 31
            if rd:
                out.add(rd)
    return sorted(out)


def _items(regs):
    """Top-level `(k, expr)` items of a generated register list."""
    body, depth, cur, items = regs.strip()[1:-1], 0, '', []
    for ch in body:
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        if ch == ',' and depth == 0:
            items.append(cur.strip())
            cur = ''
        else:
            cur += ch
    if cur.strip():
        items.append(cur.strip())
    out = {}
    for it in items:
        m = re.match(r'\((\d+),\s*(.*)\)$', it, re.S)
        out[int(m.group(1))] = m.group(2)
    return out


def _imm_facts(instrs):
    """`signExtend` facts of the block's 12-bit immediates."""
    facts = set()
    for i in instrs:
        op = i.word & 0x7f
        if op in (0x03, 0x13, 0x1b):
            raw = (i.word >> 20) & 0xfff
        elif op == 0x23:
            raw = ((i.word >> 25) << 5) | ((i.word >> 7) & 31)
        else:
            continue
        v = _signed(raw, 12)
        rhs = f'-{-v}#64' if v < 0 else f'{v}#64'
        facts.add(f'show BitVec.signExtend 64 {raw}#12 = {rhs} by decide')
    return sorted(facts)


SIMP_ADDR = ('eaddrM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, imm20Of, Functions.sign_extend, '
             'Sail.BitVec.signExtend, BitVec.sub_eq_add_neg')


def emit_fast(E, b, name, regs, fast):
    """`<name>_fast` for one generated block `b` (see the module docstring)."""
    mems = [(i, _access(i)) for i in b.instrs if _access(i)]
    specs = fast.get('mem', [])
    assert len(specs) == len(mems), f'{name}: {len(mems)} accesses, {len(specs)} specs'
    stores = any(a[0] == 'store' for _, a in mems)
    m = 'c.σ.mem'
    viewm = f'(writeLog m ({name}Log R []))'
    assert not (stores and 'loads' in fast['log'] and any(mode == 'view' for _, mode in fast.get('mem', []))), \
        f'{name}: a view load under a load-dependent log'
    loads = [(addr, mode) for (i, a), (addr, mode) in zip(mems, specs) if a[0] == 'load']
    if stores:
        E(f'def {name}Log (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) : List WEntry :=', '  ' + fast['log'], '')
        E(f'theorem {name}_log_eq (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) :',
          f'    (evalBlocks {name}_blocks (SegEvalState.init ({name}_input R) loads)).log = {name}Log R loads := by',
          f'  change [] ++ wlogM {name}_body ({name}_input R) loads = _',
          f'  simp only [List.nil_append, {name}_body, wlogM, {name}_input, wentryM, widthOfM, eaddrM, srcVal, stepGM,',
          '    lookupG, eraseG, stepLdsM, Nat.reduceEqDiff, ite_true, ite_false, Option.getD_some, Nat.reduceAdd, wvalM,',
          '    Functions.sign_extend, Sail.BitVec.signExtend]',
          '  simp only [' + ', '.join(_imm_facts(b.instrs) + ['← BitVec.sub_eq_add_neg', 'BitVec.add_zero']) + ']',
          f'  simp only [{name}Log, List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getD_eq_getElem?_getD]', '')
    E(f'def {name}_loads (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) : List (List (BitVec 8)) :=',
      '  [' + ', '.join(f'read8 {viewm if mode == "view" else "m"} ({addr}).toNat' for addr, mode in loads) + ']', '')
    L = f'({name}_loads {m} R)'
    log = f'{name}Log R {L}' if stores else None
    out = _items(regs)
    assert 10 in out, f'{name}: a wrapper reports a0, so a0 must be among the block registers'
    value = out[10].replace('loads', L)
    # the target pc of the routed outcome
    kind = b.kind
    term = b.term
    if kind in ('jal', 'jalrcall'):
        pc = f'{name}_call.pc'
    elif kind == 'ret':
        pc = 'ra' if 'ra' in fast else 'R 1'
    elif kind == 'fallthrough':
        pc = f'0x{b.instrs[-1].addr + 4:08x}#64'
    elif kind == 'j':
        pc = f'0x{_jal_target(term.word, term.addr):08x}#64'
    else:
        taken = fast.get('taken', False)
        pc = f'0x{(_branch_target(term.word, term.addr) if taken else term.addr + 4):08x}#64'
    params = [f'(h : LeafInput (R 1) c) (regs : GHolds c.σ ({name}_input R))']
    windows, bullets = [], []
    for k, ((i, a), (addr, mode)) in enumerate(zip(mems, specs)):
        w = f'w{k}'
        typ = 'ReadWindow' if a[0] == 'load' else 'WriteWindow'
        if mode == 'global':
            proof = '⟨by decide, by decide, Or.inr (by decide)⟩' if a[0] == 'load' else '⟨by decide, by decide, by decide, by decide⟩'
            windows.append(f'  have {w} : {typ} ({addr}) {a[2]} := {proof}')
        else:
            params.append(f'({w} : {typ} ({addr}) {a[2]})')
        addr_simp = f'      simp [{SIMP_ADDR}, {name}_input]'
        if a[1] == 'ld' and mode == 'view':
            bullets += [f'    · apply {w}.ld rfl', '      · ' + addr_simp.strip(),
                        f'      · apply ArgvTuple.lpins8_of_view (m\' := writeLog c.σ.mem ({name}Log R []))',
                        f'        · simp [stepMemM, wentryM, widthOfM, {SIMP_ADDR}, {name}_input, writeLog, {name}Log]',
                        '        · rfl']
            continue
        assert mode != 'view', f'{name}: view loads must be ld'
        head = {'ld': f'apply {w}.ld rfl ?_ (read8_pins _ _)',
                'lbu': f'apply {w}.lbu rfl ?_ (read8_pins _ _)',
                'lw': f'apply ExitPath.ReadWindow.lw {w} rfl ?_ (ExitPath.read8_pins4 _ _)',
                'sd': f'apply {w}.sd rfl',
                'sb': f'apply {w}.sb rfl',
                'sw': f'apply OCaml.Vm.Primitives.WriteWindow.sw {w} rfl'}[a[1]]
        bullets += ['    · ' + head, addr_simp]
    if stores:
        params.append(f'(outside : ImageOutside ({log}))')
    branch = kind not in ('jal', 'jalrcall', 'ret', 'fallthrough', 'j')
    if branch:
        op = {0: 'BEQ', 1: 'BNE', 4: 'BLT', 5: 'BGE', 6: 'BLTU', 7: 'BGEU'}[(term.word >> 12) & 7]
        val = lambda r: '0#64' if r == 0 else out[r].replace('loads', L)
        rs1, rs2 = (term.word >> 15) & 31, (term.word >> 20) & 31
        params.append(f'(ok : guardB .{op} ({val(rs1)}) ({val(rs2)}) = {"true" if fast.get("taken") else "false"})')
    if 'ra' in fast:
        ra_addr, ra_mode = loads[fast['ra']]
        ra_mem = f'(writeLog {m} ({name}Log R []))' if ra_mode == 'view' else m
        params.append(f'(savedRa : bytesVal .ld (read8 {ra_mem} ({ra_addr}).toNat) = ra) (aligned : ra.toNat % 4 = 0)')
    term_expr = 'none' if kind in ('jal', 'jalrcall', 'fallthrough') else f'some {name}_term'
    writes = _writes(b.instrs)
    E(f'theorem {name}_fast (c : Config)' + (' (ra : BitVec 64)' if 'ra' in fast else '') + ' (R : Nat → BitVec 64)',
      *['    ' + p for p in params[:-1]], '    ' + params[-1] + ' :',
      f'    FnSummary 0x{b.start:08x}#64 (fun d => d = c)',
      f'      (WriteRegistersPost {writes} {"(" + log + ")" if log else "[]"} c ({pc}) ({value}) ({name}_regs R {L})) := by',
      *windows)
    if not b.instrs:
        E(f'  have access : AccessPlan c.σ.mem ({name}_input R) {L} {name}_body := trivial')
    else:
        E(f'  have access : AccessPlan c.σ.mem ({name}_input R) {L} {name}_body := by',
          f'    simp only [AccessPlan, {name}_body, {name}_loads]',
          '    chain_facts True.intro', *bullets)
    if kind == 'ret' and 'ra' in fast:
        control = (f'by rw [{name}_eval]; exact return_facts _ rfl rfl rfl '
                   f'(by simpa [{name}_regs, srcVal, lookupG, {name}_loads] using savedRa) aligned')
    elif kind == 'ret':
        control = f'by rw [{name}_eval]; exact return_facts _ rfl rfl rfl rfl h.aligned'
    elif branch:
        control = f'by rw [{name}_eval]; exact ok'
    else:
        control = 'True.intro'
    E(f'  have control : TermFactsO (runGM {name}_body ({name}_input R) {L}) ({term_expr}) := {control}',
      f'  apply registers_of_blocks h.image ' + ('outside' if stores else '(log := []) ⟨True.intro, True.intro⟩')
      + f' ({name}_summary c (R 1) R _ h regs access control)')
    if stores:
        E(f'  · exact {name}_log_eq R _')
    elif b.instrs:
        E('  · exact readonly_log _ (by unfold ReadOnlyBody; decide) _ _')
    else:
        E('  · rfl')
    if kind == 'ret' and 'ra' in fast:
        E(f'  · change tgtPCT {name}_term (runGM {name}_body ({name}_input R) {L}) = ra',
          f'    rw [{name}_eval]',
          f'    change Sail.BitVec.update (bytesVal .ld ({L}.getD {fast["ra"]} []) + Functions.sign_extend (m := 64) (0#12)) 0 0#1 = ra',
          f'    simp only [{name}_loads, List.getD_cons_zero, List.getD_cons_succ]',
          '    rw [savedRa]', '    exact ret_tgt ra aligned')
    elif kind == 'ret':
        E('  · change Sail.BitVec.update (R 1 + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)) 0 0#1 = R 1',
          '    exact ret_tgt (R 1) h.aligned')
    else:
        E('  · rfl')
    E(f'  · exact {name}_eval R _', '  · rfl', '  · decide', '')


FAST_IMPORTS = ['OCaml.Vm.Primitives.ExitPath.Effects', 'OCaml.Vm.Primitives.ArgvTupleFinished',
                'OCaml.Vm.Primitives.Word32Access']
