#!/usr/bin/env python3
"""Generate the F1 arm table (OCaml/Vm/Sim/F1Table.lean) from the row theorems.

Every F1 opcode's row is a theorem `<op>_row ... : OCaml.OpArm P (OCaml.LoopAt L P) .<OP>`
somewhere under OCaml/. This script finds each row, reads its parameters, and
emits:

* `F1Premises P`: the program-level premises the rows name (types copied from
  the row signatures, specialised to the pinned layout and budget), plus one
  field per F1 opcode that has no row yet;
* `f1_table`: `F1Arms P c (LoopAt Gc.f1Layout P)` from `Loaded`, `GoodF1`,
  `Fits` and `F1Premises`, dispatching every opcode to its row.

`--check` fails on drift (check_all stage a5).
"""
import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'OCaml/Vm/Sim/F1Table.lean'
WHILEMIN = ROOT / 'OCaml/Vm/Sim/WhileMinTable.lean'

# Premise fields already proved for whileMin (one shape run, WhileMinShape.lean).
WHILEMIN_KNOWN = {
    'extra': 'OCaml.Programs.whileMin_extraBounded',
    'values': 'OCaml.Programs.whileMin_valuesInRange',
    'trapBounded': 'OCaml.Programs.whileMin_trapBounded.bounded',
    'ints': 'OCaml.Programs.whileMin_branchInts',
    'divint_zero': 'DivisorsNonzero.zero OCaml.Programs.whileMin_divisorsNonzero (.inl rfl)',
    'modint_zero': 'DivisorsNonzero.zero OCaml.Programs.whileMin_divisorsNonzero (.inr rfl)',
    'closure_sizes': 'OCaml.Programs.whileMin_closureSizes',
    'makeblock_sizes': 'OCaml.Programs.whileMin_blockSizes',
    'c_call1_effects': 'CcallEffects.of_ok OCaml.Programs.whileMin_ccall1Ok',
    'c_call2_effects': 'CcallEffects.of_ok OCaml.Programs.whileMin_ccall2Ok',
    'c_call3_effects': 'CcallEffects.of_ok OCaml.Programs.whileMin_ccall3Ok',
    'c_call4_effects': 'CcallEffects.of_ok OCaml.Programs.whileMin_ccall4Ok',
    'c_call5_effects': 'CcallEffects.of_ok OCaml.Programs.whileMin_ccall5Ok',
}

NON_F1 = set('MAKEFLOATBLOCK GETFLOATFIELD SETFLOATFIELD VECTLENGTH GETVECTITEM SETVECTITEM '
             'GETBYTESCHAR SETBYTESCHAR GETSTRINGCHAR C_CALLN GETMETHOD GETPUBMET GETDYNMET '
             'EVENT BREAK'.split())

# Layout-level parameters: proved once for the pinned layout and budget.
FIXED = {
    'stable': 'f1_memoryStable',
    'rf': 'f1_runtimeFrame',
    'allocFrame': 'f1_allocFrame',
    'field': ('(fun s c reach h => f1_fieldWriteReady h.running.platform.runtime'
              ' (by simpa using stack_fits fits g1_capacity reach (k := 0)))'),
    'budgetSmall': 'f1_budgetSmall',
    'fits': 'fits',
    'capacity': 'g1_capacity',
    'good': 'good',
}
# Program-level parameters shared by several rows: one premise field each.
SHARED = {'values': 'values', 'ints': 'ints', 'extra': 'extra', 'extraBounded': 'extra', 'exotic': 'exotic', 'trapBounded': 'trapBounded',
          'scratch': 'scratch', 'field': 'field'}
SUBST = [(r'\bL\b', 'Gc.f1Layout'), (r'\bB\b', 'Gc.g1Budget'),
         (r'\bhigh0\b', 'Gc.f1High'), (r'\bdom0\b', 'Gc.f1Domain')]


def opcodes():
    text = (ROOT / 'OCaml/Bytecode/Opcode.lean').read_text()
    ops = re.findall(r'^\s*\|\s*([A-Z_0-9]+)\s*$', text, re.M)
    return list(dict.fromkeys(ops))


def params(sig):
    """Explicit `(name : type)` binders of a signature, with balanced parens."""
    out, i = [], 0
    while True:
        j = sig.find('(', i)
        if j < 0:
            return out
        depth, k = 0, j
        while True:
            if sig[k] == '(':
                depth += 1
            elif sig[k] == ')':
                depth -= 1
                if depth == 0:
                    break
            k += 1
        body = sig[j + 1:k]
        m = re.match(r'(\w+) : (.*)$', body, re.S)
        if m:
            out.append((m.group(1), ' '.join(m.group(2).split())))
        i = k + 1


def rows():
    found = {}
    for f in sorted((ROOT / 'OCaml').rglob('*.lean')):
        if f == OUT:
            continue
        text = f.read_text()
        for m in re.finditer(r'^theorem ([A-Za-z0-9_.]+)((?:(?!^theorem).)*?)'
                             r'OCaml\.OpArm P \(OCaml\.LoopAt L P\) \.([A-Z_0-9]+)', text, re.M | re.S):
            name, sig, op = m.groups()
            if name.endswith('_row') and op not in found:
                mod = str(f.relative_to(ROOT))[:-5].replace('/', '.')
                found[op] = (name, params(sig), mod)
    return found


def spec(ty):
    for a, b in SUBST:
        ty = re.sub(a, b, ty)
    return ty


def whilemin_ops():
    text = (ROOT / 'OCaml/Programs/WhileMinShape.lean').read_text()
    m = re.search(r'def whileMinOps : List Opcode :=\s*\[(.*?)\]', text, re.S)
    return re.findall(r'\.([A-Z_0-9]+)', m.group(1))


def render_whilemin(fields, users):
    ops = set(whilemin_ops())
    known, open_, fill = {}, {}, []
    for fname, ty in fields.items():
        if not (set(users[fname]) & ops):
            fill.append(f'  {fname} h := absurd h (by decide)')
        elif fname in WHILEMIN_KNOWN:
            fill.append(f'  {fname} _ := {WHILEMIN_KNOWN[fname]}')
        elif re.fullmatch(r'c_call\d_returns', fname):
            m = re.fullmatch(r'CcallReturns Gc\.f1Layout P (\.C_CALL\d) (\S+) (\d+)', ty)
            prims = fname.replace('_returns', '_prims')
            open_[prims] = (f'∀ name ∈ OCaml.Programs.whileMinCalls {m.group(1)}, PrimReturnsAt Gc.f1Layout '
                            f'OCaml.Programs.whileMin {m.group(1)} {m.group(2)} {m.group(3)} name')
            fill.append(f'  {fname} _ := whileMin_ccallReturns (by decide) o.{prims}')
        else:
            open_[fname] = re.sub(r'\bP\b', 'OCaml.Programs.whileMin', ty)
            fill.append(f'  {fname} _ := o.{fname}')
    lines = ['import OCaml.Vm.Sim.F1Headline', 'import OCaml.Programs.WhileMinShape',
             'import OCaml.Vm.Sim.WhileMinCalls', '',
             '/-! GENERATED by scripts/gen_f1_table.py. The F1 table premises for `whileMin`:',
             'fields of opcodes it never reaches are discharged by `whileMinOps`, fields',
             'proved by its shape run are filled, and the rest are `WhileMinOpen`. -/', '',
             'namespace OCaml.Vm.Sim', 'set_option autoImplicit false',
             'open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives', '',
             '/-- **What `whileMin`\'s machine run still needs** from the arm lanes. -/',
             'structure WhileMinOpen : Prop where']
    for fname, ty in open_.items():
        lines.append(f'  {fname} : {ty}')
    lines += ['', 'theorem whileMin_premises (o : WhileMinOpen) :',
              '    F1PremisesFor (fun op => OCaml.Programs.whileMinOps.contains op) OCaml.Programs.whileMin where']
    lines += fill
    lines += ['', '/-- **The `whileMin` machine run** from the open premises only. -/',
              'theorem whileMin_halts_open (o : WhileMinOpen) :',
              '    Halts Boot.WhileMin.cut "55\\n2500\\n36\\n" 0 :=',
              '  whileMin_halts_f1 (whileMin_premises o)', '', 'end OCaml.Vm.Sim', '']
    return '\n'.join(lines)


def render():
    ops = opcodes()
    found = rows()
    f1 = [o for o in ops if o not in NON_F1]
    fields, users, args, imports = {}, {}, {}, set()
    for op in f1:
        if op == 'STOP':
            args[op] = 'stop_row_f1 good'
            imports.add('OCaml.Vm.Sim.StopRow')
            continue
        if op not in found:
            fname = 'row_' + op
            fields[fname] = f'OCaml.OpArm P (OCaml.LoopAt Gc.f1Layout P) .{op}'
            users.setdefault(fname, []).append(op)
            args[op] = f'pre.{fname} (by simp [h])'
            continue
        name, ps, mod = found[op]
        imports.add(mod)
        call = [name]
        for p, ty in ps:
            if p in FIXED:
                call.append(FIXED[p])
            else:
                fname = SHARED.get(p, f'{op.lower()}_{p}')
                fields.setdefault(fname, spec(ty))
                users.setdefault(fname, []).append(op)
                call.append(f'(pre.{fname} (by simp [h]))')
        args[op] = ' '.join(call)
    lines = ['import ' + m for m in sorted(imports | {'OCaml.Vm.Sim.EntryF1', 'OCaml.Vm.Sim.F1Frame'})]
    lines += ['', '/-! GENERATED by scripts/gen_f1_table.py from the row theorems. The F1 arm',
              'table for the pinned layout: entry (`f1_entry`), and every F1 opcode dispatched',
              'to its row. Program-level premises the rows name, and the rows still open,',
              'are the named fields of `F1PremisesFor keep`, each needed only when an opcode',
              'using it is kept; opcodes the program never reaches (`keep` false) have',
              'vacuous rows (`OpArm.of_unreached`). -/', '',
              'namespace OCaml.Vm.Sim', 'set_option autoImplicit false',
              'open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives', '',
              '/-- The G1 budget leaves both thresholds of slack on the VM stack. -/',
              'theorem g1_capacity : StackCapacity Gc.g1Budget := by unfold StackCapacity; decide', '',
              '/-- **Program-level premises of the F1 rows**, each guarded by the kept',
              'opcodes that use it, and the rows still open. -/',
              'structure F1PremisesFor (keep : Opcode → Bool) (P : Prog) : Prop where']
    for fname, ty in fields.items():
        guard = ' || '.join(f'keep .{o}' for o in users[fname])
        lines.append(f'  {fname} : ({guard}) = true → {ty}')
    lines += ['', '/-- All rows kept: the premises of the general F1 statement. -/',
              'abbrev F1Premises (P : Prog) : Prop := F1PremisesFor (fun _ => true) P', '',
              '/-- **The F1 arm table** for the pinned layout, for a program that only',
              'reaches kept opcodes. -/',
              'theorem f1_table_for {keep : Opcode → Bool} {P : Prog} {c : Config}',
              '    (loaded : OCaml.Loaded Gc.f1Layout P c) (good : OCaml.GoodF1 P)',
              '    (fits : OCaml.Fits Gc.g1Budget P)',
              '    (reached : ∀ s i, Reach P s → decodeAt P.code s.pc = some i → keep i.op = true)',
              '    (pre : F1PremisesFor keep P) :',
              '    OCaml.F1Arms P c (OCaml.LoopAt Gc.f1Layout P) where',
              '  entry := f1_entry loaded',
              '  arm op hop := match op, hop with']
    for op in ops:
        if op in NON_F1:
            lines.append(f'    | .{op}, h => absurd h (by decide)')
        elif op == 'STOP':
            lines.append(f'    | .{op}, _ => {args[op]}')
        else:
            lines.append(f'    | .{op}, _ => if h : keep .{op} = true then {args[op]}')
            lines.append(f'        else OCaml.OpArm.of_unreached fun s i r d e => h (e ▸ reached s i r d)')
    lines += ['', '/-- **The F1 arm table** for the pinned layout. -/',
              'theorem f1_table {P : Prog} {c : Config} (loaded : OCaml.Loaded Gc.f1Layout P c)',
              '    (good : OCaml.GoodF1 P) (fits : OCaml.Fits Gc.g1Budget P) (pre : F1Premises P) :',
              '    OCaml.F1Arms P c (OCaml.LoopAt Gc.f1Layout P) :=',
              '  f1_table_for loaded good fits (fun _ _ _ _ => rfl) pre', '',
              'end OCaml.Vm.Sim', '']
    return '\n'.join(lines), render_whilemin(fields, users)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    a = ap.parse_args()
    outputs = dict(zip([OUT, WHILEMIN], render()))
    for path, text in outputs.items():
        if a.check:
            if not path.exists() or path.read_text() != text:
                sys.exit(f'F1 table generator drift: {path.relative_to(ROOT)}')
        else:
            path.write_text(text)
            print('wrote', path.relative_to(ROOT))
    if a.check:
        print('F1 table current')


if __name__ == '__main__':
    main()
