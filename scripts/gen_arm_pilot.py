#!/usr/bin/env python3
"""Generate F1 arm pilots through the existing site/segment pipeline.

Census supplies the span, gen_code_lemmas supplies the pins, A0's ElfDecode
supplies each decode, and disasm_to_segment -> gen_segment composes the run.
No handwritten machine steps or assumed postcondition closure.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from census import ROOT, disasm
from gen_ocaml_image import sections

sys.path.insert(0, str(ROOT / 'scripts/syi'))
from disasm_to_sites import classify
from disasm_to_segment import Instr, DraftBuilder, TOTAL_LOAD_BYTES
from gen_segment import SegmentEmitter
from gen_sites import BRANCH_OPS
from disasm_to_sites import sext

spec = importlib.util.spec_from_file_location('code_lemmas', ROOT / 'experiments/syi/gen_code_lemmas.py')
code = importlib.util.module_from_spec(spec)
spec.loader.exec_module(code)


FAMILIES = {
    'RETURN_MORE': ('ReturnMore', ['lw_tot', 'slli', 'alu_add', 'branch_nottaken', 'ld_tot', 'alu_addi', 'alu_addi', 'j']),
    'RETURN_FRAME': ('ReturnFrame', ['lw_tot', 'slli', 'alu_add', 'branch_taken', 'ld_tot', 'ld_tot', 'ld_tot', 'srai', 'alu_addi', 'j']),
    'APPLY': ('Apply', ['lw_tot', 'ld_tot', 'addiw', 'j', 'ld_tot', 'alu_addi', 'ld_tot', 'branch_nottaken', 'lw_tot', 'branch_taken']),
    'POPTRAP': ('Poptrap', ['auipc', 'lw_tot', 'branch_nottaken', 'ld_tot', 'auipc', 'ld_tot', 'alu_addi', 'srai', 'slli', 'alu_add', 'sd', 'alu_addi', 'j']),
    'PUSHTRAP': ('Pushtrap', ['lw_tot', 'auipc', 'alu_addi', 'alu_addi', 'slli', 'alu_add', 'sd', 'ld_tot', 'slli', 'alu_addi', 'ld_tot', 'sd', 'sd', 'sub', 'srai', 'slli', 'alu_addi', 'sd', 'ld_tot', 'alu_addi', 'alu_addi', 'sd', 'j']),
    'OFFSETREF': ('Offsetref', ['lw_tot', 'ld_tot', 'alu_addi', 'slliw', 'alu_add', 'sd', 'alu_addi', 'j']),
    'PUSH_RETADDR': ('PushRetaddr', ['lw_tot', 'slli', 'alu_addi', 'slli', 'alu_add', 'sd', 'sd', 'sd', 'alu_addi', 'alu_addi', 'j']),
    'SWITCH_INT': ('SwitchInt', ['andi', 'alu_addi', 'branch_taken', 'srai', 'slli', 'alu_add', 'lw_tot', 'slli', 'alu_add', 'j']),
    'SWITCH_BLOCK': ('SwitchBlock', ['andi', 'alu_addi', 'branch_nottaken', 'lhu_tot', 'lbu_tot', 'alu_add', 'slli', 'alu_add', 'lw_tot', 'slli', 'alu_add', 'j']),
    'CHECK_SIGNALS': ('CheckSignals', ['alu_addi', 'j', 'lw_tot', 'branch_taken']),
    'MULINT_PREFIX': ('MulintPrefix', ['ld_tot', 'srai', 'alu_addi', 'srai', 'jal']),
    'MULINT_SUFFIX': ('MulintSuffix', ['slli', 'alu_addi', 'alu_addi', 'j']),
    'PUSH': ('Push', ['sd', 'alu_addi', 'alu_addi', 'j']),
    'PUSHACC0': ('Pushacc0', ['sd', 'alu_addi', 'alu_addi', 'j']),
    'DISPATCH': ('Dispatch', ['lw_tot', 'alu_addi', 'branch_taken', 'slli', 'alu_add', 'lw_tot', 'alu_add', 'jr']),
    'ENVACC': ('Envacc', ['lw_tot', 'alu_addi', 'slli', 'alu_add', 'ld_tot', 'j']),
    'GETFIELD': ('Getfield', ['lw_tot', 'alu_addi', 'slli', 'alu_add', 'ld_tot', 'j']),
    'GETBYTESCHAR': ('Getbyteschar', ['ld_tot', 'alu_addi', 'alu_addi', 'srai', 'alu_add', 'lbu_tot', 'slli', 'alu_addi', 'j']),
    'GETSTRINGCHAR': ('Getstringchar', ['ld_tot', 'alu_addi', 'alu_addi', 'srai', 'alu_add', 'lbu_tot', 'slli', 'alu_addi', 'j']),
    'OFFSETCLOSUREM3': ('Offsetclosurem3', ['alu_addi', 'alu_addi', 'j']),
    'OFFSETCLOSURE0': ('Offsetclosure0', ['alu_addi', 'alu_addi', 'j']),
    'OFFSETCLOSURE3': ('Offsetclosure3', ['alu_addi', 'alu_addi', 'j']),
    'OFFSETCLOSURE': ('Offsetclosure', ['lw_tot', 'alu_addi', 'slli', 'alu_add', 'j']),
    'GETVECTITEM': ('Getvectitem', ['ld_tot', 'alu_addi', 'alu_addi', 'srai', 'slli', 'alu_add', 'ld_tot', 'j']),
    'POP': ('Pop', ['lw_tot', 'alu_addi', 'slli', 'alu_add', 'j']),
    'ACC': ('Acc', ['lw_tot', 'alu_addi', 'slli', 'alu_add', 'ld_tot', 'j']),
    'ACC0': ('Acc0', ['ld_tot', 'alu_addi', 'j']),
    'ACC1': ('Acc1', ['ld_tot', 'alu_addi', 'j']),
    'ACC2': ('Acc2', ['ld_tot', 'alu_addi', 'j']),
    'ACC3': ('Acc3', ['ld_tot', 'alu_addi', 'j']),
    'ACC4': ('Acc4', ['ld_tot', 'alu_addi', 'j']),
    'ACC5': ('Acc5', ['ld_tot', 'alu_addi', 'j']),
    'ACC6': ('Acc6', ['ld_tot', 'alu_addi', 'j']),
    'ACC7': ('Acc7', ['ld_tot', 'alu_addi', 'j']),
    'ENVACC1': ('Envacc1', ['ld_tot', 'alu_addi', 'j']),
    'ENVACC2': ('Envacc2', ['ld_tot', 'alu_addi', 'j']),
    'ENVACC3': ('Envacc3', ['ld_tot', 'alu_addi', 'j']),
    'ENVACC4': ('Envacc4', ['ld_tot', 'alu_addi', 'j']),
    'GETFIELD0': ('Getfield0', ['ld_tot', 'alu_addi', 'j']),
    'GETFIELD1': ('Getfield1', ['ld_tot', 'alu_addi', 'j']),
    'GETFIELD2': ('Getfield2', ['ld_tot', 'alu_addi', 'j']),
    'GETFIELD3': ('Getfield3', ['ld_tot', 'alu_addi', 'j']),
    'BRANCHIF_JUMP': ('BranchifJump', ['alu_addi', 'branch_nottaken', 'lw_tot', 'slli', 'alu_add', 'j']),
    'BRANCHIF_NEXT': ('BranchifNext', ['alu_addi', 'branch_taken', 'alu_addi', 'j']),
    'BRANCHIFNOT_JUMP': ('BranchifnotJump', ['alu_addi', 'branch_taken', 'lw_tot', 'slli', 'alu_add', 'j']),
    'BRANCHIFNOT_NEXT': ('BranchifnotNext', ['alu_addi', 'branch_nottaken', 'alu_addi', 'j']),
    'BRANCH': ('Branch', ['lw_tot', 'slli', 'alu_add', 'j']),
    'OFFSETINT': ('Offsetint', ['lw_tot', 'alu_addi', 'slliw', 'alu_add', 'j']),
    'CONSTINT': ('Constint', ['lw_tot', 'alu_addi', 'slli', 'alu_addi', 'j']),
    'CONST0': ('Const0', ['alu_addi', 'alu_addi', 'j']),
    'CONST1': ('Const1', ['alu_addi', 'alu_addi', 'j']),
    'CONST2': ('Const2', ['alu_addi', 'alu_addi', 'j']),
    'CONST3': ('Const3', ['alu_addi', 'alu_addi', 'j']),
    'BOOLNOT': ('Boolnot', ['alu_addi', 'alu_addi', 'sub', 'j']),
    'NEGINT': ('Negint', ['alu_addi', 'alu_addi', 'sub', 'j']),
    'ADDINT': ('Addint', ['ld_tot', 'alu_addi', 'alu_addi', 'alu_add', 'alu_addi', 'j']),
    'SUBINT': ('Subint', ['ld_tot', 'alu_addi', 'alu_addi', 'sub', 'alu_addi', 'j']),
    'ANDINT': ('Andint', ['ld_tot', 'alu_addi', 'alu_addi', 'alu_and', 'j']),
    'ORINT': ('Orint', ['ld_tot', 'alu_addi', 'alu_addi', 'alu_or', 'j']),
    'XORINT': ('Xorint', ['ld_tot', 'alu_addi', 'alu_addi', 'alu_xor', 'ori', 'j']),
    'LSLINT': ('Lslint', ['ld_tot', 'alu_addi', 'alu_addi', 'srai', 'sll', 'alu_addi', 'alu_addi', 'j']),
    'LSRINT': ('Lsrint', ['ld_tot', 'alu_addi', 'alu_addi', 'srai', 'srl', 'ori', 'j']),
    'ASRINT': ('Asrint', ['ld_tot', 'alu_addi', 'alu_addi', 'srai', 'sra', 'ori', 'j']),
    'ATOM0': ('Atom0', ['auipc', 'ld_tot', 'alu_addi', 'alu_addi', 'j']),
    'ATOM': ('Atom', ['lw_tot', 'auipc', 'ld_tot', 'alu_addi', 'slli', 'alu_addi', 'alu_add', 'j']),
    'ISINT': ('Isint', ['slli', 'andi', 'alu_addi', 'alu_addi', 'j']),
    'VECTLENGTH': ('Vectlength', ['ld_tot', 'alu_addi', 'srli', 'slli', 'alu_addi', 'j']),
    'C_CALL1_PREFIX': ('Ccall1Prefix', ['alu_addi', 'sd', 'sd', 'auipc', 'alu_addi', 'ld_tot', 'alu_addi', 'alu_addi', 'sd', 'lw_tot', 'auipc', 'ld_tot', 'alu_addi', 'slli', 'alu_add', 'ld_tot', 'jalr']),
    'C_CALL1_SUFFIX': ('Ccall1Suffix', ['ld_tot', 'alu_addi', 'ld_tot', 'ld_tot', 'alu_addi', 'j']),
    'ASSIGN': ('Assign', ['lw_tot', 'alu_addi', 'slli', 'alu_add', 'sd', 'alu_addi', 'j']),
}


# Fixed-arity application paths include the shared no-growth/no-pending tail.
FAMILIES.update({
    'APPLY1': ('Apply1', ['ld_tot', 'slli', 'alu_addi', 'sd', 'sd', 'sd', 'sd', 'ld_tot', 'alu_addi', 'alu_addi', 'j', 'ld_tot', 'alu_addi', 'ld_tot', 'branch_nottaken', 'lw_tot', 'branch_taken']),
    'APPLY2': ('Apply2', ['ld_tot', 'ld_tot', 'sd', 'sd', 'sd', 'sd', 'ld_tot', 'slli', 'alu_addi', 'sd', 'ld_tot', 'alu_addi', 'ld_tot', 'alu_addi', 'alu_addi', 'branch_taken', 'lw_tot', 'branch_taken']),
    'APPLY3': ('Apply3', ['ld_tot', 'ld_tot', 'ld_tot', 'slli', 'alu_addi', 'sd', 'sd', 'sd', 'sd', 'sd', 'sd', 'ld_tot', 'alu_addi', 'alu_addi', 'j', 'ld_tot', 'alu_addi', 'ld_tot', 'branch_nottaken', 'lw_tot', 'branch_taken']),
})


for _n in range(1, 8):
    FAMILIES[f'PUSHACC{_n}'] = (f'Pushacc{_n}', ['sd', 'alu_addi', 'ld_tot', 'alu_addi', 'j'])
for _n in range(1, 5):
    FAMILIES[f'PUSHENVACC{_n}'] = (f'Pushenvacc{_n}', ['sd', 'ld_tot', 'alu_addi', 'alu_addi', 'j'])
for _n in range(4):
    FAMILIES[f'PUSHCONST{_n}'] = (f'Pushconst{_n}', ['sd', 'alu_addi', 'alu_addi', 'alu_addi', 'j'])


# Keep repeated shift/bit operations from reducing total-memory expressions.
# These load parameters have exact equations; callers do not assume a result.
FAMILIES['C_CALLN_PREFIX'] = ('CcallnPrefix', [
    'alu_addi', 'lw_tot', 'sd', 'sd', 'sd', 'auipc', 'alu_addi', 'ld_tot',
    'alu_addi', 'alu_addi', 'sd', 'lw_tot', 'auipc', 'ld_tot', 'alu_addi',
    'slli', 'alu_add', 'ld_tot', 'sd', 'slli', 'jalr'])
FAMILIES['C_CALLN_SUFFIX'] = ('CcallnSuffix', [
    'ld_tot', 'alu_addi', 'ld_tot', 'ld_tot', 'alu_addi', 'ld_tot', 'alu_add', 'j'])

OPAQUE_LOADS = {'APPLY1', 'APPLY2', 'APPLY3', 'RETURN_MORE', 'RETURN_FRAME', 'APPLY', 'POPTRAP', 'PUSHTRAP', 'OFFSETREF', 'SWITCH_BLOCK', 'VECTLENGTH', 'C_CALL1_PREFIX', 'C_CALL1_SUFFIX',
                'C_CALLN_PREFIX', 'C_CALLN_SUFFIX'}

PATHS = {
    'APPLY1': ('APPLY1', [False, True]),
    'APPLY2': ('APPLY2', [True, True]),
    'APPLY3': ('APPLY3', [False, True]),
    'RETURN_MORE': ('RETURN', [False]),
    'RETURN_FRAME': ('RETURN', [True]),
    'APPLY': ('APPLY', [False, True]),
    'POPTRAP': ('POPTRAP', [False]),
    'SWITCH_INT': ('SWITCH', [True]),
    'SWITCH_BLOCK': ('SWITCH', [False]),
    'CHECK_SIGNALS': ('CHECK_SIGNALS', [True]),
    'MULINT_PREFIX': ('MULINT', []),
    'MULINT_SUFFIX': ('MULINT', []),
    'C_CALL1_PREFIX': ('C_CALL1', []),
    'C_CALL1_SUFFIX': ('C_CALL1', []),
    'C_CALLN_PREFIX': ('C_CALLN', []),
    'C_CALLN_SUFFIX': ('C_CALLN', []),
    'DISPATCH': (None, [True]),
    'BRANCHIF_JUMP': ('BRANCHIF', [False]),
    'BRANCHIF_NEXT': ('BRANCHIF', [True]),
    'BRANCHIFNOT_JUMP': ('BRANCHIFNOT', [True]),
    'BRANCHIFNOT_NEXT': ('BRANCHIFNOT', [False]),
}


# Fixed-arity C calls share their saved frame and six-instruction return.
# Check each native shape explicitly; the callee is composed separately.
for _arity in range(2, 6):
    _op = f'C_CALL{_arity}'
    _prefix, _suffix = _op + '_PREFIX', _op + '_SUFFIX'
    FAMILIES[_prefix] = (f'Ccall{_arity}Prefix',
        ['alu_addi', 'sd', 'sd', 'auipc', 'alu_addi', 'ld_tot', 'alu_addi',
         'alu_addi', 'sd', 'lw_tot', 'auipc', 'ld_tot', 'ld_tot', 'slli',
         'alu_add', 'ld_tot'] + ['ld_tot'] * (_arity - 2) + ['alu_addi', 'jalr'])
    FAMILIES[_suffix] = (f'Ccall{_arity}Suffix',
        ['ld_tot', 'alu_addi', 'ld_tot', 'ld_tot', 'alu_addi', 'j'])
    PATHS[_prefix] = (_op, [])
    PATHS[_suffix] = (_op, [])
    OPAQUE_LOADS.update([_prefix, _suffix])


for _suffix in ['M3', '0', '3']:
    _op = 'PUSHOFFSETCLOSURE' + _suffix
    FAMILIES[_op] = (_op.title(), ['sd', 'alu_addi', 'alu_addi', 'alu_addi', 'j'])
    PATHS[_op] = (_op, [])

for _op, _finish in [('PUSHCONSTINT', 'alu_addi'), ('PUSHOFFSETCLOSURE', 'alu_add')]:
    FAMILIES[_op] = (_op.title(), ['sd', 'alu_addi', 'lw_tot', 'alu_addi', 'slli', _finish, 'j'])
    PATHS[_op] = (_op, [])

for _op in ['PUSHENVACC', 'PUSHACC']:
    FAMILIES[_op] = (_op.title(), ['sd', 'alu_addi', 'lw_tot', 'alu_addi', 'slli', 'alu_add', 'ld_tot', 'j'])
    PATHS[_op] = (_op, [])

FAMILIES['PUSHATOM0'] = ('Pushatom0', ['sd', 'alu_addi', 'auipc', 'ld_tot', 'alu_addi', 'alu_addi', 'j'])
FAMILIES['PUSHATOM'] = ('Pushatom', ['sd', 'alu_addi', 'lw_tot', 'auipc', 'ld_tot', 'alu_addi', 'slli', 'alu_addi', 'alu_add', 'j'])
for _op in ['PUSHATOM0', 'PUSHATOM']:
    PATHS[_op] = (_op, [])

FAMILIES['GETGLOBAL'] = ('Getglobal', ['lw_tot', 'auipc', 'ld_tot', 'alu_addi', 'slli', 'alu_add', 'ld_tot', 'j'])
FAMILIES['PUSHGETGLOBAL'] = ('Pushgetglobal', ['sd', 'alu_addi', 'lw_tot', 'auipc', 'ld_tot', 'alu_addi', 'slli', 'alu_add', 'ld_tot', 'j'])
for _op in ['GETGLOBAL', 'PUSHGETGLOBAL']:
    PATHS[_op] = (_op, [])

for _push in [False, True]:
    _op = ('PUSH' if _push else '') + 'GETGLOBALFIELD'
    FAMILIES[_op] = (_op.title(), (['sd', 'alu_addi'] if _push else []) +
        ['lw_tot', 'auipc', 'ld_tot', 'lw_tot', 'slli', 'alu_add', 'ld_tot', 'slli', 'alu_addi', 'alu_add', 'ld_tot', 'j'])
    PATHS[_op] = (_op, [])


# Integer comparisons branch to the false-result helper; fallthrough returns true.
for _op in ['LTINT', 'LEINT', 'GTINT', 'GEINT', 'ULTINT', 'UGEINT']:
    for _truth in [True, False]:
        _family = _op + ('_TRUE' if _truth else '_FALSE')
        FAMILIES[_family] = (_op.title() + ('True' if _truth else 'False'),
            ['ld_tot', 'alu_addi', 'alu_addi',
             'branch_nottaken' if _truth else 'branch_taken', 'alu_addi', 'j'])
        PATHS[_family] = (_op, [not _truth])

for _op in ['EQ', 'NEQ']:
    for _truth in [True, False]:
        _taken = _truth if _op == 'EQ' else not _truth
        _family = _op + ('_TRUE' if _truth else '_FALSE')
        FAMILIES[_family] = (_op.title() + ('True' if _truth else 'False'),
            ['ld_tot', 'alu_addi', 'alu_addi',
             'branch_taken' if _taken else 'branch_nottaken', 'alu_addi', 'j'])
        PATHS[_family] = (_op, [_taken])


for _op in ['BLTINT', 'BLEINT', 'BGTINT', 'BGEINT', 'BULTINT', 'BUGEINT', 'BEQ', 'BNEQ']:
    for _jumping in [True, False]:
        _family = _op + ('_JUMP' if _jumping else '_NEXT')
        _taken = _jumping if _op == 'BEQ' else not _jumping
        FAMILIES[_family] = (_op.title() + ('Jump' if _jumping else 'Next'),
            ['lw_tot', 'srai', 'branch_taken' if _taken else 'branch_nottaken'] +
            (['lw_tot', 'slli', 'alu_addi', 'alu_add', 'j'] if _jumping else ['alu_addi', 'j']))
        PATHS[_family] = (_op, [_taken])


def path_span(instructions, start, decisions, exit_pc=None):
    """Follow explicit branch outcomes; generated contracts retain every guard."""
    by_pc = {i[0]: i for i in instructions}
    pc, insts, rows, branch = start, [], [], 0
    for _ in range(32):
        ins = by_pc[pc]
        choices = classify(ins[0], ins[1], ins[2] + ' ' + ins[3], {})
        if any(r.cls == 'branch_taken' for r in choices):
            if branch >= len(decisions):
                raise ValueError('path needs another explicit branch decision')
            cls = 'branch_taken' if decisions[branch] else 'branch_nottaken'
            row = next(r for r in choices if r.cls == cls)
            branch += 1
        else:
            row = choices[0]
        insts.append(ins)
        rows.append(row)
        if row.cls in ('j', 'jr', 'jal', 'jalr') and not (row.cls == 'j' and exit_pc is not None):
            if branch != len(decisions):
                raise ValueError('unused branch decision')
            return insts, rows
        if row.cls == 'j':
            pc += sext(int(row.ops[0], 16), 21)
        else:
            pc = pc + sext(int(row.ops[3], 16), 13) if row.cls == 'branch_taken' else pc + 4
        if pc == exit_pc:
            if branch != len(decisions):
                raise ValueError('unused branch decision')
            return insts, rows
    raise ValueError('path did not terminate at a jump')


def site_outputs(insts, rows, stem, lower):
    result = {}
    name = 'caml' + stem
    pred = f'Vsa.Sim.Code.Caml{stem}Loaded'
    pin_module = f'Vsa.Sim.Code.Caml{stem}'
    result[ROOT / f'Vsa/Sim/Code/Caml{stem}.lean'] = code.render(name, [(i[0], i[1]) for i in insts]).replace(
        'generated by experiments/gen_code_lemmas.py', 'GENERATED by scripts/gen_arm_pilot.py (experiments/syi/gen_code_lemmas.py)')
    if any(r.cls == 'sd' for r in rows):
        lo, hi = min(i[0] for i in insts), max(i[0] for i in insts) + 4
        # Local fetch pins survive each checked disjoint store. This is a
        # byte-agreement certificate, not an assumed execution postcondition.
        transport = [
            'import Vsa.Sim.LibraryFacts', f'import {pin_module}', '',
            '/-! GENERATED by scripts/gen_arm_pilot.py. Store frame for local fetch pins. -/',
            'namespace Vsa.Sim', '',
            f'theorem {lower}_code_store (m : Std.ExtHashMap Nat (BitVec 8))',
            '    (a : Nat) (v : BitVec 64)',
            f'    (outside : a + 8 ≤ 0x{lo:x} ∨ 0x{hi:x} ≤ a)',
            f'    (loaded : {pred} m) :',
            f'    {pred} (writeMap8 m a (sdData_val v)) := by',
            f'  unfold {pred} ' + ' '.join(f'Code.{name}Chunk{i}' for i in range((len(insts)+code.CHUNK-1)//code.CHUNK)) + ' at loaded ⊢',
            '  simpa only [']
        transport += [f'    getElem?_writeMap8_out m a (sdData_val v) 0x{addr+k:x} (by omega)' +
                      (',' if (addr, k) != (insts[-1][0], 3) else '] using loaded')
                      for addr, _, _, _ in insts for k in range(4)]
        transport += ['', 'end Vsa.Sim', '']
        result[ROOT / f'OCaml/Vm/Sim/{stem}StoreFrame.lean'] = '\n'.join(transport)
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        index = []
        for p in sorted((ROOT / 'Vsa/Sim/ElfDecode').glob('Part*.lean')):
            index += [f'{w}\tVsa.Sim.ElfDecode.{p.stem}' for w in re.findall(r'^theorem decode_([0-9a-f]{8})', p.read_text(), re.M)]
        (tmp / 'decode.tsv').write_text('\n'.join(index) + '\n')
        (tmp / f'{lower}.tsv').write_text('\n'.join(r.tsv() for r in rows) + '\n')
        subprocess.run([sys.executable, str(ROOT / 'scripts/syi/gen_sites.py'), str(tmp / f'{lower}.tsv'),
                        '--code-loaded', pred, '--code-import', pin_module,
                        '--index', str(tmp / 'decode.tsv'), '--decode-namespace', 'Vsa.Sim.ElfDecode',
                        '--default-limits', '--suffix', '_' + lower, '-o', str(tmp / 'Sites.lean')], check=True,
                       stdout=subprocess.DEVNULL)
        result[ROOT / f'OCaml/Vm/Sim/{stem}Sites.lean'] = (tmp / 'Sites.lean').read_text().replace(
            'Per-site `StepObs` battery generated by scripts/gen_sites.py from',
            'GENERATED by scripts/gen_arm_pilot.py via scripts/syi/gen_sites.py from')
    return result


def pin_constructor(count):
    chunks = ['⟨' + ', '.join(['?_'] * (4 * min(code.CHUNK, count-i))) + '⟩'
              for i in range(0, count, code.CHUNK)]
    return chunks[0] if len(chunks) == 1 else '⟨' + ', '.join(chunks) + '⟩'


def image_projection(insts, pred, pin_module, chunks, theorem, text_base):
    """Project either arm or library pins from the same executable image."""
    lines = ['import OCaml.Vm.Platform', 'import ' + pin_module, '',
             '/-! GENERATED by scripts/gen_arm_pilot.py. Full-image projection. -/',
             'namespace OCaml.Vm.Sim', 'open Vsa.Machine', '',
             f'theorem {theorem} {{c : Config}} (h : ExecutableImage c) :',
             f'    {pred} c.σ.mem := by', f'  unfold {pred} ' + ' '.join(chunks),
             '  refine ' + pin_constructor(len(insts))]
    for a, w, _, _ in insts:
        for k in range(4):
            offset = a + k - text_base
            byte = (w >> (8 * k)) & 255
            lines += [f'  · have hb := h.text {offset} (by decide)',
                      f'    have he : Image.textByte {offset} = (0x{byte:02x}#8) := by decide +kernel',
                      '    rw [he] at hb', '    exact hb']
    lines += ['', 'end OCaml.Vm.Sim', '']
    return '\n'.join(lines)


def outputs(family='CONST0'):
    stem, shape = FAMILIES[family]
    lower = family.lower()
    text_base = sections((ROOT / 'c/ocamlrun-riscv-htif.elf').read_bytes())['.text'][0]
    census = json.loads((ROOT / 'results/census.json').read_text())['caml_interprete']
    instructions = disasm(ROOT / 'c/ocamlrun-riscv-htif.elf')['caml_interprete']['insts']
    if family in PATHS:
        opcode, decisions = PATHS[family]
        start = int(census['loop_head'] if opcode is None else census['arms'][opcode]['addr'], 16)
        if family.endswith('_SUFFIX'):
            prefix, _ = path_span(instructions, start, decisions)
            start = prefix[-1][0] + 4
        insts, rows = path_span(instructions, start, decisions,
            int(census['loop_head'], 16) if family in {'CHECK_SIGNALS', 'APPLY', 'APPLY1', 'APPLY2', 'APPLY3'} else None)
    else:
        arm = census['arms'][family]
        start = int(arm['addr'], 16)
        stop = start + 4 * arm['own']
        insts = [i for i in instructions if start <= i[0] < stop]
        rows = [row for a, w, m, ops in insts for row in classify(a, w, m + ' ' + ops, {})]
    for row in rows:
        if row.cls in ('ld', 'lw', 'lbu', 'lhu'):
            row.cls += '_tot'
    if [r.cls for r in rows] != shape:
        raise ValueError(f'{family} shape changed; revisit the pilot contract')
    result = site_outputs(insts, rows, stem, lower)
    name = 'caml' + stem
    pred = f'Vsa.Sim.Code.Caml{stem}Loaded'
    pin_module = f'Vsa.Sim.Code.Caml{stem}'
    site_module = f'OCaml.Vm.Sim.{stem}Sites'
    instrs = [Instr(r.addr, r.word, r.cls, [str(x) for x in r.ops], r.raw) for r in rows]
    draft = DraftBuilder(instrs, '_' + lower, pred).build('tr_' + lower, [site_module, 'Vsa.Sim.SegState', 'Vsa.Sim.StepCount', 'Vsa.Sim.ChainFrameOut'])
    # The prefix stops at callee entry; callSeg supplies the callee separately.
    if instrs[-1].cls == 'jal':
        assert draft['steps'][-1]['class'] == 'call'
        draft['steps'].pop()
    draft['params'].pop(0)  # Bounds are emitted below; no callee ghosts.
    draft['prelude'] = []
    draft['params'].append('(σ0 : MState)')
    if any(i.cls == 'sd' for i in instrs):
        draft['imports'].append(f'OCaml.Vm.Sim.{stem}StoreFrame')
    draft.update(boundary='segst', entry=hex(start), mem_param='m0', default_limits=True, counted=True, frame_origin='σ0',
                 doc=f'{family} arm body, generated from the census. This is a machine segment, not yet ArmSim.next.')
    if family.startswith('C_CALL') and family.endswith('_PREFIX'):
        draft['frame_compact'] = True
    for k in ['pre', 'post', 'pre_bind', 'post_proof']:
        draft.pop(k)
    values = {}
    memory = 'm0'
    for index, step in enumerate(draft['steps']):
        cls, ops = instrs[index].cls, instrs[index].ops
        value = lambda reg: values.get('x' + reg, 'v' + reg) if int(reg) else '(0#64)'
        if step['class'] == 'alu':
            step['rd_val'] = re.sub(r'\bv(\d+)\b', lambda m: values.get('x' + m[1], m[0]), step['raw_val'])
            previous_values = dict(values)
            values[step['rd']] = step['rd_val']
            step.pop('rw', None)
            cls = instrs[index].cls
            if cls in TOTAL_LOAD_BYTES:
                n = TOTAL_LOAD_BYTES[cls]
                base, off = instrs[index].ops[1:]
                ea = f"({previous_values.get('x' + base, 'v' + base)} + sign_extend (m := 64) (0x{off}#12))"
                tag = step['addr'][2:]
                draft['params'] += [
                    f"(hlo_{tag} : 0x80000000 ≤ {ea}.toNat)",
                    f"(hhi_{tag} : {ea}.toNat + {n} ≤ 0x100000000)",
                    f"(hhtif_{tag} : {ea}.toNat + {n} ≤ tohostAddr ∨ tohostAddr + 8 ≤ {ea}.toNat)"]
                step['call'] = step['call'].replace('TODO(hlo)', f'hlo_{tag}').replace('TODO(hhiram)', f'hhi_{tag}').replace('TODO(hhtif)', f'hhtif_{tag}')
                step['rd_val'] = step['rd_val'].replace('σ.mem', f'({memory})' if memory != 'm0' else memory)
                values[step['rd']] = step['rd_val']
                step['rw'] = 'hmemeq' if index == 0 else f'hmemE{index}'
                if family in OPAQUE_LOADS:
                    alias = f'loaded_{tag}'
                    draft['params'] += [f'({alias} : BitVec 64)',
                                        f'(hvalue_{tag} : {alias} = {step["rd_val"]})']
                    step['rd_val'] = alias
                    values[step['rd']] = alias
                    step['rw'] += f', ← hvalue_{tag}'
        elif cls == 'sd':
            src, base, off = ops
            ea = f"({value(base)} + sign_extend (m := 64) (0x{off}#12))"
            tag = step['addr'][2:]
            draft['params'] += [
                f'(hlo_{tag} : 0x80000000 ≤ {ea}.toNat)',
                f'(hhi_{tag} : {ea}.toNat + 8 ≤ 0x100000000)',
                f'(hhtif_{tag} : tohostAddr + 16 ≤ {ea}.toNat)',
                f'(halign_{tag} : {ea}.toNat % 8 = 0)',
                f'(hcode_{tag} : {ea}.toNat + 8 ≤ 0x{min(i[0] for i in insts):x} ∨ '
                f'0x{max(i[0] for i in insts)+4:x} ≤ {ea}.toNat)']
            step.update(key=f'{ea}.toNat', src_val=value(src),
                        loaded_via=f'{lower}_code_store _ _ _ hcode_{tag} $prev')
            step.pop('key_rw')
            for hole, bound_name in [('halo', 'hlo'), ('hahiram', 'hhi'),
                               ('hahiwin', 'hhtif'), ('haalign', 'halign')]:
                step['call'] = step['call'].replace(f'TODO({hole})', f'{bound_name}_{tag}')
            stored = f'writeMap8 ({memory}) ({ea}.toNat) (sdData_val {value(src)})'
            # Keep map expressions opaque in subsequent load/pin elaboration.
            # The caller instantiates this exact ghost equation with rfl.
            memory = f'm_{tag}'
            draft['params'] += [f'({memory} : Std.ExtHashMap Nat (BitVec 8))',
                                f'(hstore_{tag} : {memory} = {stored})']
            step.update(mem_alias=memory, mem_alias_eq=f'hstore_{tag}')
        elif cls in ('branch_taken', 'branch_nottaken'):
            guard = BRANCH_OPS[ops[0]][1].format(v1=value(ops[1]), v2=value(ops[2]))
            truth = 'true' if cls == 'branch_taken' else 'false'
            tag = step['addr'][2:]
            draft['params'].append(f'(hguard_{tag} : {guard} = {truth})')
            step['pre_lines'] = []
            step['call'] = step['call'].replace('hguard$k', f'hguard_{tag}')
        elif cls in ('jr', 'jalr'):
            base, off = (ops[0], '000') if cls == 'jr' else (ops[1], ops[2])
            target = f'(BitVec.update ({value(base)} + sign_extend (m := 64) (0x{off}#12)) 0 0#1)'
            tag = step['addr'][2:]
            draft['params'].append(f'(htgt_{tag} : {target}.toNat % 4 = 0)')
            step['call'] = step['call'].replace('TODO(htgt)', f'htgt_{tag}')
            step['pc_val'] = target
            step.pop('pc_rw')
    if family.startswith('C_CALL') and family.endswith('_PREFIX'):
        # Locate the domain and primitive-table address constructions by shape;
        # C_CALLN inserts an argument push and has a distinct native-stack save.
        domain_index = next(i for i, ins in enumerate(instrs)
                            if ins.cls == 'alu_addi' and ins.ops[0] == '25')
        table_index = next(i for i, ins in enumerate(instrs)
                           if ins.cls == 'ld_tot' and ins.ops[1] == '15'
                           and instrs[i - 1].cls == 'auipc')
        domain_value = draft['steps'][domain_index]['rd_val']
        table_tag = draft['steps'][table_index]['addr'][2:]
        table_address = next(p for p in draft['params'] if p.startswith(f'(hlo_{table_tag}')).split(' ≤ ', 1)[1].removesuffix('.toNat)')
        result[ROOT / f'OCaml/Vm/Sim/{stem}Layout.lean'] = f"""import OCaml.Vm.Layout
import {site_module}

/-! GENERATED by scripts/gen_arm_pilot.py. ELF-relative expressions checked against Layout. -/
namespace OCaml.Vm.Sim
open LeanRV64DExecutable.Functions Sail

theorem {lower}_domain : {domain_value} = BitVec.ofNat 64 Layout.sym_Caml_state := by decide

theorem {lower}_prim_contents : {table_address} =
    BitVec.ofNat 64 (Layout.sym_caml_prim_table + Layout.off_prim_contents) := by decide

end OCaml.Vm.Sim
"""
    spec_text = json.dumps(draft, indent=2, ensure_ascii=False) + '\n'
    if 'TODO' in spec_text:
        raise ValueError('unfilled pilot residue')
    result[ROOT / f'scripts/syi/segments/{lower}.json'] = spec_text
    result[ROOT / f'OCaml/Vm/Sim/{stem}Segment.lean'] = SegmentEmitter(draft).emit().replace(
        'Generated by scripts/gen_segment.py', 'GENERATED by scripts/gen_arm_pilot.py via scripts/syi/gen_segment.py')
    result[ROOT / f'OCaml/Vm/Sim/{stem}Pins.lean'] = image_projection(
        insts, pred, pin_module,
        [f'Vsa.Sim.Code.{name}Chunk{i}' for i in range((len(insts)+code.CHUNK-1)//code.CHUNK)],
        lower + '_loaded', text_base)
    if family == 'MULINT_PREFIX':
        library = disasm(ROOT / 'c/ocamlrun-riscv-htif.elf')['__muldi3']['insts']
        result[ROOT / 'OCaml/Vm/Sim/Muldi3Pins.lean'] = image_projection(
            library, 'Vsa.Sim.Code.__muldi3Loaded', 'Vsa.Sim.Code.__muldi3',
            [f'Vsa.Sim.Code.__muldi3Chunk{i}' for i in range((len(library)+code.CHUNK-1)//code.CHUNK)],
            'muldi3_loaded', text_base)

    return result


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--family', choices=FAMILIES)
    args = ap.parse_args()
    result = {}
    for family in ([args.family] if args.family else FAMILIES):
        result.update(outputs(family))
    for p, text in result.items():
        if args.check:
            if not p.exists() or p.read_text() != text:
                raise SystemExit(f'arm pilot generator drift: {p.relative_to(ROOT)}')
        else:
            p.write_text(text)
    print('Arm pilot artifacts current')
