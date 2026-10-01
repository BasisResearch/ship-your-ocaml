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
    'DISPATCH': ('Dispatch', ['lw_tot', 'alu_addi', 'branch_taken', 'slli', 'alu_add', 'lw_tot', 'alu_add', 'jr']),
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
    'ISINT': ('Isint', ['slli', 'andi', 'alu_addi', 'alu_addi', 'j']),
}


PATHS = {
    'DISPATCH': (None, [True]),
    'BRANCHIF_JUMP': ('BRANCHIF', [False]),
    'BRANCHIF_NEXT': ('BRANCHIF', [True]),
    'BRANCHIFNOT_JUMP': ('BRANCHIFNOT', [True]),
    'BRANCHIFNOT_NEXT': ('BRANCHIFNOT', [False]),
}


def path_span(instructions, start, decisions):
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
        if row.cls in ('j', 'jr'):
            if branch != len(decisions):
                raise ValueError('unused branch decision')
            return insts, rows
        pc = pc + sext(int(row.ops[3], 16), 13) if row.cls == 'branch_taken' else pc + 4
    raise ValueError('path did not terminate at a jump')


def site_outputs(insts, rows, stem, lower):
    result = {}
    name = 'caml' + stem
    pred = f'Vsa.Sim.Code.Caml{stem}Loaded'
    pin_module = f'Vsa.Sim.Code.Caml{stem}'
    result[ROOT / f'Vsa/Sim/Code/Caml{stem}.lean'] = code.render(name, [(i[0], i[1]) for i in insts]).replace(
        'generated by experiments/gen_code_lemmas.py', 'GENERATED by scripts/gen_arm_pilot.py (experiments/syi/gen_code_lemmas.py)')
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


def outputs(family='CONST0'):
    stem, shape = FAMILIES[family]
    lower = family.lower()
    text_base = sections((ROOT / 'c/ocamlrun-riscv-htif.elf').read_bytes())['.text'][0]
    census = json.loads((ROOT / 'results/census.json').read_text())['caml_interprete']
    instructions = disasm(ROOT / 'c/ocamlrun-riscv-htif.elf')['caml_interprete']['insts']
    if family in PATHS:
        opcode, decisions = PATHS[family]
        start = int(census['loop_head'] if opcode is None else census['arms'][opcode]['addr'], 16)
        insts, rows = path_span(instructions, start, decisions)
    else:
        arm = census['arms'][family]
        start = int(arm['addr'], 16)
        stop = start + 4 * arm['own']
        insts = [i for i in instructions if start <= i[0] < stop]
        rows = [row for a, w, m, ops in insts for row in classify(a, w, m + ' ' + ops, {})]
    for row in rows:
        if row.cls in ('ld', 'lw', 'lbu'):
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
    draft['params'].pop(0)  # Bounds are emitted below; no callee ghosts.
    draft['prelude'] = []
    draft['params'].append('(σ0 : MState)')
    draft.update(boundary='segst', entry=hex(start), mem_param='m0', default_limits=True, counted=True, frame_origin='σ0',
                 doc=f'{family} arm body, generated from the census. This is a machine segment, not yet ArmSim.next.')
    for k in ['pre', 'post', 'pre_bind', 'post_proof']:
        draft.pop(k)
    values = {}
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
                step['rd_val'] = step['rd_val'].replace('σ.mem', 'm0')
                values[step['rd']] = step['rd_val']
                step['rw'] = 'hmemeq' if index == 0 else f'hmemE{index}'
        elif cls in ('branch_taken', 'branch_nottaken'):
            guard = BRANCH_OPS[ops[0]][1].format(v1=value(ops[1]), v2=value(ops[2]))
            truth = 'true' if cls == 'branch_taken' else 'false'
            tag = step['addr'][2:]
            draft['params'].append(f'(hguard_{tag} : {guard} = {truth})')
            step['pre_lines'] = []
            step['call'] = step['call'].replace('hguard$k', f'hguard_{tag}')
        elif cls == 'jr':
            target = f'(BitVec.update ({value(ops[0])} + sign_extend (m := 64) (0x000#12)) 0 0#1)'
            tag = step['addr'][2:]
            draft['params'].append(f'(htgt_{tag} : {target}.toNat % 4 = 0)')
            step['call'] = step['call'].replace('TODO(htgt)', f'htgt_{tag}')
            step['pc_val'] = target
            step.pop('pc_rw')
    spec_text = json.dumps(draft, indent=2, ensure_ascii=False) + '\n'
    if 'TODO' in spec_text:
        raise ValueError('unfilled pilot residue')
    result[ROOT / f'scripts/syi/segments/{lower}.json'] = spec_text
    result[ROOT / f'OCaml/Vm/Sim/{stem}Segment.lean'] = SegmentEmitter(draft).emit().replace(
        'Generated by scripts/gen_segment.py', 'GENERATED by scripts/gen_arm_pilot.py via scripts/syi/gen_segment.py')
    # The full image predicate discharges the generated local byte pins.
    lines = ['import OCaml.Vm.Platform', 'import ' + pin_module, '',
             '/-! GENERATED by scripts/gen_arm_pilot.py. Full-image projection. -/',
             'namespace OCaml.Vm.Sim', 'open Vsa.Machine', '',
             f'theorem {lower}_loaded {{c : Config}} (h : ExecutableImage c) :',
             f'    {pred} c.σ.mem := by', f'  unfold {pred} Vsa.Sim.Code.{name}Chunk0',
             '  refine ⟨' + ', '.join(['?_'] * (4 * len(insts))) + '⟩']
    for a, w, _, _ in insts:
        for k in range(4):
            offset = a + k - text_base
            byte = (w >> (8 * k)) & 255
            lines += [f'  · have hb := h.text {offset} (by decide)',
                      f'    have he : Image.textByte {offset} = (0x{byte:02x}#8) := by decide +kernel',
                      '    rw [he] at hb', '    exact hb']
    lines += ['', 'end OCaml.Vm.Sim', '']
    result[ROOT / f'OCaml/Vm/Sim/{stem}Pins.lean'] = '\n'.join(lines)
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
