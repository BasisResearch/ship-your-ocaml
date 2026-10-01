#!/usr/bin/env python3
"""Generate PUSH families through shared write restoration and payload reads."""
import argparse
import json
from census import ROOT


def outputs():
    result = {}
    specs = [('PUSH', 'keep', 0), ('PUSHACC0', 'keep', 0)]
    specs += [(f'PUSHACC{n}', 'load', n - 1) for n in range(1, 8)]
    specs += [(f'PUSHCONST{n}', 'const', n) for n in range(4)]
    specs += [(f'PUSHENVACC{n}', 'env', n) for n in range(1, 5)]
    specs += [(f'PUSHOFFSETCLOSURE{s}', 'closure', n) for s, n in [('M3', -3), ('0', 0), ('3', 3)]]
    specs += [('PUSHCONSTINT', 'operand_const', 0), ('PUSHOFFSETCLOSURE', 'operand_closure', 0),
              ('PUSHENVACC', 'operand_env', 0), ('PUSHACC', 'operand_stack', 0),
              ('PUSHATOM0', 'atom', 0), ('PUSHATOM', 'operand_atom', 0),
              ('PUSHGETGLOBAL', 'operand_global', 0)]
    for op, kind, n in specs:
        stem, lower = op.title(), op.lower()
        spec = json.loads((ROOT / f'scripts/syi/segments/{lower}.json').read_text())
        lo = int(spec['entry'], 16)
        hi = max(int(s['addr'], 16) for s in spec['steps']) + 4
        regs = [p['reg'] for p in spec['pins']]
        for step in spec['steps']:
            if step.get('rd'):
                regs = [step['rd']] + [r for r in regs if r != step['rd']]
        sp_pin, pc_pin, accu_pin = (regs.index(r) for r in ['x9', 'x8', 'x21'])
        result_val = 'v' if kind in ('load', 'env') else f'.int ({n}#63)' if kind == 'const' else 's.accu'
        extra_binders = ' {v : Val}' if kind == 'load' else ''
        extra_inputs = f'''    (selected : s.stack[{n}]? = some v)
    (read : RamReadAt (sp + 8 * {n}) 8)
''' if kind == 'load' else ''
        value = f'(h.stack.2 {n} v selected)' if kind == 'load' else 'rfl' if kind == 'const' else 'pushed'
        root = '(stack_value_root selected)' if kind == 'load' else '(fun _ hl => by cases hl)' if kind == 'const' else '(fun l hl => Live.root (by simp [roots]) hl)'
        load_setup = f'''  have address : BitVec.ofNat 64 sp + sign_extend (m := 64) (0x{8*n:03x}#12) =
      BitVec.ofNat 64 (sp + 8 * {n}) := by
    rw [BitVec.ofNat_add]
    rfl
  have loaded := space.stack_read selected (memoryEq.trans
    (congrArg (fun m => writeLog m (pushLog sp w)) dp.memory))
''' if kind == 'load' else ''
        load_simp = ', address, read.toNat' if kind == 'load' else ''
        load_args = '\n    read.lower read.upper read.htif' if kind == 'load' else ''
        if kind == 'load':
            accu = f'''  · have hp : gpr after Layout.reg_accu = some
        (sign_extend (m := 64) (bytesT8 memoryAfter (sp + 8 * {n}))) :=
      PinsHold.get post.pins ⟨{accu_pin}, by simp⟩
    simpa only [loaded] using hp'''
        elif kind == 'const':
            accu = f'''  · have hp : gpr after Layout.reg_accu = some
        ((0#64) + sign_extend (m := 64) (0x{2*n+1:03x}#12)) :=
      PinsHold.get post.pins ⟨{accu_pin}, by simp⟩
    simpa only [show (0#64) + sign_extend (m := 64) (0x{2*n+1:03x}#12) = tag64 ({n}#63) from by decide] using hp'''
        else:
            accu = f'  · exact PinsHold.get post.pins ⟨{accu_pin}, by simp⟩'
        extra_import, value_setup = '', ''
        advance = 1
        if kind in ('env', 'operand_env', 'operand_global'):
            source_expr = 'P.globals' if kind == 'operand_global' else 's.env'
            index = str(n) if kind == 'env' else 'operandWord.toInt.toNat'
            window = 'read' if kind == 'env' else 'window'
            result_val = 'v'
            extra_import = 'import OCaml.Vm.Sim.FieldRead\n'
            extra_binders = ' {l a k : Nat} {v : Val}'
            extra_inputs = f'''    (selected : FieldSelection s.heap pl {source_expr} {index} v l a k)
    ({window} : RamReadAt (a + 8 * (k + {index})) 8)
'''
            value_setup = '''  have value := FieldSelection.read h.toVmReprAt (by simp [roots]) selected
  have environment := represented_register h.env selected.sourceWord
'''
            if kind == 'operand_global':
                value_setup = '''  have value := FieldSelection.read h.toVmReprAt (by simp [roots]) selected
  have globalWord : word c Layout.sym_caml_global_data = BitVec.ofNat 64 (a + 8 * k) :=
    Option.some.inj (h.globals.symm.trans selected.sourceWord)
'''
            value, root = 'value.word', 'value.root'
            load_setup = f'''  have address : BitVec.ofNat 64 (a + 8 * k) + sign_extend (m := 64) (0x{8*n:03x}#12) =
      BitVec.ofNat 64 (a + 8 * (k + {index})) := by
    rw [show sign_extend (m := 64) (0x{8*n:03x}#12) = BitVec.ofNat 64 (8 * {index}) from by decide]
    simp only [Nat.mul_add, ← Nat.add_assoc, BitVec.ofNat_add]
'''
            load_simp = f', address, {window}.toNat'
            load_args = f'\n    {window}.lower {window}.upper {window}.htif'
            accu = f'''  · have hp : gpr after Layout.reg_accu = some
        (sign_extend (m := 64) (bytesT8 memoryAfter (a + 8 * (k + {index})))) :=
      PinsHold.get post.pins ⟨{accu_pin}, by simp⟩
    have same := selected.word_frame (payload_of_repr h.toVmReprAt) (by simp [roots])
      space.payload (hm.trans (memoryEq.trans
        (congrArg (fun m => writeLog m (pushLog sp w)) dp.memory)))
      (frame.out.trans dp.frame.out)
    have current : gpr after Layout.reg_accu = some (word after (a + 8 * (k + {index}))) := by
      simpa only [word, hm, bytesT_eight_eq, sign_extend,
        Sail.BitVec.signExtend, BitVec.signExtend_eq] using hp
    simpa only [same] using current'''
        if kind == 'closure':
            extra_import = 'import OCaml.Vm.Sim.ClosureOffset\n'
            extra_binders = ' {l a k dest : Nat}'
            extra_inputs = f'    (selected : ClosureOffset s pl ({n}) l a k dest)\n'
            value_setup = '  have environment := represented_register h.env selected.sourceWord\n'
            value, root, result_val = 'selected.resultWord', 'selected.root', '.ptr l dest'
            load_setup = f'''  have address : BitVec.ofNat 64 (a + 8 * k) + sign_extend (m := 64) (0x{(8*n)%4096:03x}#12) =
      BitVec.ofNat 64 (a + 8 * dest) := by
    rw [show sign_extend (m := 64) (0x{(8*n)%4096:03x}#12) = BitVec.ofInt 64 (8 * ({n})) from by decide]
    exact pointer_offset_word a k dest ({n}) selected.target
'''
            load_simp = ', address'
            accu = f'  · exact PinsHold.get post.pins ⟨{accu_pin}, by simp⟩'
        variable = kind.startswith('operand_')
        if variable:
            advance = 2
            extra_binders = ' {operandWord : BitVec 32}' + extra_binders
            extra_inputs = '    (operand : OperandAt P pl (s.pc + 1) operandWord)\n' + extra_inputs
            load_setup = '''  have read := space.operand_read32 h.code operand (memoryEq.trans
    (congrArg (fun m => writeLog m (pushLog sp w)) dp.memory))
'''
            load_simp = ''
            load_args = '\n    operand.geometry.lower operand.geometry.upper operand.geometry.htif'
            if kind == 'operand_const':
                extra_import = 'import OCaml.Vm.Sim.ImmediateArithmetic\n'
                result_val = '.int (BitVec.ofInt 63 operandWord.toInt)'
                value, root = 'rfl', '(fun _ hl => by cases hl)'
                accu = f'''  · have hp : gpr after Layout.reg_accu = some
        ((operandWord.signExtend 64 <<< (1 : Nat)) + 1#64) :=
      PinsHold.get post.pins ⟨{accu_pin}, by simp⟩
    simpa only [tag_word32] using hp'''
            elif kind == 'operand_closure':
                extra_import = 'import OCaml.Vm.Sim.ClosureOffset\n'
                extra_binders += ' {l a k dest : Nat}'
                extra_inputs += '    (selected : ClosureOffset s pl operandWord.toInt l a k dest)\n'
                value_setup = '  have environment := represented_register h.env selected.sourceWord\n'
                value, root, result_val = 'selected.resultWord', 'selected.root', '.ptr l dest'
                load_setup += '''  have address : Sail.shift_bits_left (sign_extend (m := 64) operandWord)
      (Sail.BitVec.extractLsb (0x03#6) 5 0) + BitVec.ofNat 64 (a + 8 * k) =
      BitVec.ofNat 64 (a + 8 * dest) := by
    rw [signed_index_word, BitVec.add_comm]
    exact pointer_offset_word a k dest operandWord.toInt selected.target
'''
                load_simp = ', address'
                accu = f'  · exact PinsHold.get post.pins ⟨{accu_pin}, by simp⟩'
            elif kind in ('operand_env', 'operand_stack', 'operand_global'):
                extra_import += 'import OCaml.Vm.Sim.IndexWord\n'
                extra_inputs += '    (nonnegative : 0 ≤ operandWord.toInt)\n'
                if kind == 'operand_stack':
                    extra_binders += ' {v : Val}'
                    extra_inputs += '''    (selected : (s.accu :: s.stack)[operandWord.toInt.toNat]? = some v)
    (window : RamReadAt (sp - 8 + 8 * operandWord.toInt.toNat) 8)
'''
                    value, root, result_val = '(pushed_value h.toVmReprAt pushed selected)', '(pushed_root selected)', 'v'
                    base, addr = 'sp - 8', 'sp - 8 + 8 * operandWord.toInt.toNat'
                    load_setup += '''  have loaded := space.pushed_read selected (memoryEq.trans
    (congrArg (fun m => writeLog m (pushLog sp w)) dp.memory))
'''
                    accu = f'''  · have hp : gpr after Layout.reg_accu = some
        (sign_extend (m := 64) (bytesT8 memoryAfter ({addr}))) :=
      PinsHold.get post.pins ⟨{accu_pin}, by simp⟩
    simpa only [loaded] using hp'''
                    swap = ''
                else:
                    base, addr = 'a + 8 * k', 'a + 8 * (k + operandWord.toInt.toNat)'
                    swap = f''',
    show BitVec.ofNat 64 (8 * operandWord.toInt.toNat) + BitVec.ofNat 64 ({base}) =
      BitVec.ofNat 64 ({base}) + BitVec.ofNat 64 (8 * operandWord.toInt.toNat) from BitVec.add_comm _ _'''
                load_setup += f'''  have address : BitVec.ofNat 64 ({base}) + BitVec.ofNat 64 (8 * operandWord.toInt.toNat) =
      BitVec.ofNat 64 ({addr}) := by
    simp only [Nat.mul_add, ← Nat.add_assoc, BitVec.ofNat_add]
'''
                load_simp = f''', show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, index_word operandWord nonnegative{swap}, address, window.toNat'''
                if kind == 'operand_global':
                    ea = [p for p in spec['params'] if p.startswith('(hlo_')][2].split(' ≤ ', 1)[1].removesuffix('.toNat)')
                    load_setup += f'''  have globalWindow : RamReadAt Layout.sym_caml_global_data 8 := ⟨by decide, by decide, by decide⟩
  have globalAddress : {ea} = BitVec.ofNat 64 Layout.sym_caml_global_data := by decide
  have globalRead := (space.word_read space.payload.globals (memoryEq.trans
    (congrArg (fun m => writeLog m (pushLog sp w)) dp.memory))).trans globalWord
'''
                    load_simp = ', globalAddress, globalWindow.toNat, globalRead' + load_simp
                    load_args += '\n    globalWindow.lower globalWindow.upper globalWindow.htif'
                load_args += '\n    window.lower window.upper window.htif'
        if kind in ('atom', 'operand_atom'):
            extra_import = 'import OCaml.Vm.Sim.IndexWord\n'
            tag = 'operandWord.toInt.toNat' if variable else '0'
            result_val = f'.atom ({tag})'
            value, root = f'(atom_word_of_binding h.atomBase ({tag}))', '(fun _ hl => by cases hl)'
            ea = [p for p in spec['params'] if p.startswith('(hlo_')][-1].split(' ≤ ', 1)[1].removesuffix('.toNat)')
            load_setup += f'''  have table : RamReadAt Layout.sym_caml_atom_table 8 := ⟨by decide, by decide, by decide⟩
  have address : {ea} = BitVec.ofNat 64 Layout.sym_caml_atom_table := by decide
  have tableRead := space.word_read space.payload.atomBase (memoryEq.trans
    (congrArg (fun m => writeLog m (pushLog sp w)) dp.memory))
'''
            load_simp = ', address, table.toNat, tableRead, show sign_extend (m := 64) (0x008#12) = 8#64 from by decide'
            if variable:
                extra_inputs += '    (nonnegative : 0 ≤ operandWord.toInt)\n'
                load_simp += ', atom_index_offset operandWord nonnegative'
            load_args += '\n    table.lower table.upper table.htif'
            accu = f'''  · exact PinsHold.get post.pins ⟨{accu_pin}, by simp⟩'''
        words = {'x9': 'BitVec.ofNat 64 sp', 'x21': 'w',
                 'x8': 'BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)',
                 'x23': 'BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64',
                 'x25': 'BitVec.ofNat 64 (a + 8 * k)'}
        holds = {'x9': '(dp.frame.frame Register.x9 (by decide)).trans h.spReg',
                 'x8': '(dp.frame.frame Register.x8 (by decide)).trans h.pc',
                 'x21': '(dp.frame.frame Register.x21 (by decide)).trans source',
                 'x23': 'dp.nextCode',
                 'x25': '(dp.frame.frame Register.x25 (by decide)).trans environment'}
        inputs = [p['reg'] for p in spec['pins']]
        pre_pins = ',\n       '.join(f'⟨Register.{r}, {words[r]}⟩' for r in inputs)
        pre_holds = ',\n       '.join(holds[r] for r in inputs)
        run_args = ' '.join(f'({words[r]})' for r in inputs)
        run_application = f'''  obtain ⟨nb, after, _, hb, post⟩ := run space.window.lower space.window.upper
    space.window.htif space.window.aligned (by simpa only [space.toNat] using code)
    memoryAfter (by rw [space.toNat]; exact memoryEq){load_args} d bp'''
        pc_proof = f'''  · have hp : gpr after Layout.reg_pc = some
        ((BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) + sign_extend (m := 64) (0x000#12)) :=
      PinsHold.get post.pins ⟨{pc_pin}, by simp⟩
    simpa only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
      BitVec.add_zero, codePc_succ] using hp'''
        if variable or kind == 'atom':
            operand_simps = '''show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    codePc_succ, operand.geometry.toNat, read''' if variable else 'push_address space.room'
            run_application = f'''  have body := run space.window.lower space.window.upper
    space.window.htif space.window.aligned (by simpa only [space.toNat] using code)
    memoryAfter (by rw [space.toNat]; exact memoryEq)
  simp only [{operand_simps}{load_simp}] at body
  obtain ⟨nb, after, _, hb, post⟩ := body{load_args} d bp'''
            load_simp = ''
        if variable:
            pc_proof = f'''  · have hp : gpr after Layout.reg_pc = some
        (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64) :=
      PinsHold.get post.pins ⟨{pc_pin}, by simp⟩
    simpa only [show BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64 =
      BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 2)) from codePc_add pl s.pc 2] using hp'''
        result[ROOT / f'OCaml/Vm/Sim/{stem}.lean'] = f'''import OCaml.Vm.Sim.StackStore
{extra_import}import OCaml.Vm.Sim.{stem}Segment
import OCaml.Vm.Sim.{stem}Pins

/-! GENERATED by scripts/gen_push_arms.py. Represented stack write. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- {op} saves the accumulator and restores the complete represented result.
Stack placement/separation and runtime window stability remain explicit obligations. -/
theorem {lower}_arm {{L : OCaml.Layout}} {{P : Prog}} {{s : St}} {{c : Config}}
    {{pl : Place}} {{cp : ChanPlace}} {{sp high : Nat}} {{w : BitVec 64}}{extra_binders}
    (stable : WindowStable L.runtimeOk [⟨sp - 8, sp⟩])
    (h : ArmInput L P s .{op} c pl cp sp high)
    (space : PushWriteOk P s c pl cp sp w)
{extra_inputs}    (pushed : valWord pl s.accu = some w) :
    ∃ c', Plus c c' ∧ Running L P
      {{s with pc := s.pc + {advance}, accu := {result_val}, stack := s.accu :: s.stack}} c' := by
  have source := represented_register h.accu pushed
{value_setup}  apply push_value_arm stable h space pushed {value} {root}
  intro d dp
  have code : sp - 8 + 8 ≤ 0x{lo:x} ∨ 0x{hi:x} ≤ sp - 8 :=
    space.code (by decide) (by decide)
  obtain ⟨memoryAfter, memoryEq⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeLog d.σ.mem (pushLog sp w) := ⟨_, rfl⟩
{load_setup}  have bp : SegSt ({spec['entry']}#64)
      [{pre_pins}]
      (fun σ => Vsa.Sim.Code.Caml{stem}Loaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨{pre_holds}, trivial⟩,
      dp.good.minstret, dp.tick, {lower}_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_{lower} {run_args} d.σ.mem d.σ
  simp only [push_address space.room{load_simp}] at run
{run_application}
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨nb, after, hb, post.good, post.pcAt, ?_, ?_, ?_, hm.trans memoryEq, frame.out, ?_⟩
{pc_proof}
  · exact PinsHold.get post.pins ⟨{sp_pin}, by simp⟩
{accu}
  · intro r hr
    exact frame.frame r (by revert r; decide)

end OCaml.Vm.Sim
'''
    return result


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    for p, text in outputs().items():
        if args.check:
            if not p.exists() or p.read_text() != text:
                raise SystemExit(f'push arm drift: {p.relative_to(ROOT)}')
        else:
            p.write_text(text)
    print('Push arm bridges current')
