#!/usr/bin/env python3
"""Indexed/global mutation callers over the shared represented barrier contract."""
import argparse
import json
import sys
from gen_arm_pilot import ROOT
sys.path.insert(0, str(ROOT / 'scripts/syi'))
from gen_segment import SegmentEmitter


def outputs():
    result = {}
    for opcode, stem in [('SETFIELD', 'Setfield'), ('SETGLOBAL', 'Setglobal'), ('SETVECTITEM', 'Setvectitem')]:
        lower = opcode.lower()
        glob, vec = opcode == 'SETGLOBAL', opcode == 'SETVECTITEM'
        spec = json.loads((ROOT / f'scripts/syi/segments/{lower}_prefix.json').read_text())
        em = SegmentEmitter(spec)
        em.emit()
        pins = {r: i for i, (r, _) in enumerate(em.pins)}
        ra = json.loads((ROOT / f'scripts/syi/segments/{lower}_suffix.json').read_text())['entry']
        delta, drop = (1, 16) if vec else ((2, 0) if glob else (2, 8))
        code = 'BitVec.ofNat 64 (pl.codeBase + 4 * '+ ('s.pc' if glob else f'(s.pc + {delta})') + ')'
        slot = f'(BitVec.ofNat 64 (8 * {"n.toNat" if vec else "ofs.toInt.toNat"}) + base)'
        index = 'n.toNat' if vec else 'ofs.toInt.toNat'
        source = 'P.globals' if glob else 's.accu'
        val = 's.accu' if glob else 'v'
        final_stack = 's.stack' if glob else 'rest'
        target = f'{{s with pc := s.pc + {delta}, accu := .unit, heap := heap, stack := {final_stack}}}'
        target_sp = 'sp' if glob else f'(sp + {drop})'
        implicit = ('{n : BitVec 63}' if vec else '{ofs : BitVec 32}') + ('' if glob else ' {v : Val} {rest : List Val}')
        premises = []
        if not vec:
            premises += ['(operand : OperandAt P pl (s.pc + 1) ofs)', '(nonnegative : 0 ≤ ofs.toInt)']
        premises += [f'(source : valWord pl {source} = some base)']
        if not glob:
            premises += [f'(stack : s.stack = {".int n :: " if vec else ""}v :: rest)']
        premises += [f'(encoded : valWord pl {val} = some value)']
        if not glob:
            premises += ['(stackRead : RamReadAt sp 8)']
        if vec:
            premises += ['(valueRead : RamReadAt (sp + 8) 8)']
        args = ' '.join(p.split()[0][1:] for p in premises)
        premises = '\n    '.join(premises)
        # Native source pins and corresponding represented/dispatch observations.
        vals = {'x8': 'BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)', 'x9': 'BitVec.ofNat 64 sp',
                'x21': 'value' if glob else 'base', 'x23': '(BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64)'}
        hs = {'x8': '(dp.frame.frame Register.x8 (by decide)).trans h.pc',
              'x9': '(dp.frame.frame Register.x9 (by decide)).trans h.spReg',
              'x21': '(dp.frame.frame Register.x21 (by decide)).trans accu', 'x23': 'dp.nextCode'}
        bp_pins = ', '.join(f'⟨Register.{p["reg"]}, {vals[p["reg"]]}⟩' for p in spec['pins'])
        bp_proof = ', '.join(hs[p['reg']] for p in spec['pins']) + ', trivial'
        native_args = ' '.join(f'({vals[p["reg"]]})' for p in spec['pins'])
        prep = [f'  have accu := represented_register h.accu {"encoded" if glob else "source"}']
        norm = [f'show sign_extend (m := 64) (0x{n:03x}#12) = {n}#64 from by decide' for n in [0,4,8]]
        norm += ['BitVec.add_zero', 'codePc_succ']
        run_args = []
        if not vec:
            prep += ['  have codeRead := operand.read32 h.code dp.memory']
            norm += ['operand.geometry.toNat', 'codeRead', 'index_word ofs nonnegative']
            run_args += ['operand.geometry.lower operand.geometry.upper operand.geometry.htif (sign_extend (m := 64) ofs) rfl']
        if glob:
            address = next(p for p in spec['params'] if p.startswith('(hlo_') and '0x800025b0' in p).split(' ≤ ',1)[1].removesuffix('.toNat)')
            prep += [f'''  have globalAddress : {address} = BitVec.ofNat 64 Layout.sym_caml_global_data := by decide
  have globalWindow : RamReadAt Layout.sym_caml_global_data 8 := ⟨by decide, by decide, by decide⟩
  have globalWord : word c Layout.sym_caml_global_data = base := Option.some.inj (h.globals.symm.trans source)
  have globalRead : sign_extend (m := 64) (bytesT8 d.σ.mem Layout.sym_caml_global_data) = base := by
    simpa only [dp.memory, word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] using globalWord''']
            norm += ['globalAddress', 'globalWindow.toNat']
            run_args += ['globalWindow.lower globalWindow.upper globalWindow.htif base (by rw [globalRead])']
        else:
            val_index, val_addr = (1, 'sp + 8') if vec else (0, 'sp')
            prep += [f'''  have valueWord : word c ({val_addr}) = value := by
    have repr := h.stack.2 {val_index} v (by simp [stack])
    simpa only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] using Option.some.inj (repr.symm.trans encoded)
  have valueReadback : sign_extend (m := 64) (bytesT8 d.σ.mem ({val_addr})) = value := by
    simpa only [dp.memory, word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] using valueWord''']
            norm += ['stackRead.toNat']
            if vec:
                prep += ['''  have indexWord := stack_integer_word h.toVmReprAt stack
  have indexRead : sign_extend (m := 64) (bytesT8 d.σ.mem sp) = tag64 n := by
    simpa only [dp.memory, word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] using indexWord
  have stackNext : BitVec.ofNat 64 sp + 8#64 = BitVec.ofNat 64 (sp + 8) := by simp [BitVec.ofNat_add]''']
                norm += ['stackNext', 'valueRead.toNat', 'value_index_word n']
                run_args += ['stackRead.lower stackRead.upper stackRead.htif (tag64 n) (by rw [indexRead])',
                             'valueRead.lower valueRead.upper valueRead.htif value (by rw [valueReadback])']
            else:
                run_args += ['stackRead.lower stackRead.upper stackRead.htif value (by rw [valueReadback])']
        norm += [f'show BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64 = BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 2)) from codePc_add pl s.pc 2']
        norm_text = ',\n    '.join(norm)
        obs = []
        for reg, field, expr in [('x8','code',code), ('x9','stack','BitVec.ofNat 64 sp'), ('x10','slot',slot), ('x11','value','value')]:
            if reg in pins:
                layout_reg = {'x8': '8', 'x9': 'Layout.reg_sp', 'x10': '10', 'x11': '11'}[reg]
                obs += [f'''    · have observed := PinsHold.get post.pins ⟨{pins[reg]}, by simp⟩
      change gpr after {layout_reg} = some _ at observed
      simp only [Fin.getElem_fin, List.getElem_cons_zero, List.getElem_cons_succ] at observed
      simpa only [{norm_text}] using observed''']
            else:
                old = 'h.pc' if reg == 'x8' else 'h.spReg'
                obs += [f'    · exact (frame.frame Register.{reg} (by decide)).trans ((dp.frame.frame Register.{reg} (by decide)).trans {old})']
        code_fit = 'codePc_add pl s.pc 2' if glob else 'rfl'
        stack_fit = 'rfl' if glob else 'by simp [BitVec.ofNat_add]'
        # Explicit source semantic equation and instruction operands.
        bc_args = '[]' if vec else '[ofs.toInt]'
        simp_step = 'stepI, ' + ('' if glob else 'stack, ') + 'update, opt, St.adv'
        # index operands are guarded in stepI (negative → unsupported); SETVECTITEM's index is a stack value
        step_term = 'step' if vec else 'Res.unguard step'
        result[ROOT / f'OCaml/Vm/Sim/{stem}.lean'] = f'''import OCaml.Vm.Sim.ModifyCall
import OCaml.Vm.Sim.StackAcc
import OCaml.Vm.Sim.IndexWord
import OCaml.Vm.Sim.ValueIndex
import OCaml.Vm.Sim.{stem}PrefixSegment
import OCaml.Vm.Sim.{stem}PrefixPins
import OCaml.Vm.Sim.{stem}Return
import Vsa.Sim.DeriveCallSeg
import OCaml.Run.Machine

/-! GENERATED by scripts/gen_modify_indexed.py. Indexed mutation through a represented barrier summary. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- Establish the represented call input from the native indexed setup. -/
theorem {lower}_setup {{L : OCaml.Layout}} {{P : Prog}} {{s : St}} {{c d : Config}}
    {{pl : Place}} {{cp : ChanPlace}} {{sp high : Nat}} {{base value : BitVec 64}} {implicit}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s .{opcode} c pl cp sp high)
    {premises}
    (dp : DispatchPost c .{opcode} (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d) :
    ∃ count after, StepsN count d after ∧ ModifyInput L P s pl cp sp high 8
      ({ra}#64) ({code}) (BitVec.ofNat 64 sp) {slot} value after := by
{chr(10).join(prep)}
  have bp : SegSt ({spec['entry']}#64) [{bp_pins}]
      (fun σ => Vsa.Sim.Code.Caml{stem}PrefixLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨{bp_proof}⟩, dp.good.minstret, dp.tick,
      {lower}_prefix_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have native := tr_{lower}_prefix {native_args} d.σ.mem d.σ
  simp only [{norm_text}] at native
  obtain ⟨count, after, _, run, post⟩ := native {' '.join(run_args)} d (by simpa only [codePc_succ] using bp)
  obtain ⟨_, memory, frame⟩ := post.extra
  have setup : ModifySetup c 8 ({ra}#64) ({code}) (BitVec.ofNat 64 sp) {slot} value after := by
    refine {{
      good := post.good, image := image_of_writeLog (log := []) (dp.image h.dispatch.image) ⟨trivial, trivial⟩ memory,
      minstret := post.good.minstret, raReg := PinsHold.get post.pins ⟨{pins['x1']}, by simp⟩,
      aligned := by decide, tick := post.tick, entry := post.pcAt,
      code := ?_, stack := ?_, slot := ?_, value := ?_,
      memory := memory.trans dp.memory, output := frame.out.trans dp.frame.out,
      preserved := fun r hr => (frame.frame r (by revert r; decide)).trans (dp.frame.frame r (by revert r; decide)) }}
{chr(10).join(obs)}
  exact ⟨count, after, run, modify_input stable h.toVmReprAt h.running.platform h.dispatch.loop h.geometry h.native setup⟩

/-- Compose native setup, the GC lane's named barrier, and native represented return. -/
theorem {lower}_arm {{L : OCaml.Layout}} {{P : Prog}} {{s : St}} {{c : Config}}
    {{pl : Place}} {{cp : ChanPlace}} {{sp high : Nat}} {{base value : BitVec 64}} {implicit} {{heap : Heap}}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s .{opcode} c pl cp sp high)
    {premises}
    (callee : ModifyCallee L P s {target} pl cp sp {target_sp} high 8
      ({ra}#64) ({code}) (BitVec.ofNat 64 sp) {slot} value) :
    ∃ after, Plus c after ∧ Running L P {target} after := by
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨count, call, run, input⟩ := {lower}_setup stable h {args} dp
  have start : Vsa.Logic.Triple (fun e => e = d)
      (fun e => PCAt (0x8000a9a8#64) e ∧ ModifyInput L P s pl cp sp high 8
        ({ra}#64) ({code}) (BitVec.ofNat 64 sp) {slot} value e) := by
    rintro e rfl
    exact ⟨call, run.toSteps, input.entry, input⟩
  obtain ⟨after, run, result⟩ := (callSeg start callee.summary.run
    ({lower}_return stable ({code_fit}) ({stack_fit}))) d rfl
  exact ⟨_, after, run.toN_of_stepsField, result⟩

/-- Match the actual successful bytecode field update to the represented arm. -/
theorem {lower}_step_arm {{L : OCaml.Layout}} {{P : Prog}} {{s s' : St}} {{c : Config}}
    {{pl : Place}} {{cp : ChanPlace}} {{sp high : Nat}} {{base value : BitVec 64}} {implicit} {{heap : Heap}}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s .{opcode} c pl cp sp high)
    {premises}
    (callee : ModifyCallee L P s {target} pl cp sp {target_sp} high 8
      ({ra}#64) ({code}) (BitVec.ofNat 64 sp) {slot} value)
    (update : setField? s.heap {source} {index} {val} = some heap)
    (step : stepI P s ⟨.{opcode}, {bc_args}⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have state : {target} = s' := by
    simpa [{simp_step}] using {step_term}
  rw [← state]
  exact {lower}_arm stable h {args} callee

end OCaml.Vm.Sim
'''
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    drift = []
    for path, content in outputs().items():
        if args.check:
            if not path.exists() or path.read_text() != content:
                drift.append(str(path.relative_to(ROOT)))
        else:
            path.write_text(content)
    if drift:
        sys.exit('Indexed modify caller drift: ' + ', '.join(drift))
    print('Indexed modify caller adapters current')
