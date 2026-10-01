#!/usr/bin/env python3
"""Generate fixed PUSH families through shared write restoration and payload reads."""
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
        if kind == 'env':
            extra_import = 'import OCaml.Vm.Sim.FieldRead\n'
            extra_binders = ' {l a k : Nat} {v : Val}'
            extra_inputs = f'''    (selected : FieldSelection s.heap pl s.env {n} v l a k)
    (read : RamReadAt (a + 8 * (k + {n})) 8)
'''
            value_setup = '''  have value := FieldSelection.read h.toVmReprAt (by simp [roots]) selected
  have environment := represented_register h.env selected.sourceWord
'''
            value, root = 'value.word', 'value.root'
            load_setup = f'''  have address : BitVec.ofNat 64 (a + 8 * k) + sign_extend (m := 64) (0x{8*n:03x}#12) =
      BitVec.ofNat 64 (a + 8 * (k + {n})) := by
    rw [show sign_extend (m := 64) (0x{8*n:03x}#12) = BitVec.ofNat 64 (8 * {n}) from by decide]
    simp only [Nat.mul_add, ← Nat.add_assoc, BitVec.ofNat_add]
'''
            load_simp = ', address, read.toNat'
            load_args = '\n    read.lower read.upper read.htif'
            accu = f'''  · have hp : gpr after Layout.reg_accu = some
        (sign_extend (m := 64) (bytesT8 memoryAfter (a + 8 * (k + {n})))) :=
      PinsHold.get post.pins ⟨{accu_pin}, by simp⟩
    have same := selected.word_frame (payload_of_repr h.toVmReprAt) (by simp [roots])
      space.payload (hm.trans (memoryEq.trans
        (congrArg (fun m => writeLog m (pushLog sp w)) dp.memory)))
      (frame.out.trans dp.frame.out)
    have current : gpr after Layout.reg_accu = some (word after (a + 8 * (k + {n}))) := by
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
        words = {'x9': 'BitVec.ofNat 64 sp', 'x21': 'w',
                 'x23': 'BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64',
                 'x25': 'BitVec.ofNat 64 (a + 8 * k)'}
        holds = {'x9': '(dp.frame.frame Register.x9 (by decide)).trans h.spReg',
                 'x21': '(dp.frame.frame Register.x21 (by decide)).trans source',
                 'x23': 'dp.nextCode',
                 'x25': '(dp.frame.frame Register.x25 (by decide)).trans environment'}
        inputs = [p['reg'] for p in spec['pins']]
        pre_pins = ',\n       '.join(f'⟨Register.{r}, {words[r]}⟩' for r in inputs)
        pre_holds = ',\n       '.join(holds[r] for r in inputs)
        run_args = ' '.join(f'({words[r]})' for r in inputs)
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
      {{s with pc := s.pc + 1, accu := {result_val}, stack := s.accu :: s.stack}} c' := by
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
  obtain ⟨nb, after, _, hb, post⟩ := run space.window.lower space.window.upper
    space.window.htif space.window.aligned (by simpa only [space.toNat] using code)
    memoryAfter (by rw [space.toNat]; exact memoryEq){load_args} d bp
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨nb, after, hb, post.good, post.pcAt, ?_, ?_, ?_, hm.trans memoryEq, frame.out, ?_⟩
  · have hp : gpr after Layout.reg_pc = some
        ((BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) + sign_extend (m := 64) (0x000#12)) :=
      PinsHold.get post.pins ⟨{pc_pin}, by simp⟩
    simpa only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
      BitVec.add_zero, codePc_succ] using hp
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
