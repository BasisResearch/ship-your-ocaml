#!/usr/bin/env python3
"""Generate integer binary bridges using shared stack consumption restoration."""
import argparse
import json
import re
from census import ROOT


# Semantic predicates and their native complementary branch guard.
COMPARISONS = {
    'LTINT': ('a.slt b', 'native_sge'),
    'LEINT': ('a.sle b', 'native_slt'),
    'GTINT': ('b.slt a', 'native_sge'),
    'GEINT': ('b.sle a', 'native_slt'),
    'ULTINT': ('a.ult b', 'native_uge'),
    'UGEINT': ('b.ule a', 'native_ult'),
}


def tagged(expression):
    return re.sub(r'\b(a|b)\b', lambda m: '(tag64 m)' if m[0] == 'a' else '(tag64 n)', expression)


def outputs():
    arms = json.loads((ROOT / 'results/census.json').read_text())['caml_interprete']['arms']
    result = {}
    specs = [
        ('ADDINT', 'Addint', 'm + n', 'tag64 m - 1#64 + tag64 n', 'tag_add'),
        ('SUBINT', 'Subint', 'm - n', 'tag64 m + 1#64 - tag64 n', 'tag_sub'),
        ('ANDINT', 'Andint', 'untag (tag64 m &&& tag64 n)', 'tag64 m &&& tag64 n', None),
        ('ORINT', 'Orint', 'untag (tag64 m ||| tag64 n)', 'tag64 m ||| tag64 n', None),
        ('XORINT', 'Xorint', 'untag ((tag64 m ^^^ tag64 n) ||| 1#64)', '(tag64 m ^^^ tag64 n) ||| 1#64', None),
        ('LSLINT', 'Lslint', 'untag (((tag64 m - 1#64) <<< (n.toNat % 64)) + 1#64)', '((tag64 m - 1#64) <<< (n.toNat % 64)) + 1#64', None),
        ('LSRINT', 'Lsrint', 'untag ((tag64 m >>> (n.toNat % 64)) ||| 1#64)', '(tag64 m >>> (n.toNat % 64)) ||| 1#64', None),
        ('ASRINT', 'Asrint', 'untag ((tag64 m).sshiftRight (n.toNat % 64) ||| 1#64)', '(tag64 m).sshiftRight (n.toNat % 64) ||| 1#64', None),
    ]
    for op in COMPARISONS:
        for truth in [True, False]:
            specs.append((op, op.title() + ('True' if truth else 'False'),
                          '1#63' if truth else '0#63', '3#64' if truth else '1#64', None))
    for op, stem, calc, expression, arithmetic in specs:
        comparison = op in COMPARISONS
        truth = stem.endswith('True')
        lower = op.lower() + (('_true' if truth else '_false') if comparison else '')
        entry = arms[op]['addr']
        segment = json.loads((ROOT / f'scripts/syi/segments/{lower}.json').read_text())
        values = {'x9': 'BitVec.ofNat 64 sp', 'x21': 'tag64 m',
                  'x23': 'BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64'}
        holds = {'x9': '(dp.frame.frame Register.x9 (by decide)).trans h.spReg',
                 'x21': '(dp.frame.frame Register.x21 (by decide)).trans source',
                 'x23': 'dp.nextCode'}
        regs = [p['reg'] for p in segment['pins']]
        pre_pins = ', '.join(f'⟨Register.{r}, {values[r]}⟩' for r in regs)
        pre_holds = ', '.join(holds[r] for r in regs)
        run_args = ' '.join(f'({values[r]})' for r in regs)
        final = {}
        for step in segment['steps']:
            if 'rd' in step:
                reg = step['rd']
                regs = [reg] + [r for r in regs if r != reg]
                final[reg] = step['rd_val']
        sp_index, accu_index, pc_index = (regs.index(r) for r in ['x9', 'x21', 'x8'])
        native = final['x21'].replace('(v9 + sign_extend (m := 64) (0x000#12))', 'v9')
        substitutions = {f'v{r[1:]}': f'({v})' for r, v in values.items()}
        substitutions['m0'] = 'd.σ.mem'
        native = re.sub(r'\b(v9|v21|v23|m0)\b', lambda m: substitutions[m[0]], native)
        native = re.sub(r'(?<![\w.])(shift_bits_left|shift_bits_right)\b', r'Sail.\1', native)
        retag = f'    simpa only [{arithmetic}] using value' if arithmetic else f"""    have retag : tag64 ({calc}) = ({expression}) :=
      tag_untag_odd _ (by simp [tag64])
    simpa only [retag] using value"""
        semantic = {'ADDINT': 'a + b - 1#64', 'SUBINT': 'a - b + 1#64',
                    'ANDINT': 'a &&& b', 'ORINT': 'a ||| b',
                    'XORINT': '(a ^^^ b) ||| 1#64',
                    'LSLINT': '((a - 1#64) <<< ((untag b).toNat % 64)) + 1#64',
                    'LSRINT': '(a >>> ((untag b).toNat % 64)) ||| 1#64',
                    'ASRINT': '(a.sshiftRight ((untag b).toNat % 64)) ||| 1#64',
                    **{op: item[0] for op, item in COMPARISONS.items()}}[op]
        semantic_value = tagged(semantic)
        normalize = f"""  have normalize : untag ({semantic_value}) = {calc} := by
    have word : ({semantic_value}) = ({expression}) := by
      simp only [BitVec.sub_eq_add_neg]
      ac_rfl
    rw [word, {arithmetic}, untag_tag]
  rw [normalize] at state
""" if arithmetic else ''
        if op in ('LSLINT', 'LSRINT', 'ASRINT'):
            normalize = '  simp only [untag_tag] at state\n'
        if op == 'LSLINT':
            retag = retag.replace('(by simp [tag64])', '(left_shift_odd m _)')
        shift_simp = {'LSLINT': ', shiftLeft_native', 'LSRINT': ', shiftRight_native',
                      'ASRINT': ', shiftArith_native'}.get(op, '')
        shift_import = 'import OCaml.Vm.Sim.ShiftArithmetic\n' if shift_simp else ''
        accu_proof = f"""  · have loaded : sign_extend (m := 64) (bytesT8 d.σ.mem (BitVec.ofNat 64 sp).toNat) = tag64 n := by
      simpa only [natAddress, dp.memory, word, bytesT_eight_eq, sign_extend,
        Sail.BitVec.signExtend, BitVec.signExtend_eq] using slot
    have hp : gpr after Layout.reg_accu = some ({native}) :=
      PinsHold.get post.pins ⟨{accu_index}, by simp⟩
    rw [loaded] at hp
    have value : gpr after Layout.reg_accu = some ({expression}) := by
      simpa only [show sign_extend (m := 64) (0xfff#12) = -1#64 from by decide,
        show sign_extend (m := 64) (0x001#12) = 1#64 from by decide,
        BitVec.add_neg_eq_sub{shift_simp}] using hp
{retag}"""
        guard_input = guard_proof = guard_arg = comparison_import = ''
        if comparison:
            comparison_import = 'import OCaml.Vm.Sim.ComparisonArithmetic\n'
            guard_input = f'    (test : ({semantic_value}) = {str(truth).lower()})\n'
            guard_type = next(p for p in segment['params'] if p.startswith('(hguard_')).split(': ', 1)[1][:-1]
            guard_type = guard_type.replace('(v9 + sign_extend (m := 64) (0x000#12))', 'v9')
            guard_type = re.sub(r'\b(v9|v21|v23|m0)\b', lambda m: substitutions[m[0]], guard_type)
            guard_proof = f"""  have loaded : sign_extend (m := 64) (bytesT8 d.σ.mem (BitVec.ofNat 64 sp).toNat) = tag64 n := by
    simpa only [natAddress, dp.memory, word, bytesT_eight_eq, sign_extend,
      Sail.BitVec.signExtend, BitVec.signExtend_eq] using slot
  have guard : {guard_type} := by
    rw [loaded]
    simp only [{COMPARISONS[op][1]}, test, Bool.not_{'true' if truth else 'false'}]
"""
            guard_arg = ' guard'
            accu_proof = f"""  · have hp : gpr after Layout.reg_accu = some ({native}) :=
      PinsHold.get post.pins ⟨{accu_index}, by simp⟩
    simpa only [show ({native}) = tag64 ({calc}) from by decide] using hp"""
        result[ROOT / f'OCaml/Vm/Sim/{stem}.lean'] = f'''import OCaml.Vm.Sim.StackConsume
import OCaml.Vm.Sim.BinarySemantics
{comparison_import}{shift_import}import OCaml.Vm.Sim.{stem}Segment
import OCaml.Vm.Sim.{stem}Pins

/-! GENERATED by scripts/gen_binary_arms.py. Integer binary arm. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- {op} consumes the represented top stack integer and returns its modular result.
Dispatch readiness, runtime frame and the total-read window remain explicit. -/
theorem {lower}_arm {{L : OCaml.Layout}} {{P : Prog}} {{s : St}} {{c : Config}}
    {{pl : Place}} {{cp : ChanPlace}} {{sp high : Nat}} {{m n : BitVec 63}} {{rest : List Val}}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .{op} c pl cp sp high)
    (accu : s.accu = .int m) (stack : s.stack = .int n :: rest)
    (read : ReadWindow (BitVec.ofNat 64 sp) 8)
{guard_input}    :
    ∃ c', Plus c c' ∧
      Running L P {{s with pc := s.pc + 1, accu := .int ({calc}), stack := rest}} c' := by
  have selected : s.stack[0]? = some (.int n) := by simp only [stack, List.getElem?_cons_zero]
  have source := represented_register h.accu (by rw [accu]; rfl : valWord pl s.accu = some (tag64 m))
  have slot := stack_integer_word h.toVmReprAt stack
  have natAddress : (BitVec.ofNat 64 sp).toNat = sp := by
    simpa only [Nat.mul_zero, Nat.add_zero] using stack_slot_nat h.toVmReprAt selected
  have bound : 1 ≤ s.stack.length := by simp only [stack, List.length_cons]; omega
  have result := consume_arm (pc := s.pc + 1) (count := 1) (n := {calc}) stable h bound
  simp only [stack, List.drop_succ_cons, List.drop_zero] at result
  apply result
  intro d dp
{guard_proof}  have bp : SegSt ({entry}#64)
      [{pre_pins}]
      (fun σ => Vsa.Sim.Code.Caml{stem}Loaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨{pre_holds}, trivial⟩,
      dp.good.minstret, dp.tick, {lower}_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_{lower} {run_args} d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero] at run
  obtain ⟨nb, after, _, hb, post⟩ := run read.lower read.upper read.htif{guard_arg} d bp
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨nb, after, hb, post.good, post.pcAt, ?_, ?_, ?_, hm, frame.out,
    fun r hr => frame.frame r ?_⟩
  · have hp : gpr after Layout.reg_pc = some
        (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) := PinsHold.get post.pins ⟨{pc_index}, by simp⟩
    simpa only [codePc_succ] using hp
  · have hp : gpr after Layout.reg_sp = some
        (BitVec.ofNat 64 sp + sign_extend (m := 64) (0x008#12)) := PinsHold.get post.pins ⟨{sp_index}, by simp⟩
    simpa only [show sign_extend (m := 64) (0x008#12) = 8#64 from by decide,
      Nat.mul_one, BitVec.ofNat_add] using hp
{accu_proof}
  · revert r
    decide

/-- The successful semantic step supplies the integer operands; no separate
input-shape assumptions are needed by callers of this wrapper. -/
theorem {lower}_step_arm {{L : OCaml.Layout}} {{P : Prog}} {{s s' : St}} {{c : Config}}
    {{pl : Place}} {{cp : ChanPlace}} {{sp high : Nat}}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .{op} c pl cp sp high)
    (read : ReadWindow (BitVec.ofNat 64 sp) 8)
    (step : stepI P s ⟨.{op}, []⟩ = .next s') :
    ∃ c', Plus c c' ∧ Running L P s' c' := by
  have step' : intOp s (fun a b => {semantic}) = .next s' := step
  obtain ⟨m, n, rest, accu, stack, state⟩ := intOp_next step'
{normalize}  rw [← state]
  exact {lower}_arm stable h accu stack read

end OCaml.Vm.Sim
''' 
        if comparison:
            path = ROOT / f'OCaml/Vm/Sim/{stem}.lean'
            result[path] = result[path].split('/-- The successful semantic step')[0] + 'end OCaml.Vm.Sim\n'
    result.update(comparison_outputs())
    return result


def comparison_outputs():
    result = {}
    for op, (semantic, _) in COMPARISONS.items():
        stem, lower = op.title(), op.lower()
        value = tagged(semantic)
        result[ROOT / f'OCaml/Vm/Sim/{stem}.lean'] = f"""import OCaml.Vm.Sim.{stem}True
import OCaml.Vm.Sim.{stem}False

/-! GENERATED by scripts/gen_binary_arms.py. Integer comparison composition. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine
open OCaml.Vm.Primitives

/-- Both generated native paths implement the successful {op} semantic step. -/
theorem {lower}_step_arm {{L : OCaml.Layout}} {{P : Prog}} {{s s' : St}} {{c : Config}}
    {{pl : Place}} {{cp : ChanPlace}} {{sp high : Nat}}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .{op} c pl cp sp high)
    (read : ReadWindow (BitVec.ofNat 64 sp) 8)
    (step : stepI P s ⟨.{op}, []⟩ = .next s') :
    ∃ c', Plus c c' ∧ Running L P s' c' := by
  have step' : cmpOp s (fun a b => {semantic}) = .next s' := step
  obtain ⟨m, n, rest, accu, stack, state⟩ := cmpOp_next step'
  cases test : ({value}) with
  | false =>
    simp only [test, Val.ofBool] at state
    rw [← state]
    exact {lower}_false_arm stable h accu stack read test
  | true =>
    simp only [test, Val.ofBool] at state
    rw [← state]
    exact {lower}_true_arm stable h accu stack read test

end OCaml.Vm.Sim
"""
    return result


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    for p, text in outputs().items():
        if args.check:
            if not p.exists() or p.read_text() != text:
                raise SystemExit(f'binary arm drift: {p.relative_to(ROOT)}')
        else:
            p.write_text(text)
    print('Binary arm bridges current')
