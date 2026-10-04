#!/usr/bin/env python3
"""Instantiate the zero/nonzero CLOSURE prefixes from their generated register order."""
import argparse
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent

def render(kind, recursive=False):
    more=kind=='more';stem=kind.title()
    family='closurerec' if recursive else 'closure'
    native='Closurerec' if recursive else 'Closure'
    opcode=family.upper()
    spec=json.loads((ROOT/f'scripts/syi/segments/{family}_prefix_{kind}.json').read_text())
    regs=[p['reg'] for p in spec['pins']]
    vals={'x8':'(BitVec.ofNat 64 (pl.codeBase + 4 * s.pc))','x9':'(BitVec.ofNat 64 sp)','x21':'accu'}
    proofs={'x8':'(dp.frame.frame Register.x8 (by decide)).trans h.pc','x9':'(dp.frame.frame Register.x9 (by decide)).trans h.spReg','x21':'(dp.frame.frame Register.x21 (by decide)).trans (represented_register h.accu value)'}
    pins=', '.join(f'⟨Register.{r}, {vals[r]}⟩' for r in regs);args=' '.join(vals[r] for r in regs);pinproof=', '.join(proofs[r] for r in regs)
    for st in spec['steps']:
        r=st.get('rd')
        if r:regs=[r]+[x for x in regs if x!=r]
    get=lambda r:f'PinsHold.get post.pins ⟨{regs.index(r)}, by simp⟩'
    setup='''  have push := space.write branch
  have address := push_address (space.room branch)
  have member : (sp - 8, 8, accu) ∈ closurePushLog sp count.toInt.toNat accu := by
    simp only [closurePushLog, branch, ite_true, List.mem_singleton]
  have guard : zopz0zKzJ_s (0#64) (BitVec.ofNat 64 count.toInt.toNat) = false :=
    return_more_guard count.toInt.toNat branch (by omega)
  have nurseryGuard : zopz0zKzJ_s (254#64) (BitVec.ofNat 64 count.toInt.toNat) = true := by
    unfold zopz0zKzJ_s
    rw [nat64_toInt count.toInt.toNat (by omega)]
    exact decide_eq_true (by change (254 : Int) ≥ (count.toInt.toNat : Int); omega)
  obtain ⟨nextMemory, written⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 d.σ.mem (sp - 8) (sdData_val accu) := ⟨_, rfl⟩
''' if more else '''  have empty : ¬ 0 < count.toInt.toNat := by omega
  have guard : zopz0zKzJ_s (0#64) (BitVec.ofNat 64 count.toInt.toNat) = true := by rw [branch]; decide
'''
    runfinish='''  obtain ⟨nb, after, _, steps, post⟩ := first guard push.lower push.upper push.htif push.aligned
    (image_entry_code space.image member (by decide) (by decide)) nextMemory written nurseryGuard d bp
''' if more else '''  obtain ⟨nb, after, _, steps, post⟩ := first guard d bp
'''
    memory='rw [memory, written, dp.memory]; simp only [closurePushLog, branch, ite_true]; rfl' if more else 'simp only [closurePushLog, empty, ite_false]; exact memory.trans dp.memory'
    if recursive:
        if more:
            start=setup.index('  have nurseryGuard')
            end=setup.index('  obtain',start)
            setup=setup[:start]+setup[end:]
        setup = """  have positive : 0 < functions.toInt.toNat := by omega
  have sizeBound : 3 * functions.toInt.toNat + count.toInt.toNat ≤ 257 := by
    have bound := nursery
    unfold closurerecSize at bound
    omega
  have nurseryGuard : zopz0zKzJ_u (256#64) (BitVec.ofNat 64 (closurerecSize functions.toInt.toNat count.toInt.toNat)) = true := by
    apply bgeu_of_le
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show closurerecSize functions.toInt.toNat count.toInt.toNat < 2^64 by omega)]
    omega
""" + setup
        if not more: runfinish=runfinish.replace('first guard d bp','first guard nurseryGuard d bp')
    parameters = '{functions : BitVec 32} ' if recursive else ''
    inputs = """    (functionsOperand : OperandAt P pl (s.pc + 1) functions) (functionsPositive : 0 < functions.toInt)
""" if recursive else ''
    nursery = 'closurerecSize functions.toInt.toNat count.toInt.toNat ≤ 256' if recursive else 'count.toInt.toNat ≤ 254'
    metadata = (f"⟨positive, nursery, {get('x17')}, {get('x26')}, {get('x27')}, {get('x16')}, ?_⟩, {get('x10')}"
                if recursive else f"⟨nursery, {get('x17')}, {get('x26')}, {get('x27')}, ?_⟩")
    arithmetic = """  have twice := closurerec_twice functions.toInt.toNat (by omega)
  have triple := addw_nat_add (2 * functions.toInt.toNat) functions.toInt.toNat (by omega)
  have tripleEq : 2 * functions.toInt.toNat + functions.toInt.toNat = 3 * functions.toInt.toNat := by omega
  rw [tripleEq] at triple
  have offset := addiw_nat_pred (3 * functions.toInt.toNat) (by omega) (by omega)
  have sizeWord : BitVec.ofNat 64 count.toInt.toNat + BitVec.ofNat 64 (3 * functions.toInt.toNat - 1) =
      BitVec.ofNat 64 (closurerecSize functions.toInt.toNat count.toInt.toNat) := by
    rw [← BitVec.ofNat_add]
    congr 1
    unfold closurerecSize
    omega
""" if recursive else "  have sizeWord := addiw_nat_add count.toInt.toNat 2 (offset := 0x002#12) (by decide) (by omega)\n"
    decode = """  have functionsLoaded := run functionsOperand.geometry.lower functionsOperand.geometry.upper functionsOperand.geometry.htif
    (BitVec.ofNat 64 functions.toInt.toNat) (by rw [functionsOperand.read32 h.code dp.memory, nonnegative_word32 functions (by omega)])
  have first := functionsLoaded operand.geometry.lower operand.geometry.upper operand.geometry.htif
    (BitVec.ofNat 64 count.toInt.toNat) (by rw [operand.read32 h.code dp.memory, nonnegative_word32 count nonnegative])
  simp only [twice, triple, offset, sizeWord] at first
""" if recursive else """  have first := run operand.geometry.lower operand.geometry.upper operand.geometry.htif
    (BitVec.ofNat 64 count.toInt.toNat) (by rw [operand.read32 h.code dp.memory, nonnegative_word32 count nonnegative])
"""
    return f'''-- GENERATED by scripts/gen_closure_prefix.py; do not edit.
import OCaml.Vm.Sim.{native}PrefixInput
import OCaml.Vm.Sim.{native}Prefix{stem}Segment
import OCaml.Vm.Sim.{native}Prefix{stem}Pins
import OCaml.Vm.Sim.Immediate
import OCaml.Vm.Sim.{"ClosurerecArithmetic" if recursive else "ApplyArithmetic"}
import OCaml.Vm.Sim.StackPush

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- The actual {kind} capture prefix establishes the common nursery input registers. -/
theorem {family}_prefix_{kind} {{L : OCaml.Layout}} {{P : Prog}} {{s : St}} {{c d : Config}}
    {{pl : Place}} {{cp : ChanPlace}} {{sp high : Nat}} {parameters}{{count : BitVec 32}} {{accu : BitVec 64}}
    (h : ArmInput L P s .{opcode} c pl cp sp high)
{inputs}    (operand : OperandAt P pl (s.pc + {2 if recursive else 1}) count) (nonnegative : 0 ≤ count.toInt)
    (nursery : {nursery}) (branch : {'0 < count.toInt.toNat' if more else 'count.toInt.toNat = 0'})
    (value : valWord pl s.accu = some accu) (space : ClosurePushInput sp count.toInt.toNat accu)
    (dp : DispatchPost c .{opcode} (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d) :
    ∃ nb after, StepsN nb d after ∧ {native}Prefixed c pl s.pc sp {"functions.toInt.toNat " if recursive else ""}count.toInt.toNat accu after := by
{setup}{arithmetic}  have codeBase := codePc_add pl s.pc {3 if recursive else 2}
  have bp : SegSt ({spec['entry']}#64)
      [{pins}]
      (fun σ => Vsa.Sim.Code.Caml{native}Prefix{stem}Loaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨{pinproof}, trivial⟩,
      dp.good.minstret, dp.tick, {family}_prefix_{kind}_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_{family}_prefix_{kind} {args} d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    show sign_extend (m := 64) (0x004#12) = 4#64 from by decide, BitVec.add_zero,
    codePc_succ, {"show sign_extend (m := 64) (0x008#12) = 8#64 from by decide, codePc_add pl s.pc 2, functionsOperand.geometry.toNat, " if recursive else ""}operand.geometry.toNat] at run
{decode}  simp only [sizeWord, show sign_extend (m := 64) (0x008#12) = 8#64 from by decide,
    show sign_extend (m := 64) ({"0x100" if recursive else "0x0fe"}#12) = {256 if recursive else 254}#64 from by decide, BitVec.zero_add, {"show sign_extend (m := 64) (0x00c#12) = 12#64 from by decide, " if recursive else ""}codeBase{', address, push.read.toNat' if more else ''}] at first
{runfinish}  obtain ⟨_, memory, rawFrame⟩ := post.extra
  have fullMemory : after.σ.mem = writeLog c.σ.mem (closurePushLog sp count.toInt.toNat accu) := by
    {memory}
  refine ⟨nb, after, steps, post.good, post.tick, image_of_writeLog h.dispatch.image space.image fullMemory,
    post.pcAt, {metadata}, fullMemory,
    (dp.frame.trans rawFrame).widenChecked (allowed := {family}PrefixWrites) (by decide)⟩
  · simp only [closureSource, {'branch, ite_true' if more else 'empty, ite_false'}]
    exact {get('x23')}

end OCaml.Vm.Sim
'''

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    for recursive in [False, True]:
        native='Closurerec' if recursive else 'Closure'
        for kind in ['more','zero']:
            p=ROOT/f'OCaml/Vm/Sim/{native}Prefix{kind.title()}.lean';out=render(kind,recursive)
            if args.check:
                if not p.exists() or p.read_text()!=out:raise SystemExit(f'drift: {p}')
            else:p.write_text(out)
    print('Closure prefix adapters current')
