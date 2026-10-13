#!/usr/bin/env python3
"""Emit the step summaries of newlib's reentrant syscall wrappers.

newlib's `f(a, b, c)` loads `_impure_ptr`, shifts its arguments up one and
tail-jumps to `_f_r(reent, a, b, c)`, which saves `s0`/`ra`, clears the global
`errno`, calls htif.c's `_f`, and on success restores and returns `_f`'s
result. The three blocks have one shape for every `f`; this script
instantiates it per function from the generated rows (gen_startup_rows.py),
so no wrapper is proved by hand.

    scripts/gen_reent_wrappers.py [--check]
"""
import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'OCaml/Vm/Boot/Startup/ReentWrappers.lean'
STARTUP = ROOT / 'OCaml/Vm/Boot/Startup'

# fn: newlib wrapper, its `_r`, the htif callee entry, and the row stems.
# lib: (stem, entry, segment, auipc pc, ld imm, `_r` entry)
# r:   (stem, segment, auipc pc, sw imm, jal pc)
# ret: (stem, entry, segments)
TABLE = [
    ('lseek', '_lseek_r',
     ('LibLseek', 0x80042574, 'lseekX2574Seg', 0x80042578, 896, 0x80042328),
     ('LseekREntry', 'lseek_rX2328Seg', 0x80042348, -1536, 0x80042350),
     ('LseekRReturn', 0x80042354, ['lseek_rX2354FSeg', 'lseek_rX235cSeg'])),
    ('read', '_read_r',
     ('LibRead', 0x800425e4, 'readX25e4Seg', 0x800425e8, 784, 0x8004238c),
     ('ReadREntry', 'read_rX238cSeg', 0x800423ac, -1636, 0x800423b4),
     ('ReadRReturn', 0x800423b8, ['read_rX23b8FSeg', 'read_rX23c0Seg'])),
]


def lines(stem):
    text = (STARTUP / f'{stem}Normalized.lean').read_text()
    return ', '.join(re.findall(r'^theorem (\w+_line_[0-9a-f]+)', text, re.M))


def code(stem):
    return stem[0].lower() + stem[1:] + '_code'


def imm12(v):
    return v & 0xfff


def emit(fn, rfn, lib, r, ret):
    lstem, lentry, lseg, lauipc, limm, rentry = lib
    rstem, rseg, rauipc, rimm, rjal = r
    tstem, tentry, tsegs = ret
    L, R, T = lines(lstem), lines(rstem), lines(tstem)
    a5 = rauipc + (0x23 << 12)
    fnid = fn.replace('_', '')
    return f'''
open Sail in
/-- `auipc a0; ld a0,{limm}(a0)` at {lauipc:#x}: `_impure_ptr`. -/
theorem {fnid}_impure_auipc : {lauipc}#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 140567#32 +++ 0#12) +
    Functions.sign_extend (m := 64) {imm12(limm)}#12 = BitVec.ofNat 64 allocatorImpureAddr := by decide

/-- `{fn}`: move the arguments up one and load `_impure_ptr`. -/
theorem lib_{fnid} (c : Config) (a b d ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, a), (11, b), (12, d)]) :
    FnSummary {lentry:#x}#64 (fun e => e = c)
      (WriteRegistersPost [14, 10, 13, 12, 11] [] c {rentry:#x}#64 (getenvReent c)
        [(11, a), (12, b), (13, d), (10, getenvReent c), (14, a)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput {lseg} {lentry:#x}#64 [(10, a), (11, b), (12, d)]
        [read8 c.σ.mem allocatorImpureAddr] c from {{
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 11, 12]; decide
      shape := by change ChainOK _ [10, 11, 12] _; decide
      tick := leaf.tick
      facts := by
        have code := {code(lstem)} leaf.image
        chain_facts code with "Vsa.Sim.Code.{fn}_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 allocatorImpureAddr) 8 by constructor <;> decide).ld rfl
            (by simp only [{L}, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
                  ite_false, imm20Of, Nat.reduceEqDiff]
                exact {fnid}_impure_auipc) (read8_pins _ _) }}))
  · rfl
  · rfl
  · simp only [{lseg}, evalBlocks, evalBlock, SegEvalState.init, {L}, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, getenvReent, read8_value,
      open_se0, BitVec.add_zero]
  · rfl
  · decide

open Sail in
/-- `auipc a5; sw zero,{rimm}(a5)` at {rauipc:#x}: the global `errno`. -/
theorem {fnid}_r_errno_auipc : {rauipc}#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 145303#32 +++ 0#12) +
    Functions.sign_extend (m := 64) {imm12(rimm)}#12 = BitVec.ofNat 64 0x80064d48 := by decide

open Sail in
theorem {fnid}_r_a5_auipc : {rauipc}#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 145303#32 +++ 0#12) =
    {a5:#x}#64 := by decide

/-- `{rfn}`: save, clear the global `errno`, call `_{fn}(a, b, d)`. -/
theorem {fnid}_r_entry (c : Config) (sp ra s0 reent a b d : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 16) (regs : GHolds c.σ (openRInput sp ra s0 reent a b d)) :
    FnSummary {rentry:#x}#64 (fun e => e = c) (WriteRegistersPost [15, 10, 12, 8, 11, 2] (openRLog sp ra s0) c {rjal:#x}#64 a
      [(15, {a5:#x}#64), (10, a), (12, d), (8, reent), (11, b), (2, nativeStack sp 16), (1, ra),
        (13, d)]) := by
  apply registers_of_blocks leaf.image (imageOutside_append (frame.image_outside (frame.word_log_inside
      fun off value member => by simp at member; omega)) (by constructor <;> simp only [OutLRange] <;> decide))
    (block_summary _ _ _ _ _ (show BlockInput {rseg} {rentry:#x}#64 (openRInput sp ra s0 reent a b d)
        [] c from {{
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 8, 10, 11, 12, 13]; decide
      shape := by change ChainOK _ [2, 1, 8, 10, 11, 12, 13] _; decide
      tick := leaf.tick
      facts := by
        have code := {code(rstem)} leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 16) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 16 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.{rfn}_at_"
        · exact (slot 0 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl
        · exact (show WriteWindow (BitVec.ofNat 64 0x80064d48) 4 by constructor <;> decide).sw rfl
            (by simp only [{R}, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
                  ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
                exact {fnid}_r_errno_auipc) }}))
  · simp only [{rseg}, evalBlocks, evalBlock, SegEvalState.init, {R}, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, openRInput, imm20Of, openRLog,
      nativeWordLog, List.map, List.nil_append, List.cons_append, {fnid}_r_errno_auipc,
      show Functions.sign_extend (m := 64) 4080#12 = -BitVec.ofNat 64 16 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide]
    rfl
  · rfl
  · simp only [{rseg}, evalBlocks, evalBlock, SegEvalState.init, {R}, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, openRInput, imm20Of,
      show Functions.sign_extend (m := 64) 4080#12 = -BitVec.ofNat 64 16 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, {fnid}_r_a5_auipc]
    rfl
  · rfl
  · decide

/-- `_{fn}` succeeded: `{rfn}` restores and returns its result. -/
theorem {fnid}_r_succeed (c : Config) (sp ra s0 v oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 16) (regs : GHolds c.σ [(10, v), (2, nativeStack sp 16)]) (ok : v ≠ -1#64)
    (saved : ∀ off value, (off, value) ∈ [(8, ra), (0, s0)] →
      bytesT c.σ.mem (nativeFrameBase sp 16 + off) 8 = value) (aligned : ra.toNat % 4 = 0) :
    FnSummary {tentry:#x}#64 (fun e => e = c)
      (WriteRegistersPost [2, 8, 1, 15] [] c ra v [(2, sp), (8, s0), (1, ra), (15, -1#64), (10, v)]) := by
  have savedRa := saved 8 ra (by simp)
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput ({' ++ '.join(tsegs)}) {tentry:#x}#64
        [(10, v), (2, nativeStack sp 16)]
        [read8 c.σ.mem (nativeFrameBase sp 16 + 8), read8 c.σ.mem (nativeFrameBase sp 16 + 0)] c from {{
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 2]; decide
      shape := by change ChainOK _ [10, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := {code(tstem)} leaf.image
        chain_facts code with "Vsa.Sim.Code.{rfn}_at_"
        · change guardB bop.BEQ v (0#64 + Functions.sign_extend (m := 64) 4095#12) = false
          rw [show 0#64 + Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide]
          exact beq_eq_false_iff_ne.mpr ok
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 0) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 16 + 8)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }}))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 16 + 8)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · simp only [{', '.join(tsegs)}, evalBlocks, evalBlock, SegEvalState.init, {T}, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, read8_value,
      List.cons_append, List.nil_append]
    rw [show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide, nativeStack_restore, savedRa,
      saved 0 s0 (by simp), show 0#64 + Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide]
  · rfl
  · decide
'''


def render():
    imports = ['OCaml.Vm.Boot.Startup.OpenSteps', 'OCaml.Vm.Boot.Startup.OpenProgSteps']
    for _, _, lib, r, ret in TABLE:
        for stem in (lib[0], r[0], ret[0]):
            imports += [f'OCaml.Vm.Boot.Startup.{stem}Normalized', f'OCaml.Vm.Boot.Startup.{stem}Image']
    head = '\n'.join(f'import {m}' for m in imports) + '''
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! GENERATED by scripts/gen_reent_wrappers.py — do not hand-edit.
newlib's reentrant syscall wrappers (`f` → `_f_r` → htif.c's `_f`): the
tail-jumping wrapper, `_f_r`'s prologue and its success return, one instance
per function. -/
'''
    return head + ''.join(emit(*row) for row in TABLE) + 'end OCaml.Vm.Boot.Startup\n'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    text = render()
    if args.check:
        if not OUT.exists() or OUT.read_text() != text:
            raise SystemExit(f'{OUT.relative_to(ROOT)}: drift; rerun scripts/gen_reent_wrappers.py')
        return
    OUT.write_text(text)


if __name__ == '__main__':
    main()
