import OCaml.Vm.Boot.Startup.SecureTailNormalized
import OCaml.Vm.Boot.Startup.SecureGetenvFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def secureTailInput (sp name : BitVec 64) : GRegs := [(2, secureStack sp), (9, name), (10, 0#64)]
def secureTailLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 32 + 16), read8 c.σ.mem (nativeFrameBase sp 32 + 24), read8 c.σ.mem (nativeFrameBase sp 32 + 8)]
def secureTailRegs (sp name ra s0 s1 : BitVec 64) : GRegs := [(2, sp), (9, s1), (10, name), (1, ra), (8, s0)]

local macro "secure_tail_nf" : tactic =>
  `(tactic| simp only [securetail_line_80025730, securetail_line_80025734, securetail_line_80025738,
    securetail_line_8002573c, securetail_line_80025740, MemFacts, runGM, ldsRunM, wlogM, stepGM,
    stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG, secureTailInput, secureTailLoads,
    wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem secure_stack_restore (sp : BitVec 64) : secureStack sp + 32#64 = sp := by
  unfold secureStack
  rw [BitVec.add_assoc]
  exact BitVec.add_zero sp

theorem secureTail_input {sp name oldra c} (h : LeafInput oldra c) (frame : NativeFrame sp 32)
    (regs : GHolds c.σ (secureTailInput sp name)) :
    BlockInput caml_secure_getenvX5730Seg 0x80025730#64 (secureTailInput sp name) (secureTailLoads sp c) c where
  good := h.good
  minstret := h.minstret
  regs := regs
  keys := by change KeysOK [2, 9, 10]; decide
  shape := by change ChainOK _ [2, 9, 10] _; decide
  tick := h.tick
  facts := by
    have code := secureGetenv_code h.image
    have window (off : Nat) (bound : off + 8 ≤ 32) (aligned : off % 8 = 0) :
        ReadWindow (secureStack sp + BitVec.ofNat 64 off) 8 := by
      rw [secureStack, frame.address off (by omega)]
      exact (frame.word bound aligned).read
    have pins (off : Nat) (bound : off ≤ 32) :
        LPins8 c.σ.mem (secureStack sp + BitVec.ofNat 64 off).toNat (read8 c.σ.mem (nativeFrameBase sp 32 + off)) := by
      rw [secure_slot_nat frame off bound]
      exact read8_pins _ _
    chain_facts code with "Vsa.Sim.Code.caml_secure_getenv_at_"
    · exact (window 16 (by decide) (by decide)).ld rfl rfl (pins 16 (by decide))
    · exact (window 24 (by decide) (by decide)).ld rfl rfl (pins 24 (by decide))
    · exact (window 8 (by decide) (by decide)).ld rfl rfl (pins 8 (by decide))

theorem secureTail_regs {sp name ra s0 s1 c} (saved : SecureSaved sp ra s0 s1 c) :
    (evalBlocks caml_secure_getenvX5730Seg (SegEvalState.init (secureTailInput sp name) (secureTailLoads sp c))).regs = secureTailRegs sp name ra s0 s1 := by
  simp only [caml_secure_getenvX5730Seg, evalBlocks, evalBlock, SegEvalState.init]
  secure_tail_nf
  rw [read8_value, read8_value, read8_value, saved.saved0, saved.saved1, saved.returnAddress]
  change [(2, secureStack sp + 32#64), (9, s1), (10, name + 0#64), (1, ra), (8, s0)] = _
  rw [secure_stack_restore, BitVec.add_zero]
  rfl

/-- Equal identities restore the original caller frame before tailcalling getenv. -/
theorem secure_getenv_tail (c : Config) (sp name ra s0 s1 oldra : BitVec 64) (h : LeafInput oldra c)
    (frame : NativeFrame sp 32) (regs : GHolds c.σ (secureTailInput sp name)) (saved : SecureSaved sp ra s0 s1 c) :
    FnSummary 0x80025730#64 (fun d => d = c)
      (WriteRegistersPost [8, 1, 10, 9, 2] [] c 0x80037410#64 name (secureTailRegs sp name ra s0 s1)) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (secureTail_input h frame regs))
  · rfl
  · rfl
  · exact secureTail_regs saved
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
