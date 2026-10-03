import OCaml.Vm.Gc.Generated.AllocEntry
import OCaml.Vm.Gc.CodeFrame
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Primitives.MemoryFrame

namespace OCaml.Vm.Gc.AllocEntry
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Native slots are extracted from this allocator's prologue, independently
of oldify's outer native frame. -/
structure Windows (R : Nat → BitVec 64) : Prop where
  saved : ∀ cell ∈ saves, WriteWindow (frameSp R + BitVec.ofNat 64 cell.2) 8
  tag : WriteWindow (frameSp R + BitVec.ofNat 64 tagOffset) 8

def loads (R : Nat → BitVec 64) (c : Config) :=
  [read8 (writeLog c.σ.mem (prefixLog R)) Layout.sym_caml_fl_p_allocate]

/-- The free-list function pointer is an ELF-derived ordinary RAM word. -/
theorem pointer_window : ReadWindow (BitVec.ofNat 64 Layout.sym_caml_fl_p_allocate) 8 := by
  constructor <;> decide

theorem head_control {R : Nat → BitVec 64} (lds : List (List (BitVec 8)))
    (small : (R 10).toNat ≤ maximum.toNat) :
    TermFactsO (runGM headBlock.body (regs R) lds) headBlock.term := by
  rw [head_regs]
  simpa [headBlock, caml_alloc_shr_for_minor_gcXb768FSeg, TermFactsO, TermFactsT,
    afterHead, srcVal, lookupG, guardB, Functions.zopz0zI_u, Sail.BitVec.toNatInt] using small

theorem lookup_access {R c} (windows : Windows R) :
    AccessPlan (writeLog c.σ.mem (prefixLog R)) (afterHead R) (loads R c) lookupBlock.body := by
  simp only [lookupBlock, caml_alloc_shr_for_minor_gcXb784Seg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · apply pointer_window.ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, mkLine, decodeM, afterHead, srcVal, lookupG, eraseG,
      stepGM, stepLdsM, wvalM, imm20Of, Layout.sym_caml_fl_p_allocate,
      Functions.sign_extend, Sail.BitVec.signExtend]
  · apply windows.tag.sd rfl ?_
    simp [eaddrM, mkLine, decodeM, afterHead, srcVal, lookupG, eraseG,
      stepGM, stepLdsM, wvalM, tagOffset, Functions.sign_extend, Sail.BitVec.signExtend]

structure Input (R : Nat → BitVec 64) (target : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem
  registers : GHolds c.σ (regs R)
  windows : Windows R
  small : (R 10).toNat ≤ maximum.toNat
  pointer : word c Layout.sym_caml_fl_p_allocate = target
  outside : OutLRange (prefixLog R) Layout.sym_caml_fl_p_allocate 8

theorem access {R target c} (input : Input R target c) :
    ChainAccess c.σ.mem (regs R) (loads R c) blocks := by
  apply ChainAccess.cons ⟨head_access R c.σ.mem (loads R c) input.windows.saved, head_control _ input.small⟩
  rw [head_log, head_regs, head_loads]
  exact ChainAccess.cons ⟨lookup_access input.windows, True.intro⟩ ChainAccess.nil

/-- At the indirect free-list call with the actual loaded target, exact
native-save/tag log and concrete outgoing size/native register interface. -/
structure Post (R : Nat → BitVec 64) (target : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs R) (loads R before) before after
  memory : after.σ.mem = writeLog before.σ.mem (effect R)
  pc : PCAt callPc after
  registers : GHolds after.σ (atCall R target)
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem

/-- Actual allocating-wrapper prologue and free-list target lookup. -/
theorem prepare {R target c} (input : Input R target c) :
    FnSummary pc (fun d => d = c) (Post R target c) := by
  have facts := chainPlan_facts (code_facts input.code) (access input)
  have summary := block_summary blocks pc (regs R) (loads R c) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [2,1,8,9,10,11]; decide,
      facts, chain_ok, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post, ?_, ?_, ?_, image_after Code.caml_alloc_shr_for_minor_gc_transport (by decide) input.code facts post⟩
  · rw [post.memory, writes]
  · rw [PCAt, post.pc, endpoint]
  · have pins := post.regs
    rw [registers] at pins
    have pointer : bytesVal .ld ((loads R c).headD []) = target := by
      change bytesVal .ld (read8 (writeLog c.σ.mem (prefixLog R)) Layout.sym_caml_fl_p_allocate) = target
      rw [read8_value, bytesT_writeLog_out _ input.outside]
      exact input.pointer
    simpa only [pointer] using pins

end OCaml.Vm.Gc.AllocEntry
