import OCaml.Vm.Boot.Startup.MinorHeapFrameNormalized
import OCaml.Vm.Boot.Startup.MinorHeapFrameImage
import OCaml.Vm.Boot.Startup.MinorHeapSaveNormalized
import OCaml.Vm.Boot.Startup.MinorHeapSaveImage
import OCaml.Vm.Boot.Startup.MinorHeapStateNormalized
import OCaml.Vm.Boot.Startup.MinorHeapStateImage
import OCaml.Vm.Boot.Startup.PageAddSteps
import OCaml.Vm.Boot.Startup.DomainInit
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_set_minor_heap_size(size)'s blocks, on the path from a domain whose
minor heap is empty and whose ref tables have no storage yet. -/

/-- A field of the first domain's state. -/
def domainField (off : Nat) : Nat := firstDomainPtr.toNat + off

/-- Open a 64-byte frame. -/
theorem minor_frame (c : Config) (sp ra v : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(2, sp), (10, v)]) :
    FnSummary 0x8000a23c#64 (fun e => e = c) (WriteRegistersPost [2] [] c 0x8000a240#64 v
      [(2, nativeStack sp 64), (10, v)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_set_minor_heap_sizeXa23cSeg 0x8000a23c#64 [(2, sp), (10, v)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := minorHeapFrame_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_set_minor_heap_size_at_" }))
  · rfl
  · rfl
  · intro σ pins
    exact ⟨gholds_lookup (n := 2) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

def minorSlots (ra s0 s1 s2 s3 : BitVec 64) : List (Nat × BitVec 64) :=
  [(40, s1), (32, s2), (56, ra), (48, s0), (24, s3)]

/-- Save s1, s2, ra, s0, s3. -/
theorem minor_save (c : Config) (sp ra s0 s1 s2 s3 v : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 64)
    (regs : GHolds c.σ [(9, s1), (2, nativeStack sp 64), (18, s2), (1, ra), (8, s0), (19, s3), (10, v)]) :
    FnSummary 0x8000a240#64 (fun e => e = c) (WriteRegistersPost [] (nativeWordLog sp 64 (minorSlots ra s0 s1 s2 s3))
      c 0x8000a254#64 v [(9, s1), (2, nativeStack sp 64), (18, s2), (1, ra), (8, s0), (19, s3), (10, v)]) := by
  have inside : LogInW [⟨nativeFrameBase sp 64, sp.toNat⟩] (nativeWordLog sp 64 (minorSlots ra s0 s1 s2 s3)) :=
    frame.word_log_inside fun off value member => by simp [minorSlots] at member; omega
  apply registers_of_blocks' leaf.image (frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_set_minor_heap_sizeXa240Seg 0x8000a240#64
        [(9, s1), (2, nativeStack sp 64), (18, s2), (1, ra), (8, s0), (19, s3), (10, v)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [9, 2, 18, 1, 8, 19, 10]; decide
      shape := by change ChainOK _ [9, 2, 18, 1, 8, 19, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := minorHeapSave_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 64) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 64 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_set_minor_heap_size_at_"
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 56 (by decide) (by decide)).sd rfl rfl
        · exact (slot 48 (by decide) (by decide)).sd rfl rfl
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · intro σ pins
    exact pins
  · rfl
  · decide

local macro "msk" : tactic => `(tactic| simp only [minorheapstate_line_8000a254, minorheapstate_line_8000a258, minorheapstate_line_8000a25c, minorheapstate_line_8000a260, minorheapstate_line_8000a264, minorheapstate_line_8000a268, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- `s1 = &Caml_state`, `s2 = size`; the minor heap is empty
(`young_ptr = young_alloc_end`), so nothing is emptied. -/
theorem minor_state (c : Config) (ra size : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, size)])
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr)
    (idle : bytesT c.σ.mem (domainField 8) 8 = bytesT c.σ.mem (domainField 56) 8) :
    FnSummary 0x8000a254#64 (fun e => e = c) (WriteRegistersPost [9, 15, 18, 13, 14] [] c 0x8000a284#64 size
      [(9, BitVec.ofNat 64 Layout.sym_Caml_state), (15, firstDomainPtr), (18, size),
        (13, bytesT c.σ.mem (domainField 8) 8), (14, bytesT c.σ.mem (domainField 8) 8), (10, size)]) := by
  have state : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat) = firstDomainPtr := by
    rw [read8_value]; exact domain
  have young : bytesVal .ld (read8 c.σ.mem (firstDomainPtr + 8#64).toNat) = bytesT c.σ.mem (domainField 8) 8 := by
    rw [read8_value]; rfl
  have alloc : bytesVal .ld (read8 c.σ.mem (firstDomainPtr + 56#64).toNat) = bytesT c.σ.mem (domainField 8) 8 := by
    rw [read8_value, idle]; rfl
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_set_minor_heap_sizeXa254TSeg 0x8000a254#64 [(10, size)]
        [read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat, read8 c.σ.mem (firstDomainPtr + 8#64).toNat,
          read8 c.σ.mem (firstDomainPtr + 56#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := minorHeapState_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_set_minor_heap_size_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 by constructor <;> decide).ld rfl
            (by msk; decide) (read8_pins _ _)
        · exact (show ReadWindow (firstDomainPtr + 8#64) 8 by constructor <;> decide).ld rfl
            (by msk; rw [state]; decide) (read8_pins _ _)
        · exact (show ReadWindow (firstDomainPtr + 56#64) 8 by constructor <;> decide).ld rfl
            (by msk; rw [state]; decide) (read8_pins _ _)
        · msk
          rw [young, alloc]
          exact beq_self_eq_true _ }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_set_minor_heap_sizeXa254TSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, imm20Of, minorheapstate_line_8000a254, minorheapstate_line_8000a258, minorheapstate_line_8000a25c, minorheapstate_line_8000a260, minorheapstate_line_8000a264, minorheapstate_line_8000a268] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl state, gholds_lookup_eq pins rfl
        (by rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]),
      gholds_lookup_eq pins rfl young, gholds_lookup_eq pins rfl alloc, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
