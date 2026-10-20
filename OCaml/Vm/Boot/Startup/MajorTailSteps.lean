import OCaml.Vm.Boot.Startup.MajorGrayNormalized
import OCaml.Vm.Boot.Startup.MajorGrayImage
import OCaml.Vm.Boot.Startup.MajorStackSetNormalized
import OCaml.Vm.Boot.Startup.MajorStackSetImage
import OCaml.Vm.Boot.Startup.MajorStackAllocNormalized
import OCaml.Vm.Boot.Startup.MajorStackAllocImage
import OCaml.Vm.Boot.Startup.MajorStackStoreNormalized
import OCaml.Vm.Boot.Startup.MajorStackStoreImage
import OCaml.Vm.Boot.Startup.MajorStackCheckNormalized
import OCaml.Vm.Boot.Startup.MajorStackCheckImage
import OCaml.Vm.Boot.Startup.MajorStackInitNormalized
import OCaml.Vm.Boot.Startup.MajorStackInitImage
import OCaml.Vm.Boot.Startup.MajorReturnNormalized
import OCaml.Vm.Boot.Startup.MajorReturnImage
import OCaml.Vm.Boot.Startup.MajorGrayCallInterface
import OCaml.Vm.Boot.Startup.MajorStackAllocCallInterface
import OCaml.Vm.Boot.Startup.MajorHeadSteps
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_init_major_heap's end: `caml_gc_phase = Phase_idle`, the mark stack
(`caml_stat_alloc_noexc` twice), `caml_extra_heap_resources`, and the tail call
`memset(caml_major_ring, 0, 400)`. -/

/-- `caml_gc_phase`. -/
def gcPhaseAddr : Nat := 0x80064ac0

/-- `caml_gc_phase = Phase_idle`; `caml_stat_alloc_noexc(sizeof(struct mark_stack))`. -/
theorem major_phase_front (c : Config) (ra v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, BitVec.ofNat 64 Layout.sym_Caml_state), (10, v)])
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr) :
    FnSummary 0x80009434#64 (fun e => e = c) (WriteRegistersPost [15, 10, 9, 14] [(gcPhaseAddr, 4, 3#64)] c
      jal_80009448_call.pc 24#64 [(15, 3#64), (10, 24#64), (9, firstDomainPtr), (14, 0x80064440#64),
        (8, BitVec.ofNat 64 Layout.sym_Caml_state)]) := by
  have dw : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat) = firstDomainPtr := by
    rw [read8_value]; exact domain
  apply registers_of_blocks' leaf.image (by constructor <;> simp only [OutLRange, gcPhaseAddr] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX9434Seg 0x80009434#64
        [(8, BitVec.ofNat 64 Layout.sym_Caml_state), (10, v)]
        [read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 10]; decide
      shape := by change ChainOK _ [8, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := majorGray_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 by constructor <;> decide).ld rfl
            (by simp only [majorgray_line_80009434, majorgray_line_80009438, majorgray_line_8000943c, majorgray_line_80009440, majorgray_line_80009444, eaddrM, srcVal, lookupG, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false,
              Nat.reduceEqDiff, List.headD_cons]; decide) (read8_pins _ _)
        · exact (show WriteWindow (BitVec.ofNat 64 gcPhaseAddr) 4 by constructor <;> decide).sw rfl
            (by simp only [majorgray_line_80009434, majorgray_line_80009438, majorgray_line_8000943c, majorgray_line_80009440, majorgray_line_80009444, eaddrM, srcVal, lookupG, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false,
              Nat.reduceEqDiff, List.headD_cons, imm20Of]; decide) }))
  · simp only [caml_init_major_heapX9434Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, List.headD_cons, List.tail_cons, imm20Of, majorgray_line_80009434, majorgray_line_80009438, majorgray_line_8000943c, majorgray_line_80009440, majorgray_line_80009444]
    decide
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX9434Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, imm20Of, majorgray_line_80009434, majorgray_line_80009438, majorgray_line_8000943c, majorgray_line_80009440, majorgray_line_80009444] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl dw,
      gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 8) _ pins rfl, trivial⟩
  · rfl
  · decide

theorem major_phase_call (c : Config) (ra v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, BitVec.ofNat 64 Layout.sym_Caml_state), (10, v)])
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr) :
    FnSummary 0x80009434#64 (fun e => e = c) (WriteRegistersPost ([15, 10, 9, 14] ++ [1]) [(gcPhaseAddr, 4, 3#64)] c
      jal_80009448_call.target 24#64 ((1, jal_80009448_call.link) :: [(15, 3#64), (10, 24#64), (9, firstDomainPtr),
        (14, 0x80064440#64), (8, BitVec.ofNat 64 Layout.sym_Caml_state)])) :=
  block_then_call c jal_80009448_call_shape jal_80009448_call_decode (fun _ h => jal_80009448_call_pins h)
    (major_phase_front c ra v leaf regs domain) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

/-- `Caml_state->mark_stack = mark stack record`. -/
theorem major_stack_set (c : Config) (ra stack : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, BitVec.ofNat 64 Layout.sym_Caml_state), (10, stack), (9, firstDomainPtr)])
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr) :
    FnSummary 0x8000944c#64 (fun e => e = c) (WriteRegistersPost [15] [(domainField 128, 8, stack)] c 0x80009454#64 stack
      [(15, firstDomainPtr), (8, BitVec.ofNat 64 Layout.sym_Caml_state), (10, stack), (9, firstDomainPtr)]) := by
  have dw : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat) = firstDomainPtr := by
    rw [read8_value]; exact domain
  apply registers_of_blocks' leaf.image (by
      constructor <;> simp only [OutLRange, domainField, show firstDomainPtr.toNat = 0x8007d150 from rfl] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX944cSeg 0x8000944c#64
        [(8, BitVec.ofNat 64 Layout.sym_Caml_state), (10, stack), (9, firstDomainPtr)]
        [read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 10, 9]; decide
      shape := by change ChainOK _ [8, 10, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := majorStackSet_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 by constructor <;> decide).ld rfl
            (by simp only [majorstackset_line_8000944c, majorstackset_line_80009450, eaddrM, srcVal, lookupG, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff,
              sext_zero, BitVec.add_zero]) (read8_pins _ _)
        · exact (show WriteWindow (BitVec.ofNat 64 (domainField 128)) 8 by constructor <;> decide).sd rfl
            (by simp only [majorstackset_line_8000944c, majorstackset_line_80009450, eaddrM, srcVal, lookupG, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false,
              Nat.reduceEqDiff, List.headD_cons]; decide) }))
  · simp only [caml_init_major_heapX944cSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, List.headD_cons, List.tail_cons, majorstackset_line_8000944c, majorstackset_line_80009450]
    rw [show (firstDomainPtr + Functions.sign_extend (m := 64) 128#12).toNat = domainField 128 by decide]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX944cSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, majorstackset_line_8000944c, majorstackset_line_80009450] at pins
    exact ⟨gholds_lookup_eq pins rfl dw, gholds_lookup (n := 8) _ pins rfl, gholds_lookup (n := 10) _ pins rfl,
      gholds_lookup (n := 9) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- The mark stack record is nonnull; `caml_stat_alloc_noexc(MARK_STACK_INIT_SIZE * sizeof(mark_entry))`. -/
theorem major_stack_alloc_front (c : Config) (ra stack : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, firstDomainPtr), (10, stack)])
    (word : bytesT c.σ.mem (domainField 128) 8 = stack) (nonzero : stack ≠ 0#64) :
    FnSummary 0x80009454#64 (fun e => e = c) (WriteRegistersPost [9, 10] [] c jal_80009460_call.pc 32768#64
      [(9, stack), (10, 32768#64), (15, firstDomainPtr)]) := by
  have sw : bytesVal .ld (read8 c.σ.mem (firstDomainPtr + 128#64).toNat) = stack := by rw [read8_value]; exact word
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (caml_init_major_heapX9454FSeg ++ caml_init_major_heapX945cSeg) 0x80009454#64
        [(15, firstDomainPtr), (10, stack)] [read8 c.σ.mem (firstDomainPtr + 128#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 10]; decide
      shape := by change ChainOK _ [15, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := majorStackAlloc_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        · exact (show ReadWindow (firstDomainPtr + 128#64) 8 by constructor <;> decide).ld rfl
            (by simp only [majorstackalloc_line_80009454, majorstackalloc_line_8000945c, eaddrM, srcVal, lookupG, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff]; decide)
            (read8_pins _ _)
        · simp only [majorstackalloc_line_80009454, majorstackalloc_line_8000945c, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false,
            Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons]
          rw [sw]
          exact beq_eq_false_iff_ne.mpr nonzero }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX9454FSeg, caml_init_major_heapX945cSeg, List.cons_append, List.nil_append,
      evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM, srcVal, lookupG, eraseG, wvalM,
      Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons, List.tail_cons, imm20Of, majorstackalloc_line_80009454, majorstackalloc_line_8000945c] at pins
    rw [sw] at pins
    exact ⟨gholds_lookup (n := 9) _ pins rfl, gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 15) _ pins rfl,
      trivial⟩
  · rfl
  · decide

theorem major_stack_alloc_call (c : Config) (ra stack : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, firstDomainPtr), (10, stack)])
    (word : bytesT c.σ.mem (domainField 128) 8 = stack) (nonzero : stack ≠ 0#64) :
    FnSummary 0x80009454#64 (fun e => e = c) (WriteRegistersPost ([9, 10] ++ [1]) [] c jal_80009460_call.target 32768#64
      ((1, jal_80009460_call.link) :: [(9, stack), (10, 32768#64), (15, firstDomainPtr)])) :=
  block_then_call c jal_80009460_call_shape jal_80009460_call_decode (fun _ h => jal_80009460_call_pins h)
    (major_stack_alloc_front c ra stack leaf regs word nonzero) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl
end OCaml.Vm.Boot.Startup
