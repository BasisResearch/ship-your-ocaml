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

/-- `stack->stack = entries`. -/
theorem major_stack_store (c : Config) (ra stack entries : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, entries), (9, stack)]) (window : WriteWindow stack 8)
    (outside : ImageOutside [(stack.toNat, 8, entries)]) :
    FnSummary 0x80009464#64 (fun e => e = c) (WriteRegistersPost [] [(stack.toNat, 8, entries)] c 0x80009468#64 entries
      [(10, entries), (9, stack)]) := by
  apply registers_of_blocks' leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX9464Seg 0x80009464#64 [(10, entries), (9, stack)] [] c
      from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 9]; decide
      shape := by change ChainOK _ [10, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := majorStackStore_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        · exact window.sd rfl (by simp only [majorstackstore_line_80009464, eaddrM, srcVal, lookupG, Option.getD_some, ite_true, ite_false,
            Nat.reduceEqDiff, sext_zero, BitVec.add_zero]) }))
  · simp only [caml_init_major_heapX9464Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, wlogM, wentryM,
      widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, majorstackstore_line_80009464,
      sext_zero, BitVec.add_zero]
    rfl
  · rfl
  · intro σ pins
    exact pins
  · rfl
  · decide

local macro "msc" : tactic => `(tactic| simp only [majorstackcheck_line_80009468, majorstackcheck_line_8000946c, majorstackcheck_line_80009470, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- Reload the record and its entries; nonnull. -/
theorem major_stack_check (c : Config) (ra stack entries v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, BitVec.ofNat 64 Layout.sym_Caml_state), (10, v)])
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr)
    (record : bytesT c.σ.mem (domainField 128) 8 = stack) (readRecord : ReadWindow stack 8)
    (stored : bytesT c.σ.mem stack.toNat 8 = entries) (nonzero : entries ≠ 0#64) :
    FnSummary 0x80009468#64 (fun e => e = c) (WriteRegistersPost [15, 14, 13] [] c 0x80009478#64 v
      [(15, firstDomainPtr), (14, stack), (13, entries), (8, BitVec.ofNat 64 Layout.sym_Caml_state), (10, v)]) := by
  have dw : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat) = firstDomainPtr := by
    rw [read8_value]; exact domain
  have rw' : bytesVal .ld (read8 c.σ.mem (firstDomainPtr + 128#64).toNat) = stack := by rw [read8_value]; exact record
  have ew : bytesVal .ld (read8 c.σ.mem stack.toNat) = entries := by rw [read8_value]; exact stored
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX9468FSeg 0x80009468#64
        [(8, BitVec.ofNat 64 Layout.sym_Caml_state), (10, v)]
        [read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat, read8 c.σ.mem (firstDomainPtr + 128#64).toNat,
          read8 c.σ.mem stack.toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 10]; decide
      shape := by change ChainOK _ [8, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := majorStackCheck_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 by constructor <;> decide).ld rfl
            (by msc; rw [sext_zero, BitVec.add_zero]) (read8_pins _ _)
        · exact (show ReadWindow (firstDomainPtr + 128#64) 8 by constructor <;> decide).ld rfl
            (by msc; rw [dw]; decide) (read8_pins _ _)
        · exact readRecord.ld rfl (by msc; simp only [dw, show firstDomainPtr + Functions.sign_extend (m := 64) 128#12 = firstDomainPtr + 128#64 by decide, rw', sext_zero, BitVec.add_zero]) (read8_pins _ _)
        · msc
          simp only [dw, show firstDomainPtr + Functions.sign_extend (m := 64) 128#12 = firstDomainPtr + 128#64 by decide, rw', sext_zero, BitVec.add_zero, ew]
          exact beq_eq_false_iff_ne.mpr nonzero }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX9468FSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, majorstackcheck_line_80009468, majorstackcheck_line_8000946c, majorstackcheck_line_80009470] at pins
    exact ⟨gholds_lookup_eq pins rfl dw, gholds_lookup_eq pins rfl rw', gholds_lookup_eq pins rfl ew,
      gholds_lookup (n := 8) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

local macro "msi" : tactic => `(tactic| simp only [majorstackinit_line_80009478, majorstackinit_line_8000947c, majorstackinit_line_80009480, majorstackinit_line_80009484, majorstackinit_line_80009488, majorstackinit_line_8000948c, majorstackinit_line_80009490, majorstackinit_line_80009494, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- `caml_extra_heap_resources`. -/
def extraResourcesAddr : Nat := 0x80064aa0

/-- `stack->count = 0`, `stack->size = MARK_STACK_INIT_SIZE`, `caml_extra_heap_resources = 0`. -/
def stackInitLog (stack : BitVec 64) : List WEntry :=
  [((stack + 8#64).toNat, 8, 0#64), ((stack + 16#64).toNat, 8, 2048#64), (extraResourcesAddr, 8, 0#64)]

theorem major_stack_init (c : Config) (ra stack v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(14, stack), (15, firstDomainPtr), (10, v)])
    (record : bytesT c.σ.mem (domainField 128) 8 = stack)
    (window8 : WriteWindow (stack + 8#64) 8) (window16 : WriteWindow (stack + 16#64) 8)
    (apart : OutLRange [((stack + 8#64).toNat, 8, 0#64)] (domainField 128) 8)
    (outside : ImageOutside (stackInitLog stack)) :
    FnSummary 0x80009478#64 (fun e => e = c) (WriteRegistersPost [14, 15] (stackInitLog stack) c 0x80009498#64 v
      [(14, stack), (15, 0x80064aa0#64), (10, v)]) := by
  have rw' : bytesVal .ld (read8 c.σ.mem (firstDomainPtr + 128#64).toNat) = stack := by rw [read8_value]; exact record
  have s8 : Functions.sign_extend (m := 64) 8#12 = 8#64 := by decide
  have s16 : Functions.sign_extend (m := 64) 16#12 = 16#64 := by decide
  have s128 : Functions.sign_extend (m := 64) 128#12 = 128#64 := by decide
  apply registers_of_blocks' leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX9478Seg 0x80009478#64
        [(14, stack), (15, firstDomainPtr), (10, v)] [read8 c.σ.mem (firstDomainPtr + 128#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [14, 15, 10]; decide
      shape := by change ChainOK _ [14, 15, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := majorStackInit_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        · exact window8.sd rfl (by msi; rw [s8])
        · past_stores
          · exact (show ReadWindow (firstDomainPtr + 128#64) 8 by constructor <;> decide).ld rfl (by msi; rw [s128])
              (read8_pins _ _)
          all_goals (intro _; simp only [majorstackinit_line_80009478, majorstackinit_line_8000947c, majorstackinit_line_80009480, majorstackinit_line_80009484, majorstackinit_line_80009488, majorstackinit_line_8000948c, majorstackinit_line_80009490, majorstackinit_line_80009494, wentryM, widthOfM, eaddrM, srcVal, lookupG, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, s8, s128, stepGM, eraseG, wvalM, List.headD_cons]; simp only [show (firstDomainPtr + 128#64).toNat = domainField 128 from rfl]; exact apart)
        · exact window16.sd rfl (by msi; simp only [s16, rw', s128])
        · exact (show WriteWindow (BitVec.ofNat 64 extraResourcesAddr) 8 by constructor <;> decide).sd rfl
            (by msi; decide) }))
  · simp only [caml_init_major_heapX9478Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, List.headD_cons, List.tail_cons, imm20Of, majorstackinit_line_80009478, majorstackinit_line_8000947c, majorstackinit_line_80009480, majorstackinit_line_80009484, majorstackinit_line_80009488, majorstackinit_line_8000948c, majorstackinit_line_80009490, majorstackinit_line_80009494]
    simp only [s8, s16, s128, rw']
    rw [show (2147521676#64 + Functions.sign_extend (BitVec.extractLsb' 12 20 0x0005b797#32 +++ 0#12) +
      Functions.sign_extend (m := 64) 1556#12 + Functions.sign_extend (m := 64) 0#12).toNat = extraResourcesAddr by decide,
      show Functions.sign_extend (BitVec.extractLsb' 12 20 0x000017b7#32 +++ 0#12) + Functions.sign_extend (m := 64) 2048#12
        = 2048#64 by decide]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX9478Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, imm20Of, majorstackinit_line_80009478, majorstackinit_line_8000947c, majorstackinit_line_80009480, majorstackinit_line_80009484, majorstackinit_line_80009488, majorstackinit_line_8000948c, majorstackinit_line_80009490, majorstackinit_line_80009494] at pins
    simp only [s128, rw'] at pins
    exact ⟨gholds_lookup (n := 14) _ pins rfl, gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 10) _ pins rfl,
      trivial⟩
  · rfl
  · decide

/-- `caml_allocated_words`. -/
def allocatedWordsAddr : Nat := 0x80064ab8
/-- `caml_major_ring`. -/
def majorRingAddr : Nat := 0x80068328

def majorSavedLoads (m : Std.ExtHashMap Nat (BitVec 8)) (sp : BitVec 64) : List (List (BitVec 8)) :=
  [Primitives.read8 m (nativeFrameBase sp 48 + 32), Primitives.read8 m (nativeFrameBase sp 48 + 40),
    Primitives.read8 m (nativeFrameBase sp 48 + 24), Primitives.read8 m (nativeFrameBase sp 48 + 16)]

/-- Restore; `caml_allocated_words = 0`; tail call `memset(caml_major_ring, 0, 400)`. -/
theorem major_tail (c : Config) (sp ra s0 s1 s2 v oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ [(2, nativeStack sp 48), (10, v)])
    (saved : ∀ off value, (off, value) ∈ majorSlots ra s0 s1 s2 → bytesT c.σ.mem (nativeFrameBase sp 48 + off) 8 = value) :
    FnSummary 0x80009498#64 (fun e => e = c) (WriteRegistersPost [8, 1, 9, 18, 15, 12, 11, 10, 2]
      [(allocatedWordsAddr, 8, 0#64)] c 0x8004276c#64 (BitVec.ofNat 64 majorRingAddr)
      [(2, sp), (10, BitVec.ofNat 64 majorRingAddr), (11, 0#64), (12, 400#64), (18, s2), (9, s1), (1, ra),
        (8, s0)]) := by
  have word (off : Nat) (value : BitVec 64) (member : (off, value) ∈ majorSlots ra s0 s1 s2) :
      bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + off)) = value := by
    rw [read8_value]; exact saved off value member
  apply registers_of_blocks' leaf.image (by constructor <;> simp only [OutLRange, allocatedWordsAddr] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX9498Seg 0x80009498#64
        [(2, nativeStack sp 48), (10, v)] (majorSavedLoads c.σ.mem sp) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := majorReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 16) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (show WriteWindow (BitVec.ofNat 64 allocatedWordsAddr) 8 by constructor <;> decide).sd rfl
            (by simp only [majorreturn_line_80009498, majorreturn_line_8000949c, majorreturn_line_800094a0, majorreturn_line_800094a4, majorreturn_line_800094a8, majorreturn_line_800094ac, majorreturn_line_800094b0, majorreturn_line_800094b4, majorreturn_line_800094b8, majorreturn_line_800094bc, majorreturn_line_800094c0, eaddrM, srcVal, lookupG, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false,
              Nat.reduceEqDiff, imm20Of, stepLdsM, List.headD_cons, List.tail_cons]; decide) }))
  · simp only [caml_init_major_heapX9498Seg, majorSavedLoads, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
      stepLdsM, ldsRunM, wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some,
      Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons, List.tail_cons, imm20Of, majorreturn_line_80009498, majorreturn_line_8000949c, majorreturn_line_800094a0, majorreturn_line_800094a4, majorreturn_line_800094a8, majorreturn_line_800094ac, majorreturn_line_800094b0, majorreturn_line_800094b4, majorreturn_line_800094b8, majorreturn_line_800094bc, majorreturn_line_800094c0]
    rw [show (2147521704#64 + Functions.sign_extend (BitVec.extractLsb' 12 20 0x0005b797#32 +++ 0#12) +
      Functions.sign_extend (m := 64) 1552#12).toNat = allocatedWordsAddr by decide]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX9498Seg, majorSavedLoads, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
      stepLdsM, ldsRunM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, imm20Of, majorreturn_line_80009498, majorreturn_line_8000949c, majorreturn_line_800094a0, majorreturn_line_800094a4, majorreturn_line_800094a8, majorreturn_line_800094ac, majorreturn_line_800094b0, majorreturn_line_800094b4, majorreturn_line_800094b8, majorreturn_line_800094bc, majorreturn_line_800094c0] at pins
    rw [show Functions.sign_extend (m := 64) 48#12 = 48#64 by decide, nativeStack_restore,
      word 32 s0 (by simp [majorSlots]), word 40 ra (by simp [majorSlots]), word 24 s1 (by simp [majorSlots]),
      word 16 s2 (by simp [majorSlots])] at pins
    exact ⟨gholds_lookup (n := 2) _ pins rfl, gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 18) _ pins rfl, gholds_lookup (n := 9) _ pins rfl,
      gholds_lookup (n := 1) _ pins rfl, gholds_lookup (n := 8) _ pins rfl, trivial⟩
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
