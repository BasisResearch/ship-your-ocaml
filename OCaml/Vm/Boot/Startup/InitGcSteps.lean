import OCaml.Vm.Boot.Startup.InitGcSaveNormalized
import OCaml.Vm.Boot.Startup.InitGcSaveImage
import OCaml.Vm.Boot.Startup.InitGcArgsNormalized
import OCaml.Vm.Boot.Startup.InitGcArgsImage
import OCaml.Vm.Boot.Startup.InitGcMinorNormalized
import OCaml.Vm.Boot.Startup.InitGcMinorImage
import OCaml.Vm.Boot.Startup.InitGcMinorCallInterface
import OCaml.Vm.Boot.Startup.InitGcPolicyNormalized
import OCaml.Vm.Boot.Startup.InitGcPolicyImage
import OCaml.Vm.Boot.Startup.InitGcPolicyCallInterface
import OCaml.Vm.Boot.Startup.InitGcMajorCallNormalized
import OCaml.Vm.Boot.Startup.InitGcMajorCallImage
import OCaml.Vm.Boot.Startup.InitGcMajorCallCallInterface
import OCaml.Vm.Boot.Startup.InitGcArgsCallInterface
import OCaml.Vm.Boot.Startup.InitGcWindowNormalized
import OCaml.Vm.Boot.Startup.InitGcWindowImage
import OCaml.Vm.Boot.Startup.InitGcWindowCallInterface
import OCaml.Vm.Boot.Startup.MajorHeap
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_init_gc's blocks. -/

/-- caml_init_gc's saved registers in its 96-byte frame. -/
def initGcSlots (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64) : List (Nat × BitVec 64) :=
  [(72, s1), (64, s2), (56, s3), (48, s4), (40, s5), (32, s6), (24, s7), (16, s8), (8, s9), (88, ra), (80, s0)]

/-- The page-rounded major heap in bytes. -/
def initGcMajorBytes (wsz : BitVec 64) : BitVec 64 := ((wsz <<< 3) + 4095#64) &&& 0xfffffffffffff000#64

/-- Open a 96-byte frame; save s0–s9 and ra. -/
theorem init_gc_save (c : Config) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 a0 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 96)
    (regs : GHolds c.σ [(2, sp), (9, s1), (18, s2), (19, s3), (20, s4), (21, s5), (22, s6), (23, s7), (24, s8),
      (25, s9), (1, ra), (8, s0), (10, a0)]) :
    FnSummary 0x8001f2c4#64 (fun e => e = c) (WriteRegistersPost [2, 6]
      (nativeWordLog sp 96 (initGcSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9)) c 0x8001f2f8#64 a0
      [(2, nativeStack sp 96), (6, 0xf000#64), (10, a0)]) := by
  have inside : LogInW [⟨nativeFrameBase sp 96, sp.toNat⟩] (nativeWordLog sp 96 (initGcSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9)) :=
    frame.word_log_inside fun off value member => by simp [initGcSlots] at member; omega
  apply registers_of_blocks' leaf.image (frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_gcXf2c4Seg 0x8001f2c4#64
        [(2, sp), (9, s1), (18, s2), (19, s3), (20, s4), (21, s5), (22, s6), (23, s7), (24, s8),
          (25, s9), (1, ra), (8, s0), (10, a0)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 9, 18, 19, 20, 21, 22, 23, 24, 25, 1, 8, 10]; decide
      shape := by change ChainOK _ [2, 9, 18, 19, 20, 21, 22, 23, 24, 25, 1, 8, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := initGcSave_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 96) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 96 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_init_gc_at_"
        · exact (slot 72 (by decide) (by decide)).sd rfl rfl
        · exact (slot 64 (by decide) (by decide)).sd rfl rfl
        · exact (slot 56 (by decide) (by decide)).sd rfl rfl
        · exact (slot 48 (by decide) (by decide)).sd rfl rfl
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 16 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl
        · exact (slot 88 (by decide) (by decide)).sd rfl rfl
        · exact (slot 80 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_gcXf2c4Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG, eraseG,
      wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, initgcsave_line_8001f2c4, initgcsave_line_8001f2c8, initgcsave_line_8001f2cc, initgcsave_line_8001f2d0, initgcsave_line_8001f2d4, initgcsave_line_8001f2d8, initgcsave_line_8001f2dc, initgcsave_line_8001f2e0, initgcsave_line_8001f2e4, initgcsave_line_8001f2e8, initgcsave_line_8001f2ec, initgcsave_line_8001f2f0, initgcsave_line_8001f2f4] at pins
    exact ⟨gholds_lookup (n := 2) _ pins rfl, gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 10) _ pins rfl,
      trivial⟩
  · rfl
  · decide

local macro "iga" : tactic => `(tactic| simp only [initgcargs_line_8001f2f8, initgcargs_line_8001f2fc, initgcargs_line_8001f300, initgcargs_line_8001f304, initgcargs_line_8001f308, initgcargs_line_8001f30c, initgcargs_line_8001f310, initgcargs_line_8001f314, initgcargs_line_8001f318, initgcargs_line_8001f320, initgcargs_line_8001f324, initgcargs_line_8001f328, initgcargs_line_8001f32c, initgcargs_line_8001f330, initgcargs_line_8001f334, initgcargs_line_8001f338, initgcargs_line_8001f33c, initgcargs_line_8001f340, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- The stack arguments; the heap size is at least `Heap_chunk_min` words;
`caml_page_table_initialize(Bsize_wsize(minor) + major)`. -/
theorem init_gc_args (c : Config) (fsp ra a0 a1 a2 a3 a4 a5 a6 a7 arg0 arg1 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(2, fsp), (10, a0), (12, a2), (13, a3), (14, a4), (15, a5), (16, a6), (17, a7), (11, a1),
      (6, 0xf000#64)])
    (window0 : ReadWindow (fsp + 96#64) 8) (window8 : ReadWindow (fsp + 104#64) 8)
    (word0 : bytesT c.σ.mem (fsp + 96#64).toNat 8 = arg0) (word8 : bytesT c.σ.mem (fsp + 104#64).toNat 8 = arg1)
    (bigHeap : 0xf000 ≤ a1.toNat) :
    FnSummary 0x8001f2f8#64 (fun e => e = c) (WriteRegistersPost [18, 19, 9, 20, 21, 22, 23, 24, 25, 15, 8, 10]
      [] c jal_8001f344_call.pc ((a0 <<< 3) + initGcMajorBytes a1)
      [(18, arg0), (19, arg1), (9, a0), (20, a2), (21, a3), (22, a4), (23, a5), (24, a6), (25, a7),
        (15, 0xfffffffffffff000#64), (8, initGcMajorBytes a1), (10, (a0 <<< 3) + initGcMajorBytes a1), (11, a1),
        (2, fsp), (6, 0xf000#64)]) := by
  have w0 : bytesVal .ld (read8 c.σ.mem (fsp + 96#64).toNat) = arg0 := by rw [read8_value]; exact word0
  have w8 : bytesVal .ld (read8 c.σ.mem (fsp + 104#64).toNat) = arg1 := by rw [read8_value]; exact word8
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (caml_init_gcXf2f8TSeg ++ caml_init_gcXf324Seg) 0x8001f2f8#64
        [(2, fsp), (10, a0), (12, a2), (13, a3), (14, a4), (15, a5), (16, a6), (17, a7), (11, a1), (6, 0xf000#64)]
        [read8 c.σ.mem (fsp + 96#64).toNat, read8 c.σ.mem (fsp + 104#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10, 12, 13, 14, 15, 16, 17, 11, 6]; decide
      shape := by change ChainOK _ [2, 10, 12, 13, 14, 15, 16, 17, 11, 6] _; decide
      tick := leaf.tick
      facts := by
        have code := initGcArgs_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_gc_at_"
        · exact window0.ld rfl (by iga; rfl) (read8_pins _ _)
        · exact window8.ld rfl (by iga; rfl) (read8_pins _ _)
        · iga
          unfold guardB Functions.zopz0zKzJ_u
          simp only [Sail.BitVec.toNatInt]
          exact decide_eq_true (Int.ofNat_le.mpr (by simp only [BitVec.toNat_ofNat]; omega)) }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_gcXf2f8TSeg, caml_init_gcXf324Seg, List.cons_append, List.nil_append, evalBlocks, evalBlock,
      SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM, srcVal, lookupG, eraseG, wvalM, Option.getD_some,
      Nat.reduceEqDiff, ite_true, ite_false, imm20Of, List.headD_cons, List.tail_cons, initgcargs_line_8001f2f8, initgcargs_line_8001f2fc, initgcargs_line_8001f300, initgcargs_line_8001f304, initgcargs_line_8001f308, initgcargs_line_8001f30c, initgcargs_line_8001f310, initgcargs_line_8001f314, initgcargs_line_8001f318, initgcargs_line_8001f320, initgcargs_line_8001f324, initgcargs_line_8001f328, initgcargs_line_8001f32c, initgcargs_line_8001f330, initgcargs_line_8001f334, initgcargs_line_8001f338, initgcargs_line_8001f33c, initgcargs_line_8001f340] at pins
    rw [slli_three _ _ rfl, slli_three _ _ rfl,
      show Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 6071#32 +++ 0#12) +
        Functions.sign_extend (m := 64) 4095#12 = 4095#64 by decide,
      show Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 4294965175#32 +++ 0#12) =
        0xfffffffffffff000#64 by decide, sext_zero, w0, w8] at pins
    simp only [BitVec.add_zero] at pins
    exact ⟨gholds_lookup (n := 18) _ pins rfl, gholds_lookup (n := 19) _ pins rfl, gholds_lookup (n := 9) _ pins rfl,
      gholds_lookup (n := 20) _ pins rfl, gholds_lookup (n := 21) _ pins rfl, gholds_lookup (n := 22) _ pins rfl,
      gholds_lookup (n := 23) _ pins rfl, gholds_lookup (n := 24) _ pins rfl, gholds_lookup (n := 25) _ pins rfl,
      gholds_lookup (n := 15) _ pins rfl, gholds_lookup (n := 8) _ pins rfl, gholds_lookup (n := 10) _ pins rfl,
      gholds_lookup (n := 11) _ pins rfl, gholds_lookup (n := 2) _ pins rfl, gholds_lookup (n := 6) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- `caml_page_table_initialize` succeeded; the minor heap size (262144
words) is in range; `caml_set_minor_heap_size(caml_norm_minsize(…))`. -/
theorem init_gc_minor_front (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, 0#64), (9, 262144#64)]) :
    FnSummary 0x8001f348#64 (fun e => e = c) (WriteRegistersPost [15, 10] [] c jal_8001f36c_call.pc 0x200000#64
      [(15, 4096#64), (10, 0x200000#64), (9, 262144#64)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (caml_init_gcXf348FSeg ++ caml_init_gcXf34cFSeg ++ caml_init_gcXf358FSeg ++
        caml_init_gcXf360Seg) 0x8001f348#64 [(10, 0#64), (9, 262144#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 9]; decide
      shape := by change ChainOK _ [10, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := initGcMinor_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_gc_at_"
        all_goals simp only [initgcminor_line_8001f34c, initgcminor_line_8001f350, initgcminor_line_8001f358, initgcminor_line_8001f360, initgcminor_line_8001f364, initgcminor_line_8001f368, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
          ite_false, Nat.reduceEqDiff, imm20Of]
        all_goals decide }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_gcXf348FSeg, caml_init_gcXf34cFSeg, caml_init_gcXf358FSeg, caml_init_gcXf360Seg,
      List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, initgcminor_line_8001f34c, initgcminor_line_8001f350, initgcminor_line_8001f358, initgcminor_line_8001f360, initgcminor_line_8001f364, initgcminor_line_8001f368] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup (n := 9) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- `caml_percent_free`, `caml_percent_max`. -/
def percentFreeAddr : Nat := 0x80064af0
def percentMaxAddr : Nat := 0x80064c60

local macro "igp" : tactic => `(tactic| simp only [initgcpolicy_line_8001f370, initgcpolicy_line_8001f374, initgcpolicy_line_8001f378, initgcpolicy_line_8001f37c, initgcpolicy_line_8001f380, initgcpolicy_line_8001f388, initgcpolicy_line_8001f38c, initgcpolicy_line_8001f390, initgcpolicy_line_8001f394, initgcpolicy_line_8001f398, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, List.headD_cons])

/-- `caml_major_heap_increment = 15`; `caml_percent_free`'s value is nonzero. -/
theorem init_gc_increment (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(20, 15#64), (21, 120#64), (10, 0#64)]) :
    FnSummary 0x8001f370#64 (fun e => e = c) (WriteRegistersPost [15, 9] [(majorIncrementAddr, 8, 15#64)] c 0x8001f388#64 0#64
      [(15, 120#64), (9, BitVec.ofNat 64 percentFreeAddr), (20, 15#64), (21, 120#64), (10, 0#64)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> simp only [OutLRange, majorIncrementAddr] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_gcXf370FSeg 0x8001f370#64 [(20, 15#64), (21, 120#64), (10, 0#64)]
        [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [20, 21, 10]; decide
      shape := by change ChainOK _ [20, 21, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := initGcPolicy_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_gc_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 majorIncrementAddr) 8 by constructor <;> decide).sd rfl (by igp; decide)
        · igp; decide }))
  · simp only [caml_init_gcXf370FSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM, widthOfM]
    igp
    decide
  · rfl
  · intro σ pins
    simp only [caml_init_gcXf370FSeg, evalBlocks, evalBlock, SegEvalState.init] at pins
    simp only [initgcpolicy_line_8001f370, initgcpolicy_line_8001f374, initgcpolicy_line_8001f378, initgcpolicy_line_8001f37c, initgcpolicy_line_8001f380, initgcpolicy_line_8001f388, initgcpolicy_line_8001f38c, initgcpolicy_line_8001f390, initgcpolicy_line_8001f394, initgcpolicy_line_8001f398, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, List.headD_cons] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 20) _ pins rfl,
      gholds_lookup (n := 21) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- `caml_percent_free = 120`, `caml_percent_max = 500`; `caml_set_allocation_policy(2)`. -/
theorem init_gc_percent (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(19, 2#64), (15, 120#64), (9, BitVec.ofNat 64 percentFreeAddr), (22, 500#64)]) :
    FnSummary 0x8001f388#64 (fun e => e = c) (WriteRegistersPost [10, 19]
      [(percentFreeAddr, 8, 120#64), (percentMaxAddr, 8, 500#64)] c jal_8001f39c_call.pc 2#64
      [(10, 2#64), (19, BitVec.ofNat 64 percentMaxAddr), (15, 120#64), (9, BitVec.ofNat 64 percentFreeAddr),
        (22, 500#64)]) := by
  apply registers_of_blocks' leaf.image
    (by constructor <;> simp only [OutLRange, percentFreeAddr, percentMaxAddr] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_gcXf388Seg 0x8001f388#64
        [(19, 2#64), (15, 120#64), (9, BitVec.ofNat 64 percentFreeAddr), (22, 500#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [19, 15, 9, 22]; decide
      shape := by change ChainOK _ [19, 15, 9, 22] _; decide
      tick := leaf.tick
      facts := by
        have code := initGcPolicy_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_gc_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 percentFreeAddr) 8 by constructor <;> decide).sd rfl (by igp; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 percentMaxAddr) 8 by constructor <;> decide).sd rfl (by igp; decide) }))
  · simp only [caml_init_gcXf388Seg, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM, widthOfM]
    igp
    decide
  · rfl
  · intro σ pins
    simp only [caml_init_gcXf388Seg, evalBlocks, evalBlock, SegEvalState.init] at pins
    simp only [initgcpolicy_line_8001f370, initgcpolicy_line_8001f374, initgcpolicy_line_8001f378, initgcpolicy_line_8001f37c, initgcpolicy_line_8001f380, initgcpolicy_line_8001f388, initgcpolicy_line_8001f38c, initgcpolicy_line_8001f390, initgcpolicy_line_8001f394, initgcpolicy_line_8001f398, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, List.headD_cons] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 15) _ pins rfl,
      gholds_lookup (n := 9) _ pins rfl, gholds_lookup (n := 22) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- `caml_init_major_heap(major_bytes)`. -/
theorem init_gc_major_front (c : Config) (ra bytes v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, bytes), (10, v)]) :
    FnSummary 0x8001f3a0#64 (fun e => e = c) (WriteRegistersPost [10] [] c jal_8001f3a4_call.pc bytes
      [(10, bytes), (8, bytes)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_gcXf3a0Seg 0x8001f3a0#64 [(8, bytes), (10, v)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 10]; decide
      shape := by change ChainOK _ [8, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := initGcMajorCall_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_gc_at_" }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_gcXf3a0Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG, eraseG,
      wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, initgcmajorcall_line_8001f3a0] at pins
    exact ⟨gholds_lookup_eq pins rfl (by rw [sext_zero, BitVec.add_zero]), gholds_lookup (n := 8) _ pins rfl, trivial⟩
  · rfl
  · decide

local macro "igw" : tactic => `(tactic| simp only [initgcwindow_line_8001f3a8, initgcwindow_line_8001f3ac, initgcwindow_line_8001f3b8, initgcwindow_line_8001f3bc, initgcwindow_line_8001f3c0, initgcwindow_line_8001f3c4, initgcwindow_line_8001f3cc, initgcwindow_line_8001f3d0, initgcwindow_line_8001f3d4, initgcwindow_line_8001f3dc, initgcwindow_line_8001f3e0, initgcwindow_line_8001f3e4, initgcwindow_line_8001f3e8, initgcwindow_line_8001f3ec, initgcwindow_line_8001f3f0, initgcwindow_line_8001f3f4, initgcwindow_line_8001f3f8, initgcwindow_line_8001f3fc, initgcwindow_line_8001f400, initgcwindow_line_8001f404, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- `caml_major_window`, `caml_custom_major_ratio`, `caml_custom_minor_ratio`, `caml_custom_minor_max_bsz`. -/
def majorWindowAddr : Nat := 0x80064858
def customMajorAddr : Nat := 0x800648c0
def customMinorAddr : Nat := 0x800648b8
def customMaxAddr : Nat := 0x800648b0

/-- The window (1) is within `1..Max_major_window`. -/
theorem init_gc_window_check (c : Config) (ra v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(23, 1#64), (10, v)]) :
    FnSummary 0x8001f3a8#64 (fun e => e = c) (WriteRegistersPost [14, 15] [] c 0x8001f3bc#64 v
      [(14, 50#64), (15, 1#64), (23, 1#64), (10, v)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (caml_init_gcXf3a8FSeg ++ caml_init_gcXf3b4TSeg) 0x8001f3a8#64
        [(23, 1#64), (10, v)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [23, 10]; decide
      shape := by change ChainOK _ [23, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := initGcWindow_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_gc_at_"
        all_goals igw
        all_goals decide }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_gcXf3a8FSeg, caml_init_gcXf3b4TSeg, List.cons_append, List.nil_append, evalBlocks, evalBlock,
      SegEvalState.init, initgcwindow_line_8001f3a8, initgcwindow_line_8001f3ac, initgcwindow_line_8001f3b8, initgcwindow_line_8001f3bc, initgcwindow_line_8001f3c0, initgcwindow_line_8001f3c4, initgcwindow_line_8001f3cc, initgcwindow_line_8001f3d0, initgcwindow_line_8001f3d4, initgcwindow_line_8001f3dc, initgcwindow_line_8001f3e0, initgcwindow_line_8001f3e4, initgcwindow_line_8001f3e8, initgcwindow_line_8001f3ec, initgcwindow_line_8001f3f0, initgcwindow_line_8001f3f4, initgcwindow_line_8001f3f8, initgcwindow_line_8001f3fc, initgcwindow_line_8001f400, initgcwindow_line_8001f404, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
      ite_false, Nat.reduceEqDiff, Nat.reduceAdd, imm20Of] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 23) _ pins rfl,
      gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- `caml_major_window = 1`; the custom major ratio (44) is nonzero. -/
theorem init_gc_window_store (c : Config) (ra v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, 1#64), (24, 44#64), (10, v)]) :
    FnSummary 0x8001f3bc#64 (fun e => e = c) (WriteRegistersPost [14, 15] [(majorWindowAddr, 4, 1#64)] c 0x8001f3cc#64 v
      [(14, 0x800643bc#64), (15, 44#64), (24, 44#64), (10, v)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> simp only [OutLRange, majorWindowAddr] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_gcXf3bcFSeg 0x8001f3bc#64 [(15, 1#64), (24, 44#64), (10, v)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 24, 10]; decide
      shape := by change ChainOK _ [15, 24, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := initGcWindow_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_gc_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 majorWindowAddr) 4 by constructor <;> decide).sw rfl (by igw; decide)
        · igw; decide }))
  · simp only [caml_init_gcXf3bcFSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM, widthOfM]
    igw
    decide
  · rfl
  · intro σ pins
    simp only [caml_init_gcXf3bcFSeg, evalBlocks, evalBlock, SegEvalState.init] at pins
    simp only [initgcwindow_line_8001f3a8, initgcwindow_line_8001f3ac, initgcwindow_line_8001f3b8, initgcwindow_line_8001f3bc, initgcwindow_line_8001f3c0, initgcwindow_line_8001f3c4, initgcwindow_line_8001f3cc, initgcwindow_line_8001f3d0, initgcwindow_line_8001f3d4, initgcwindow_line_8001f3dc, initgcwindow_line_8001f3e0, initgcwindow_line_8001f3e4, initgcwindow_line_8001f3e8, initgcwindow_line_8001f3ec, initgcwindow_line_8001f3f0, initgcwindow_line_8001f3f4, initgcwindow_line_8001f3f8, initgcwindow_line_8001f3fc, initgcwindow_line_8001f400, initgcwindow_line_8001f404, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- `caml_custom_major_ratio = 44`; the custom minor ratio (100) is nonzero. -/
theorem init_gc_custom_major (c : Config) (ra v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, 44#64), (25, 100#64), (10, v)]) :
    FnSummary 0x8001f3cc#64 (fun e => e = c) (WriteRegistersPost [14, 15] [(customMajorAddr, 8, 44#64)] c 0x8001f3dc#64 v
      [(14, 0x800643cc#64), (15, 100#64), (25, 100#64), (10, v)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> simp only [OutLRange, customMajorAddr] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_gcXf3ccFSeg 0x8001f3cc#64 [(15, 44#64), (25, 100#64), (10, v)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 25, 10]; decide
      shape := by change ChainOK _ [15, 25, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := initGcWindow_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_gc_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 customMajorAddr) 8 by constructor <;> decide).sd rfl (by igw; decide)
        · igw; decide }))
  · simp only [caml_init_gcXf3ccFSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM, widthOfM]
    igw
    decide
  · rfl
  · intro σ pins
    simp only [caml_init_gcXf3ccFSeg, evalBlocks, evalBlock, SegEvalState.init] at pins
    simp only [initgcwindow_line_8001f3a8, initgcwindow_line_8001f3ac, initgcwindow_line_8001f3b8, initgcwindow_line_8001f3bc, initgcwindow_line_8001f3c0, initgcwindow_line_8001f3c4, initgcwindow_line_8001f3cc, initgcwindow_line_8001f3d0, initgcwindow_line_8001f3d4, initgcwindow_line_8001f3dc, initgcwindow_line_8001f3e0, initgcwindow_line_8001f3e4, initgcwindow_line_8001f3e8, initgcwindow_line_8001f3ec, initgcwindow_line_8001f3f0, initgcwindow_line_8001f3f4, initgcwindow_line_8001f3f8, initgcwindow_line_8001f3fc, initgcwindow_line_8001f400, initgcwindow_line_8001f404, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- The custom minor parameters; the first message's arguments:
`Caml_state->minor_heap_wsz / 1024`. -/
def initGcCustomLog : List WEntry := [(customMinorAddr, 8, 100#64), (customMaxAddr, 8, 8192#64)]

theorem init_gc_custom_minor (c : Config) (ra v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, 100#64), (18, 8192#64), (10, v)])
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr)
    (minorWsz : bytesT c.σ.mem (domainField 80) 8 = 262144#64) :
    FnSummary 0x8001f3dc#64 (fun e => e = c) (WriteRegistersPost [14, 15, 11, 10, 12] initGcCustomLog c
      jal_8001f408_call.pc 32#64
      [(14, 0x800643dc#64), (15, firstDomainPtr), (11, 0x80057750#64), (10, 32#64), (12, 256#64), (18, 8192#64)]) := by
  have dw : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat) = firstDomainPtr := by
    rw [read8_value]; exact domain
  have mw : bytesVal .ld (read8 c.σ.mem (firstDomainPtr + 80#64).toNat) = 262144#64 := by
    rw [read8_value]; exact minorWsz
  apply registers_of_blocks' leaf.image
    (by constructor <;> simp only [initGcCustomLog, OutLRange, customMinorAddr, customMaxAddr] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_gcXf3dcSeg 0x8001f3dc#64 [(15, 100#64), (18, 8192#64), (10, v)]
        [read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat, read8 c.σ.mem (firstDomainPtr + 80#64).toNat] c
        from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 18, 10]; decide
      shape := by change ChainOK _ [15, 18, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := initGcWindow_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_gc_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 customMinorAddr) 8 by constructor <;> decide).sd rfl (by igw; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 customMaxAddr) 8 by constructor <;> decide).sd rfl (by igw; decide)
        · past_stores
          · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 by constructor <;> decide).ld rfl
              (by igw; decide) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, and_true]; igw; (try rw [dw]); decide)
        · past_stores
          · exact (show ReadWindow (firstDomainPtr + 80#64) 8 by constructor <;> decide).ld rfl
              (by igw; rw [dw]; decide) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, and_true]; igw; (try rw [dw]); decide) }))
  · simp only [caml_init_gcXf3dcSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM, widthOfM]
    igw
    decide
  · rfl
  · intro σ pins
    simp only [caml_init_gcXf3dcSeg, evalBlocks, evalBlock, SegEvalState.init] at pins
    simp only [initgcwindow_line_8001f3a8, initgcwindow_line_8001f3ac, initgcwindow_line_8001f3b8, initgcwindow_line_8001f3bc, initgcwindow_line_8001f3c0, initgcwindow_line_8001f3c4, initgcwindow_line_8001f3cc, initgcwindow_line_8001f3d0, initgcwindow_line_8001f3d4, initgcwindow_line_8001f3dc, initgcwindow_line_8001f3e0, initgcwindow_line_8001f3e4, initgcwindow_line_8001f3e8, initgcwindow_line_8001f3ec, initgcwindow_line_8001f3f0, initgcwindow_line_8001f3f4, initgcwindow_line_8001f3f8, initgcwindow_line_8001f3fc, initgcwindow_line_8001f400, initgcwindow_line_8001f404, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons] at pins
    rw [mw, srli_ten _ _ rfl] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl dw, gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 18) _ pins rfl,
      trivial⟩
  · rfl
  · decide

end OCaml.Vm.Boot.Startup
