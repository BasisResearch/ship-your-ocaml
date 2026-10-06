import OCaml.Vm.Boot.Startup.NewNodePrologueNormalized
import OCaml.Vm.Boot.Startup.NewNodePrologueImage
import OCaml.Vm.Boot.Startup.NewNodeScanNormalized
import OCaml.Vm.Boot.Startup.NewNodeScanImage
import OCaml.Vm.Boot.Startup.NewNodeAllocNormalized
import OCaml.Vm.Boot.Startup.NewNodeAllocCallInterface
import OCaml.Vm.Boot.Startup.NewNodeCopyNormalized
import OCaml.Vm.Boot.Startup.NewNodeCopyCallInterface
import OCaml.Vm.Boot.Startup.NewNodeInitNormalized
import OCaml.Vm.Boot.Startup.NewNodeInitImage
import OCaml.Vm.Boot.Startup.NewNodeReturnNormalized
import OCaml.Vm.Boot.Startup.NewNodeReturnImage
import OCaml.Vm.Boot.Startup.BlockCall
import OCaml.Vm.Boot.Startup.ChildScan
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-! htif.c's `new_node(d, n, k, dir)` when slot 1 is free: the name is copied
into a fresh `malloc(k + 1)` buffer and slot 1 initialized. -/

def newNodeSlots (ra s0 : BitVec 64) : List (Nat × BitVec 64) := [(48, s0), (56, ra)]
def newNodeLog (sp ra s0 : BitVec 64) : List WEntry := nativeWordLog sp 64 (newNodeSlots ra s0)
def newNodeInput (sp ra s0 d name k dir : BitVec 64) : GRegs :=
  [(2, sp), (8, s0), (1, ra), (10, d), (11, name), (12, k), (13, dir)]

theorem newNodeLog_inside {sp ra s0} (frame : NativeFrame sp 64) :
    LogInW [⟨nativeFrameBase sp 64, sp.toNat⟩] (newNodeLog sp ra s0) := by
  apply frame.word_log_inside
  intro off value member
  simp only [newNodeSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  omega

def newNodeSaved (sp ra d name k dir : BitVec 64) : GRegs :=
  [(16, 64#64), (8, 1#64), (15, childFirst), (2, nativeStack sp 64), (1, ra), (10, d), (11, name), (12, k), (13, dir)]

theorem new_node_save (c : Config) (sp ra s0 d name k dir : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ (newNodeInput sp ra s0 d name k dir)) :
    FnSummary 0x800000f0#64 (fun e => e = c)
      (WriteRegistersPost [2, 15, 8, 16] (newNodeLog sp ra s0) c 0x80000118#64 d
        (newNodeSaved sp ra d name k dir)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (newNodeLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput new_nodeX00f0Seg 0x800000f0#64
        (newNodeInput sp ra s0 d name k dir) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 8, 1, 10, 11, 12, 13]; decide
      shape := by change ChainOK _ [2, 8, 1, 10, 11, 12, 13] _; decide
      tick := leaf.tick
      facts := by
        have code := newNodePrologue_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 64) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 64 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.new_node_at_"
        · exact (slot 48 (by decide) (by decide)).sd rfl rfl
        · exact (slot 56 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · simp only [new_nodeX00f0Seg, evalBlocks, evalBlock, SegEvalState.init, newnodeprologue_line_800000f0, newnodeprologue_line_800000f4, newnodeprologue_line_800000f8, newnodeprologue_line_800000fc, newnodeprologue_line_80000100, newnodeprologue_line_80000104, newnodeprologue_line_80000108, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, newNodeInput, newNodeSaved]
    have down : Functions.sign_extend (m := 64) 4032#12 = -BitVec.ofNat 64 64 := by decide
    rw [down]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and, nativeStack]
    decide
  · rfl
  · decide

def newNodeFound (sp ra d name k dir : BitVec 64) : GRegs :=
  [(15, childFirst + 56#64), (14, 0#64), (16, 64#64), (8, 1#64), (2, nativeStack sp 64), (1, ra), (10, d),
    (11, name), (12, k), (13, dir)]

/-- Slot 1 is free: leave the scan. -/
theorem new_node_free (c : Config) (sp ra d name k dir : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (newNodeSaved sp ra d name k dir))
    (free : (c.σ.mem[Layout.sym_files + 56]?).getD 0 = 0#8) :
    FnSummary 0x80000118#64 (fun e => e = c)
      (WriteRegistersPost [14, 15] [] c 0x80000124#64 d (newNodeFound sp ra d name k dir)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput new_nodeX0118FSeg 0x80000118#64
        (newNodeSaved sp ra d name k dir) [[0#8]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [16, 8, 15, 2, 1, 10, 11, 12, 13]; decide
      shape := by change ChainOK _ [16, 8, 15, 2, 1, 10, 11, 12, 13] _; decide
      tick := leaf.tick
      facts := by
        have code := newNodeScan_code leaf.image
        chain_facts code with "Vsa.Sim.Code.new_node_at_"
        · exact (show ReadWindow childFirst 1 by constructor <;> decide).lbu rfl
            (by change childFirst + 0#64 = _; rw [BitVec.add_zero]) (by rw [show childFirst.toNat = Layout.sym_files + 56 by decide]; exact free)
        · rfl }))
  · rfl
  · rfl
  · simp only [new_nodeX0118FSeg, evalBlocks, evalBlock, SegEvalState.init, newnodescan_line_80000118, newnodescan_line_8000011c, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, newNodeSaved, newNodeFound]
    rw [show Functions.sign_extend (m := 64) 56#12 = 56#64 by decide]
    rfl
  · rfl
  · decide
def newNodeAllocSlots (s1 s2 s3 name : BitVec 64) : List (Nat × BitVec 64) := [(24, s3), (40, s1), (32, s2), (8, name)]
def newNodeAllocLog (sp s1 s2 s3 name : BitVec 64) : List WEntry := nativeWordLog sp 64 (newNodeAllocSlots s1 s2 s3 name)
def newNodeAllocInput (sp d name k dir s1 s2 s3 : BitVec 64) : GRegs :=
  [(15, childFirst + 56#64), (14, 0#64), (16, 64#64), (8, 1#64), (2, nativeStack sp 64), (10, d),
    (11, name), (12, k), (13, dir), (9, s1), (18, s2), (19, s3)]

theorem newNodeAllocLog_inside {sp s1 s2 s3 name} (frame : NativeFrame sp 64) :
    LogInW [⟨nativeFrameBase sp 64, sp.toNat⟩] (newNodeAllocLog sp s1 s2 s3 name) := by
  apply frame.word_log_inside
  intro off value member
  simp only [newNodeAllocSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  omega

def newNodeAllocated (sp d name k dir : BitVec 64) : GRegs :=
  [(18, dir), (9, k), (10, k + 1#64), (19, d), (15, childFirst + 56#64), (14, 0#64), (16, 64#64), (8, 1#64),
    (2, nativeStack sp 64), (11, name), (12, k), (13, dir)]

theorem new_node_alloc_save (c : Config) (sp d name k dir s1 s2 s3 oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ (newNodeAllocInput sp d name k dir s1 s2 s3)) :
    FnSummary 0x80000124#64 (fun e => e = c)
      (WriteRegistersPost [19, 10, 9, 18] (newNodeAllocLog sp s1 s2 s3 name) c jal_80000144_call.pc
        (k + 1#64) (newNodeAllocated sp d name k dir)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (newNodeAllocLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput newNodeAllocSave 0x80000124#64
        (newNodeAllocInput sp d name k dir s1 s2 s3) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 14, 16, 8, 2, 10, 11, 12, 13, 9, 18, 19]; decide
      shape := by change ChainOK _ [15, 14, 16, 8, 2, 10, 11, 12, 13, 9, 18, 19] _; decide
      tick := leaf.tick
      facts := by
        have code := newNodeAlloc_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 64) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 64 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.new_node_at_"
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · simp only [newNodeAllocSave, evalBlocks, evalBlock, SegEvalState.init, newnodealloc_line_80000124, newnodealloc_line_80000128, newnodealloc_line_8000012c, newnodealloc_line_80000130, newnodealloc_line_80000134, newnodealloc_line_80000138, newnodealloc_line_8000013c, newnodealloc_line_80000140, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, newNodeAllocInput,
      newNodeAllocated]
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
      show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide, BitVec.add_zero, BitVec.add_zero, BitVec.add_zero]
  · rfl
  · decide

/-- Save s1–s3 and the name, then call `malloc(k + 1)`. -/
theorem new_node_alloc_call (c : Config) (sp d name k dir s1 s2 s3 oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ (newNodeAllocInput sp d name k dir s1 s2 s3)) :
    FnSummary 0x80000124#64 (fun e => e = c)
      (WriteRegistersPost ([19, 10, 9, 18] ++ [1]) (newNodeAllocLog sp s1 s2 s3 name) c jal_80000144_call.target
        (k + 1#64) ((1, jal_80000144_call.link) :: newNodeAllocated sp d name k dir)) :=
  block_then_call c jal_80000144_call_shape jal_80000144_call_decode (fun _ h => jal_80000144_call_pins h)
    (new_node_alloc_save c sp d name k dir s1 s2 s3 oldra leaf frame regs)
    (by simp only [newNodeAllocated, keysG]; decide) (by simp only [newNodeAllocated, KeysAvoidRa, keysG]; decide) rfl
def newNodeCopyLog (sp p : BitVec 64) : List WEntry := nativeWordLog sp 64 [(8, p)]

theorem new_node_copy_save (c : Config) (sp p name k oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ [(10, p), (2, nativeStack sp 64), (9, k)])
    (nonnull : p ≠ 0#64) (saved : bytesT c.σ.mem (nativeFrameBase sp 64 + 8) 8 = name) :
    FnSummary 0x80000148#64 (fun e => e = c)
      (WriteRegistersPost [11, 12] (newNodeCopyLog sp p) c jal_80000158_call.pc p
        [(12, k), (11, name), (10, p), (2, nativeStack sp 64), (9, k)]) := by
  apply registers_of_blocks leaf.image (frame.image_outside (frame.word_log_inside (slots := [(8, p)])
      (fun off value member => by simp at member; omega)))
    (block_summary _ _ _ _ _ (show BlockInput (new_nodeX0148FSeg ++ newNodeCopySave) 0x80000148#64
        [(10, p), (2, nativeStack sp 64), (9, k)] [read8 c.σ.mem (nativeFrameBase sp 64 + 8)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 2, 9]; decide
      shape := by change ChainOK _ [10, 2, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := newNodeCopy_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 64) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 64 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.new_node_at_"
        · change guardB bop.BEQ p 0#64 = false
          exact beq_eq_false_iff_ne.mpr nonnull
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · simp only [new_nodeX0148FSeg, newNodeCopySave, evalBlocks, evalBlock, SegEvalState.init, newnodecopy_line_8000014c, newnodecopy_line_80000150, newnodecopy_line_80000154,
      runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM,
      List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.cons_append,
      List.nil_append]
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, read8_value, saved]
  · rfl
  · decide

/-- Reload the name and call `memcpy(p, name, k)`. -/
theorem new_node_copy_call (c : Config) (sp p name k oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ [(10, p), (2, nativeStack sp 64), (9, k)])
    (nonnull : p ≠ 0#64) (saved : bytesT c.σ.mem (nativeFrameBase sp 64 + 8) 8 = name) :
    FnSummary 0x80000148#64 (fun e => e = c)
      (WriteRegistersPost ([11, 12] ++ [1]) (newNodeCopyLog sp p) c jal_80000158_call.target p
        ((1, jal_80000158_call.link) :: [(12, k), (11, name), (10, p), (2, nativeStack sp 64), (9, k)])) :=
  block_then_call c jal_80000158_call_shape jal_80000158_call_decode (fun _ h => jal_80000158_call_pins h)
    (new_node_copy_save c sp p name k oldra leaf frame regs nonnull saved)
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
/-- Slot 1 of `files`. -/
def slotOne : Nat := Layout.sym_files + 56

def newNodeInitLog (p k d dir : BitVec 64) : List WEntry :=
  [(slotOne, 8, 0#64), (slotOne + 1, 1, dir), (slotOne + 24, 8, 0#64), (slotOne + 32, 8, 0#64),
   (slotOne + 40, 8, 0#64), (slotOne + 48, 8, 0#64), (slotOne + 4, 4, d), (slotOne + 8, 8, p),
   (slotOne + 16, 8, k), ((p + k).toNat, 1, 0#64), (slotOne, 1, 1#64), (slotOne + 2, 1, 1#64)]

def newNodeInitRegs (sp p k d dir : BitVec 64) : GRegs :=
  [(13, 1#64), (12, p + k), (15, childFirst), (14, p), (8, 1#64), (2, nativeStack sp 64), (9, k), (18, dir), (19, d),
    (10, p)]

/-- A store window inside slot 1 of `files`. -/
theorem slotOne_write (off w : Nat) (fits : off + w ≤ 56) (aligned : (Layout.sym_files + 56 + off) % w = 0) :
    WriteWindow (childFirst + BitVec.ofNat 64 off) w := by
  have nat : (childFirst + BitVec.ofNat 64 off).toNat = Layout.sym_files + 56 + off := by
    unfold childFirst Layout.sym_files at *
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  constructor <;> rw [nat] <;> unfold Layout.sym_files at * <;> first | omega | (unfold Layout.sym_tohost; omega)

local macro "init_addr" : tactic =>
  `(tactic| (simp only [newnodeinit_line_8000015c, newnodeinit_line_80000160, newnodeinit_line_80000164, newnodeinit_line_80000168, newnodeinit_line_8000016c, newnodeinit_line_80000170, newnodeinit_line_80000174, newnodeinit_line_80000178, newnodeinit_line_8000017c, newnodeinit_line_80000180, newnodeinit_line_80000184, newnodeinit_line_80000188, newnodeinit_line_8000018c, newnodeinit_line_80000190, newnodeinit_line_80000194, newnodeinit_line_80000198, newnodeinit_line_8000019c, newnodeinit_line_800001a0, newnodeinit_line_800001a4, newnodeinit_line_800001a8, newnodeinit_line_800001ac, eaddrM, srcVal, lookupG, runGM, stepGM,
    eraseG, wvalM, Option.getD_some, ite_true, ite_false, imm20Of, Nat.reduceEqDiff]; decide))

theorem new_node_init (c : Config) (sp p k d dir oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 64)
    (regs : GHolds c.σ [(8, 1#64), (2, nativeStack sp 64), (9, k), (18, dir), (19, d), (10, p)])
    (saved : bytesT c.σ.mem (nativeFrameBase sp 64 + 8) 8 = p)
    (arena : Vsa.Sim.DlHeap.heapStart ≤ (p + k).toNat ∧ (p + k).toNat < Vsa.Sim.DlHeap.heapEnd) :
    FnSummary 0x8000015c#64 (fun e => e = c)
      (WriteRegistersPost [15, 14, 12, 13] (newNodeInitLog p k d dir) c 0x800001b0#64 p
        (newNodeInitRegs sp p k d dir)) := by
  have slotW := slotOne_write
  have heapBounds : 0x80000000 ≤ Vsa.Sim.DlHeap.heapStart ∧ Vsa.Sim.DlHeap.heapEnd ≤ 0x100000000 ∧
      Layout.sym_tohost + 16 ≤ Vsa.Sim.DlHeap.heapStart ∧ Image.textBase + Image.textSize ≤ slotOne ∧
      Image.rodataBase + Image.rodataSize ≤ slotOne ∧ Image.textBase + Image.textSize ≤ Vsa.Sim.DlHeap.heapStart ∧
      Image.rodataBase + Image.rodataSize ≤ Vsa.Sim.DlHeap.heapStart := by decide
  apply registers_of_blocks leaf.image (by
      constructor <;> simp only [newNodeInitLog, OutLRange] <;>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega)
    (block_summary _ _ _ _ _ (show BlockInput new_nodeX015cSeg 0x8000015c#64
        [(8, 1#64), (2, nativeStack sp 64), (9, k), (18, dir), (19, d), (10, p)]
        [read8 c.σ.mem (nativeFrameBase sp 64 + 8)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 2, 9, 18, 19, 10]; decide
      shape := by change ChainOK _ [8, 2, 9, 18, 19, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := newNodeInit_code leaf.image
        chain_facts code with "Vsa.Sim.Code.new_node_at_"
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (slotW 0 8 (by decide) (by decide)).sd rfl (by init_addr)
        · exact (slotW 1 1 (by decide) (by decide)).sb rfl (by init_addr)
        · exact (slotW 24 8 (by decide) (by decide)).sd rfl (by init_addr)
        · exact (slotW 32 8 (by decide) (by decide)).sd rfl (by init_addr)
        · exact (slotW 40 8 (by decide) (by decide)).sd rfl (by init_addr)
        · exact (slotW 48 8 (by decide) (by decide)).sd rfl (by init_addr)
        · exact (slotW 4 4 (by decide) (by decide)).sw rfl (by init_addr)
        · exact (slotW 8 8 (by decide) (by decide)).sd rfl (by init_addr)
        · exact (slotW 16 8 (by decide) (by decide)).sd rfl (by init_addr)
        · exact (show WriteWindow (p + k) 1 from ⟨by omega, by omega, by omega, Nat.mod_one _⟩).sb rfl
            (by change bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 8)) + k +
                  Functions.sign_extend (m := 64) 0#12 = p + k
                rw [read8_value, saved, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero])
        · exact (slotW 0 1 (by decide) (by decide)).sb rfl (by init_addr)
        · exact (slotW 2 1 (by decide) (by decide)).sb rfl (by init_addr) }))
  · simp only [new_nodeX015cSeg, evalBlocks, evalBlock, SegEvalState.init, newnodeinit_line_8000015c, newnodeinit_line_80000160, newnodeinit_line_80000164, newnodeinit_line_80000168, newnodeinit_line_8000016c, newnodeinit_line_80000170, newnodeinit_line_80000174, newnodeinit_line_80000178, newnodeinit_line_8000017c, newnodeinit_line_80000180, newnodeinit_line_80000184, newnodeinit_line_80000188, newnodeinit_line_8000018c, newnodeinit_line_80000190, newnodeinit_line_80000194, newnodeinit_line_80000198, newnodeinit_line_8000019c, newnodeinit_line_800001a0, newnodeinit_line_800001a4, newnodeinit_line_800001a8, newnodeinit_line_800001ac, runGM, ldsRunM,
      wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, newNodeInitLog,
      List.nil_append, read8_value, saved]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      ?_, by decide, by decide⟩
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]
  · rfl
  · simp only [new_nodeX015cSeg, evalBlocks, evalBlock, SegEvalState.init, newnodeinit_line_8000015c, newnodeinit_line_80000160, newnodeinit_line_80000164, newnodeinit_line_80000168, newnodeinit_line_8000016c, newnodeinit_line_80000170, newnodeinit_line_80000174, newnodeinit_line_80000178, newnodeinit_line_8000017c, newnodeinit_line_80000180, newnodeinit_line_80000184, newnodeinit_line_80000188, newnodeinit_line_8000018c, newnodeinit_line_80000190, newnodeinit_line_80000194, newnodeinit_line_80000198, newnodeinit_line_8000019c, newnodeinit_line_800001a0, newnodeinit_line_800001a4, newnodeinit_line_800001a8, newnodeinit_line_800001ac, runGM, ldsRunM,
      wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, newNodeInitRegs,
      read8_value, saved]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    exact ⟨by decide, by decide⟩
  · rfl
  · decide
def newNodeReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 64 + 56), read8 c.σ.mem (nativeFrameBase sp 64 + 48),
   read8 c.σ.mem (nativeFrameBase sp 64 + 40), read8 c.σ.mem (nativeFrameBase sp 64 + 32),
   read8 c.σ.mem (nativeFrameBase sp 64 + 24)]

/-- Restore and return the node index in s0. -/
theorem new_node_return (c : Config) (sp ra s0 s1 s2 s3 node oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ [(2, nativeStack sp 64), (8, node)])
    (saved : ∀ off value, (off, value) ∈ [(56, ra), (48, s0), (40, s1), (32, s2), (24, s3)] →
      bytesT c.σ.mem (nativeFrameBase sp 64 + off) 8 = value) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x800001b0#64 (fun e => e = c)
      (WriteRegistersPost [1, 10, 8, 9, 18, 19, 2] [] c ra node
        [(2, sp), (19, s3), (18, s2), (9, s1), (8, s0), (10, node), (1, ra)]) := by
  have savedRa := saved 56 ra (by simp)
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput new_nodeX01b0Seg 0x800001b0#64
        [(2, nativeStack sp 64), (8, node)] (newNodeReturnLoads sp c) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 8]; decide
      shape := by change ChainOK _ [2, 8] _; decide
      tick := leaf.tick
      facts := by
        have code := newNodeReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.new_node_at_"
        · exact (frame.read_slot (off := 56) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 48) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 56)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 56)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · simp only [new_nodeX01b0Seg, evalBlocks, evalBlock, SegEvalState.init, newnodereturn_line_800001b0, newnodereturn_line_800001b4, newnodereturn_line_800001b8, newnodereturn_line_800001bc, newnodereturn_line_800001c0, newnodereturn_line_800001c4, newnodereturn_line_800001c8, runGM, ldsRunM,
      wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, newNodeReturnLoads]
    rw [read8_value, read8_value, read8_value, read8_value, read8_value,
      show Functions.sign_extend (m := 64) 64#12 = 64#64 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, nativeStack_restore,
      saved 24 s3 (by simp), saved 32 s2 (by simp), saved 40 s1 (by simp), saved 48 s0 (by simp), savedRa]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
