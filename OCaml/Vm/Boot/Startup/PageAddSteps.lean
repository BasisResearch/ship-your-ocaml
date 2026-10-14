import OCaml.Vm.Boot.Startup.PageAddFrameNormalized
import OCaml.Vm.Boot.Startup.PageAddFrameImage
import OCaml.Vm.Boot.Startup.PageAddEntryNormalized
import OCaml.Vm.Boot.Startup.PageAddEntryImage
import OCaml.Vm.Boot.Startup.PageAddLoopNormalized
import OCaml.Vm.Boot.Startup.PageAddLoopImage
import OCaml.Vm.Boot.Startup.PageAddLoopCallInterface
import OCaml.Vm.Boot.Startup.PageAddReturnNormalized
import OCaml.Vm.Boot.Startup.PageAddReturnImage
import OCaml.Vm.Boot.Startup.PageAddModel
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_page_table_add's blocks: page-align the range, then one
caml_page_table_modify per page. -/

local macro "pak0" : tactic => `(tactic| simp only [pageaddentry_line_8000b0f0, pageaddentry_line_8000b0f4, pageaddentry_line_8000b0f8, pageaddentry_line_8000b0fc, pageaddentry_line_8000b100, pageaddentry_line_8000b104, pageaddentry_line_8000b108, pageaddentry_line_8000b110, pageaddentry_line_8000b114, pageaddentry_line_8000b118, pageaddentry_line_8000b11c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])
local macro "pak" : tactic => `(tactic| simp only [pageaddentry_line_8000b0f0, pageaddentry_line_8000b0f4, pageaddentry_line_8000b0f8, pageaddentry_line_8000b0fc, pageaddentry_line_8000b100, pageaddentry_line_8000b104, pageaddentry_line_8000b108, pageaddentry_line_8000b110, pageaddentry_line_8000b114, pageaddentry_line_8000b118, pageaddentry_line_8000b11c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- The page mask, as `lui a5, 0xfffff` builds it. -/
theorem page_mask (i : MInstr) (w : i.word = 0xfffff7b7#32) :
    Functions.sign_extend (m := 64) (imm20Of i +++ 0#12) = 0xfffffffffffff000#64 := by
  rw [imm20Of, w]; decide

theorem page_size (i : MInstr) (w : i.word = 0x000019b7#32) :
    Functions.sign_extend (m := 64) (imm20Of i +++ 0#12) = 4096#64 := by
  rw [imm20Of, w]; decide

def pageAddSlots (ra s0 s1 s2 s3 : BitVec 64) : List (Nat × BitVec 64) :=
  [(24, s1), (32, s0), (40, ra), (16, s2), (8, s3)]

def pageAddLog (sp ra s0 s1 s2 s3 : BitVec 64) : List WEntry := nativeWordLog sp 48 (pageAddSlots ra s0 s1 s2 s3)

theorem pageAddLog_inside {sp ra s0 s1 s2 s3 : BitVec 64} (frame : NativeFrame sp 48) :
    LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (pageAddLog sp ra s0 s1 s2 s3) :=
  frame.word_log_inside fun off value member => by
    simp only [pageAddSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega

theorem gholds_lookup_eq {σ : MState} {L : GRegs} {n : Nat} {v w : BitVec 64} (h : GHolds σ L)
    (hl : lookupG n L = some v) (e : v = w) : gprGet σ n = some w := e ▸ gholds_lookup _ h hl

/-- `registers_of_blocks` with the register list implied rather than computed. -/
theorem registers_of_blocks' {bs entry before L loads writes pc value regs log}
    (image : ExecutableImage before) (outside : ImageOutside log)
    (S : FnSummary entry (fun c => c = before) (BlockPost bs entry L loads before))
    (hlog : (evalBlocks bs (SegEvalState.init L loads)).log = log)
    (hpc : evalBlocksPC entry (SegEvalState.init L loads) bs = pc)
    (hregs : ∀ σ, GHolds σ (evalBlocks bs (SegEvalState.init L loads)).regs → GHolds σ regs)
    (result : lookupG 10 regs = some value)
    (writesOk : ∀ n ∈ wrChain bs, n ∈ writes)
    (keys : KeysOK (wrChain bs) := by first | decide | exact of_decide_eq_true rfl)
    (no3 : 3 ∉ wrChain bs := by first | decide | exact of_decide_eq_true rfl) :
    FnSummary entry (fun c => c = before) (WriteRegistersPost writes log before pc value regs) := by
  apply S.weaken (fun _ h => h)
  intro after post
  have call := post.effect image outside hlog hpc (fun _ h => gholds_lookup _ (hregs _ h) result) writesOk keys no3
  exact ⟨call, hregs _ post.regs⟩

/-- Open caml_page_table_add's frame. -/
theorem page_add_frame (c : Config) (sp ra kind : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(2, sp), (10, kind)]) :
    FnSummary 0x8000b0ec#64 (fun e => e = c) (WriteRegistersPost [2] [] c 0x8000b0f0#64 kind
      [(2, nativeStack sp 48), (10, kind)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_page_table_addXb0ecSeg 0x8000b0ec#64 [(2, sp), (10, kind)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := pageAddFrame_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_page_table_add_at_" }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

def pageAddLogA (sp ra s0 s1 : BitVec 64) : List WEntry := nativeWordLog sp 48 [(24, s1), (32, s0), (40, ra)]
def pageAddLogB (sp s2 s3 : BitVec 64) : List WEntry := nativeWordLog sp 48 [(16, s2), (8, s3)]

/-- Save `s1`, `s0`, `ra`; page-align `[start, stop)` to pages `first .. last`. -/
theorem page_add_align (c : Config) (sp ra s0 s1 start stop first last v : BitVec 64)
    (leaf : LeafInput ra c) (frame : NativeFrame sp 48)
    (regs : GHolds c.σ [(2, nativeStack sp 48), (1, ra), (8, s0), (9, s1), (11, start), (12, stop), (10, v)])
    (hfirst : start &&& 0xfffffffffffff000#64 = first)
    (hlast : (stop + Functions.sign_extend (m := 64) 4095#12) &&& 0xfffffffffffff000#64 = last)
    (nonempty : guardB bop.BLTU last first = false) :
    FnSummary 0x8000b0f0#64 (fun e => e = c) (WriteRegistersPost [15, 9, 8] (pageAddLogA sp ra s0 s1) c
      0x8000b110#64 v [(8, first), (9, last), (15, 0xfffffffffffff000#64), (2, nativeStack sp 48), (10, v)]) := by
  have inside : LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (pageAddLogA sp ra s0 s1) :=
    frame.word_log_inside fun off value member => by simp at member; omega
  apply registers_of_blocks' leaf.image (frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_page_table_addXb0f0FSeg 0x8000b0f0#64
        [(2, nativeStack sp 48), (1, ra), (8, s0), (9, s1), (11, start), (12, stop), (10, v)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 8, 9, 11, 12, 10]; decide
      shape := by change ChainOK _ [2, 1, 8, 9, 11, 12, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := pageAddEntry_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 48) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 48 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_page_table_add_at_"
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · pak; rw [page_mask _ rfl, hfirst, hlast]; exact nonempty }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_page_table_addXb0f0FSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, pageaddentry_line_8000b0f0,
      pageaddentry_line_8000b0f4, pageaddentry_line_8000b0f8, pageaddentry_line_8000b0fc, pageaddentry_line_8000b100,
      pageaddentry_line_8000b104, pageaddentry_line_8000b108] at pins
    exact ⟨gholds_lookup_eq pins rfl (by rw [page_mask _ rfl, hfirst]),
      gholds_lookup_eq pins rfl (by rw [page_mask _ rfl, hlast]), gholds_lookup_eq pins rfl (page_mask _ rfl),
      gholds_lookup (n := 2) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- Save `s2`, `s3`; `s2 = kind`, `s3 = 4096`; into the loop. -/
theorem page_add_setup (c : Config) (sp ra s2 s3 kind : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 48)
    (regs : GHolds c.σ [(2, nativeStack sp 48), (18, s2), (19, s3), (10, kind)]) :
    FnSummary 0x8000b110#64 (fun e => e = c) (WriteRegistersPost [18, 19] (pageAddLogB sp s2 s3) c
      0x8000b128#64 kind [(19, 4096#64), (18, kind), (2, nativeStack sp 48), (10, kind)]) := by
  have inside : LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (pageAddLogB sp s2 s3) :=
    frame.word_log_inside fun off value member => by simp at member; omega
  apply registers_of_blocks' leaf.image (frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_page_table_addXb110Seg 0x8000b110#64
        [(2, nativeStack sp 48), (18, s2), (19, s3), (10, kind)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 18, 19, 10]; decide
      shape := by change ChainOK _ [2, 18, 19, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := pageAddEntry_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 48) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 48 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_page_table_add_at_"
        · exact (slot 16 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_page_table_addXb110Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, pageaddentry_line_8000b110,
      pageaddentry_line_8000b114, pageaddentry_line_8000b118, pageaddentry_line_8000b11c] at pins
    exact ⟨gholds_lookup_eq pins rfl (page_size _ rfl),
      gholds_lookup_eq pins rfl (by rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]),
      gholds_lookup (n := 2) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- `caml_page_table_modify(page, 0, kind)`. -/
theorem page_add_call_front (c : Config) (ra page kind : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, page), (18, kind)]) :
    FnSummary 0x8000b128#64 (fun e => e = c) (WriteRegistersPost [10, 12, 11] [] c jal_8000b134_call.pc page
      [(11, 0#64), (12, kind), (10, page), (8, page), (18, kind)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_page_table_addXb128Seg 0x8000b128#64 [(8, page), (18, kind)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 18]; decide
      shape := by change ChainOK _ [8, 18] _; decide
      tick := leaf.tick
      facts := by
        have code := pageAddLoop_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_page_table_add_at_" }))
  · rfl
  · rfl
  · simp only [caml_page_table_addXb128Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, pageaddloop_line_8000b128,
      pageaddloop_line_8000b12c, pageaddloop_line_8000b130]
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.add_zero, BitVec.add_zero]
  · rfl
  · decide

theorem page_add_call (c : Config) (ra page kind : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, page), (18, kind)]) :
    FnSummary 0x8000b128#64 (fun e => e = c) (WriteRegistersPost ([10, 12, 11] ++ [1]) [] c jal_8000b134_call.target page
      ((1, jal_8000b134_call.link) :: [(11, 0#64), (12, kind), (10, page), (8, page), (18, kind)])) :=
  block_then_call c jal_8000b134_call_shape jal_8000b134_call_decode (fun _ h => jal_8000b134_call_pins h)
    (page_add_call_front c ra page kind leaf regs) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

def pageAddNextBlocks (more : Bool) : List BBlock :=
  caml_page_table_addXb138TSeg ++ if more then caml_page_table_addXb124FSeg else caml_page_table_addXb124TSeg

/-- The page went in: next page; back while it is at most the last. -/
theorem page_add_next (c : Config) (ra page last : BitVec 64) (more : Bool) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, page), (19, 4096#64), (10, 0#64), (9, last)])
    (test : guardB bop.BLTU last (page + 4096#64) = !more) :
    FnSummary 0x8000b138#64 (fun e => e = c) (WriteRegistersPost [8] [] c
      (if more then 0x8000b128#64 else 0x8000b160#64) 0#64
      [(8, page + 4096#64), (19, 4096#64), (10, 0#64), (9, last)]) := by
  have input : BlockInput (pageAddNextBlocks more) 0x8000b138#64 [(8, page), (19, 4096#64), (10, 0#64), (9, last)]
      [] c := {
    good := leaf.good
    minstret := leaf.minstret
    regs := regs
    keys := by change KeysOK [8, 19, 10, 9]; decide
    shape := by unfold pageAddNextBlocks; cases more <;> (change ChainOK _ [8, 19, 10, 9] _; decide)
    tick := leaf.tick
    facts := by
      have code := pageAddLoop_code leaf.image
      have code2 := pageAddEntry_code leaf.image
      unfold pageAddNextBlocks
      cases more
      all_goals
        chain_facts code with "Vsa.Sim.Code.caml_page_table_add_at_"
        all_goals simp only [pageaddloop_line_8000b138, srcVal, lookupG, runGM, stepGM, eraseG, wvalM,
          Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff]
        all_goals first | decide | (rw [test]; rfl) }
  apply registers_of_blocks leaf.image (by constructor <;> trivial) (block_summary _ _ _ _ _ input)
    (keys := by unfold pageAddNextBlocks; cases more <;> decide) (no3 := by unfold pageAddNextBlocks; cases more <;> decide)
  · unfold pageAddNextBlocks; cases more <;> rfl
  · unfold pageAddNextBlocks; cases more <;> rfl
  · unfold pageAddNextBlocks; cases more <;> rfl
  · rfl
  · unfold pageAddNextBlocks; cases more <;> decide

/-- Restore and return 0. -/
theorem page_add_return (c : Config) (sp ra s0 s1 s2 s3 v oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ [(2, nativeStack sp 48), (10, v)])
    (saved : ∀ off value, (off, value) ∈ pageAddSlots ra s0 s1 s2 s3 →
      bytesT c.σ.mem (nativeFrameBase sp 48 + off) 8 = value)
    (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8000b160#64 (fun e => e = c) (WriteRegistersPost [18, 19, 1, 8, 9, 10, 2] [] c ra 0#64
      [(2, sp), (10, 0#64), (9, s1), (8, s0), (1, ra), (19, s3), (18, s2)]) := by
  have word (off : Nat) (value : BitVec 64) (member : (off, value) ∈ pageAddSlots ra s0 s1 s2 s3) :
      bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + off)) = value := by
    rw [read8_value]; exact saved off value member
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_page_table_addXb160Seg 0x8000b160#64
        [(2, nativeStack sp 48), (10, v)]
        [read8 c.σ.mem (nativeFrameBase sp 48 + 16), read8 c.σ.mem (nativeFrameBase sp 48 + 8),
          read8 c.σ.mem (nativeFrameBase sp 48 + 40), read8 c.σ.mem (nativeFrameBase sp 48 + 32),
          read8 c.σ.mem (nativeFrameBase sp 48 + 24)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := pageAddReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_page_table_add_at_"
        · exact (frame.read_slot (off := 16) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 40)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [word 40 ra (by simp [pageAddSlots]), ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 40)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [word 40 ra (by simp [pageAddSlots]), ret_tgt ra aligned]
  · simp only [caml_page_table_addXb160Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, pageaddreturn_line_8000b160, pageaddreturn_line_8000b164, pageaddreturn_line_8000b168, pageaddreturn_line_8000b16c, pageaddreturn_line_8000b170, pageaddreturn_line_8000b174, pageaddreturn_line_8000b178]
    rw [show Functions.sign_extend (m := 64) 48#12 = 48#64 by decide, nativeStack_restore,
      word 16 s2 (by simp [pageAddSlots]), word 8 s3 (by simp [pageAddSlots]),
      word 40 ra (by simp [pageAddSlots]), word 32 s0 (by simp [pageAddSlots]),
      word 24 s1 (by simp [pageAddSlots]), show 0#64 + Functions.sign_extend (m := 64) 0#12 = 0#64 by decide]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
