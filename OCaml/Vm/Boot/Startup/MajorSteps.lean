import OCaml.Vm.Boot.Startup.MajorFrameNormalized
import OCaml.Vm.Boot.Startup.MajorFrameImage
import OCaml.Vm.Boot.Startup.MajorEntryNormalized
import OCaml.Vm.Boot.Startup.MajorEntryImage
import OCaml.Vm.Boot.Startup.MajorDivNormalized
import OCaml.Vm.Boot.Startup.MajorDivImage
import OCaml.Vm.Boot.Startup.MajorMulNormalized
import OCaml.Vm.Boot.Startup.MajorMulImage
import OCaml.Vm.Boot.Startup.MajorSizeNormalized
import OCaml.Vm.Boot.Startup.MajorSizeImage
import OCaml.Vm.Boot.Startup.MajorAllocCallNormalized
import OCaml.Vm.Boot.Startup.MajorAllocCallImage
import OCaml.Vm.Boot.Startup.MajorDivCallInterface
import OCaml.Vm.Boot.Startup.MajorMulCallInterface
import OCaml.Vm.Boot.Startup.MajorAllocCallCallInterface
import OCaml.Vm.Boot.Startup.MinorHeap
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_init_major_heap(size)'s blocks up to caml_alloc_for_heap, on the path
with `caml_major_heap_increment ≤ 1000` (a percentage) and a size at least
`Heap_chunk_min` and the increment. -/

/-- `caml_major_heap_increment`. -/
def majorIncrementAddr : Nat := 0x80064ad8

/-- Open a 48-byte frame. -/
theorem major_frame (c : Config) (sp ra v : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(2, sp), (10, v)]) :
    FnSummary 0x80009340#64 (fun e => e = c) (WriteRegistersPost [2] [] c 0x80009344#64 v
      [(2, nativeStack sp 48), (10, v)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX9340Seg 0x80009340#64 [(2, sp), (10, v)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := majorFrame_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_" }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

def majorSlots (ra s0 s1 s2 : BitVec 64) : List (Nat × BitVec 64) := [(16, s2), (32, s0), (40, ra), (24, s1)]

local macro "mek" : tactic => `(tactic| simp only [majorentry_line_80009344, majorentry_line_80009348, majorentry_line_8000934c, majorentry_line_80009350, majorentry_line_80009354, majorentry_line_80009358, majorentry_line_8000935c, majorentry_line_80009360, majorentry_line_80009364, majorentry_line_80009368, majorentry_line_8000936c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- Save s2, s0, ra, s1; `s2 = caml_major_heap_increment`, `s0 = &Caml_state`,
`s1 = Caml_state`; the increment is a percentage. -/
theorem major_entry (c : Config) (sp ra s0 s1 s2 size inc : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 48)
    (regs : GHolds c.σ [(18, s2), (2, nativeStack sp 48), (8, s0), (1, ra), (9, s1), (10, size)])
    (increment : bytesT c.σ.mem majorIncrementAddr 8 = inc) (percent : inc.toNat ≤ 1000)
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr) :
    FnSummary 0x80009344#64 (fun e => e = c) (WriteRegistersPost [18, 8, 13, 9, 15]
      (nativeWordLog sp 48 (majorSlots ra s0 s1 s2)) c 0x80009374#64 size
      [(18, inc), (8, BitVec.ofNat 64 Layout.sym_Caml_state), (13, 1000#64), (9, firstDomainPtr), (15, size),
        (2, nativeStack sp 48), (10, size)]) := by
  have inside : LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (nativeWordLog sp 48 (majorSlots ra s0 s1 s2)) :=
    frame.word_log_inside fun off value member => by simp [majorSlots] at member; omega
  have incWord : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 majorIncrementAddr).toNat) = inc := by
    rw [read8_value]; exact increment
  have state : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat) = firstDomainPtr := by
    rw [read8_value]; exact domain
  have sx16 : Functions.sign_extend (m := 64) 16#12 = BitVec.ofNat 64 16 := by decide
  have sx24 : Functions.sign_extend (m := 64) 24#12 = BitVec.ofNat 64 24 := by decide
  have sx32 : Functions.sign_extend (m := 64) 32#12 = BitVec.ofNat 64 32 := by decide
  have sx40 : Functions.sign_extend (m := 64) 40#12 = BitVec.ofNat 64 40 := by decide
  have hi16 := frame.slot_above (off := 16) (by decide)
  have hi24 := frame.slot_above (off := 24) (by decide)
  have hi32 := frame.slot_above (off := 32) (by decide)
  have hi40 := frame.slot_above (off := 40) (by decide)
  have hE : heapEnd = 0x86800000 := rfl
  rw [hE] at hi16 hi24 hi32 hi40
  have gI : (2147521352#64 + Functions.sign_extend (BitVec.extractLsb' 12 20 375063#32 +++ 0#12) +
      Functions.sign_extend 1936#12).toNat = 0x80064ad8 := by decide
  have gS : (2147521372#64 + Functions.sign_extend (BitVec.extractLsb' 12 20 377879#32 +++ 0#12) +
      Functions.sign_extend 2476#12 + Functions.sign_extend 0#12).toNat = 0x80064d08 := by decide
  apply registers_of_blocks' leaf.image (frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX9344FSeg 0x80009344#64
        [(18, s2), (2, nativeStack sp 48), (8, s0), (1, ra), (9, s1), (10, size)]
        [read8 c.σ.mem (BitVec.ofNat 64 majorIncrementAddr).toNat,
          read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [18, 2, 8, 1, 9, 10]; decide
      shape := by change ChainOK _ [18, 2, 8, 1, 9, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := majorEntry_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 48) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 48 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        all_goals mek
        · exact (slot 16 (by decide) (by decide)).sd rfl rfl
        · past_stores
          · exact (show ReadWindow (BitVec.ofNat 64 majorIncrementAddr) 8 by constructor <;> decide).ld rfl
              (by mek; decide) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, eaddrM, srcVal, lookupG, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, sx16, sx32, sx40, sx24, gI, gS, and_true]; (try simp only [majorIncrementAddr, Layout.sym_Caml_state]); omega)
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · past_stores
          · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 by constructor <;> decide).ld rfl
              (by mek; decide) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, eaddrM, srcVal, lookupG, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, sx16, sx32, sx40, sx24, gI, gS, and_true]; (try simp only [majorIncrementAddr, Layout.sym_Caml_state]); omega)
        · rw [incWord]
          change guardB bop.BLTU (0#64 + Functions.sign_extend (m := 64) 1000#12) inc = false
          unfold guardB Functions.zopz0zI_u
          simp only [Sail.BitVec.toNatInt, show Functions.sign_extend (m := 64) 1000#12 = 1000#64 by decide,
            BitVec.zero_add, decide_eq_false_iff_not, Int.ofNat_eq_natCast, Int.ofNat_lt]
          simp only [BitVec.toNat_ofNat]
          omega }))
  · simp only [caml_init_major_heapX9344FSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, List.headD_cons, List.tail_cons, majorentry_line_80009344, majorentry_line_80009348, majorentry_line_8000934c, majorentry_line_80009350, majorentry_line_80009354, majorentry_line_80009358, majorentry_line_8000935c, majorentry_line_80009360, majorentry_line_80009364, majorentry_line_80009368, majorentry_line_8000936c]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX9344FSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, imm20Of, majorentry_line_80009344, majorentry_line_80009348, majorentry_line_8000934c, majorentry_line_80009350, majorentry_line_80009354, majorentry_line_80009358, majorentry_line_8000935c, majorentry_line_80009360, majorentry_line_80009364, majorentry_line_80009368, majorentry_line_8000936c] at pins
    exact ⟨gholds_lookup_eq pins rfl incWord, gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl state, gholds_lookup_eq pins rfl (by rw [sext_zero, BitVec.add_zero]),
      gholds_lookup (n := 2) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

local macro "mdk" : tactic => `(tactic| simp only [majordiv_line_80009374, majordiv_line_80009378, majordiv_line_8000937c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- Save the size at `8(sp)`; `__divdi3(stat_heap_wsz, 100)`. -/
theorem major_div_front (c : Config) (sp ra size w : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 48)
    (regs : GHolds c.σ [(10, size), (2, nativeStack sp 48), (9, firstDomainPtr)])
    (wsz : bytesT c.σ.mem (domainField 336) 8 = w) :
    FnSummary 0x80009374#64 (fun e => e = c) (WriteRegistersPost [10, 11] (nativeWordLog sp 48 [(8, size)]) c
      jal_80009380_call.pc w [(10, w), (11, 100#64), (2, nativeStack sp 48), (9, firstDomainPtr)]) := by
  have inside : LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (nativeWordLog sp 48 [(8, size)]) :=
    frame.word_log_inside fun off value member => by simp at member; omega
  have word : bytesVal .ld (read8 c.σ.mem (firstDomainPtr + 336#64).toNat) = w := by rw [read8_value]; exact wsz
  have hi8 := frame.slot_above (off := 8) (by decide)
  have hE : heapEnd = 0x86800000 := rfl
  rw [hE] at hi8
  have f336 : (firstDomainPtr + Functions.sign_extend (m := 64) 336#12).toNat = 0x8007d150 + 336 := by decide
  have sx8 : Functions.sign_extend (m := 64) 8#12 = BitVec.ofNat 64 8 := by decide
  apply registers_of_blocks' leaf.image (frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX9374Seg 0x80009374#64
        [(10, size), (2, nativeStack sp 48), (9, firstDomainPtr)] [read8 c.σ.mem (firstDomainPtr + 336#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 2, 9]; decide
      shape := by change ChainOK _ [10, 2, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := majorDiv_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 48) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 48 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        all_goals mdk
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl
        · past_stores
          · exact (show ReadWindow (firstDomainPtr + 336#64) 8 by constructor <;> decide).ld rfl (by mdk; decide)
              (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, eaddrM, srcVal, lookupG, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, sx8, f336, and_true]; omega) }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX9374Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, majordiv_line_80009374, majordiv_line_80009378, majordiv_line_8000937c] at pins
    exact ⟨gholds_lookup_eq pins rfl word,
      gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 2) _ pins rfl, gholds_lookup (n := 9) _ pins rfl, trivial⟩
  · rfl
  · decide

theorem major_div_call (c : Config) (sp ra size w : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 48)
    (regs : GHolds c.σ [(10, size), (2, nativeStack sp 48), (9, firstDomainPtr)])
    (wsz : bytesT c.σ.mem (domainField 336) 8 = w) :
    FnSummary 0x80009374#64 (fun e => e = c) (WriteRegistersPost ([10, 11] ++ [1]) (nativeWordLog sp 48 [(8, size)]) c
      jal_80009380_call.target w ((1, jal_80009380_call.link) ::
        [(10, w), (11, 100#64), (2, nativeStack sp 48), (9, firstDomainPtr)])) :=
  block_then_call c jal_80009380_call_shape jal_80009380_call_decode (fun _ h => jal_80009380_call_pins h)
    (major_div_front c sp ra size w leaf frame regs wsz) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

/-- `__muldi3(increment, quotient)`. -/
theorem major_mul_front (c : Config) (ra q inc : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, q), (18, inc)]) :
    FnSummary 0x80009384#64 (fun e => e = c) (WriteRegistersPost [11, 10] [] c jal_8000938c_call.pc inc
      [(11, q), (10, inc), (18, inc)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX9384Seg 0x80009384#64 [(10, q), (18, inc)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 18]; decide
      shape := by change ChainOK _ [10, 18] _; decide
      tick := leaf.tick
      facts := by
        have code := majorMul_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_" }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX9384Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, majormul_line_80009384, majormul_line_80009388] at pins
    exact ⟨gholds_lookup_eq pins rfl (by rw [sext_zero, BitVec.add_zero]),
      gholds_lookup_eq pins rfl (by rw [sext_zero, BitVec.add_zero]), gholds_lookup (n := 18) _ pins rfl, trivial⟩
  · rfl
  · decide

theorem major_mul_call (c : Config) (ra q inc : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, q), (18, inc)]) :
    FnSummary 0x80009384#64 (fun e => e = c) (WriteRegistersPost ([11, 10] ++ [1]) [] c jal_8000938c_call.target inc
      ((1, jal_8000938c_call.link) :: [(11, q), (10, inc), (18, inc)])) :=
  block_then_call c jal_8000938c_call_shape jal_8000938c_call_decode (fun _ h => jal_8000938c_call_pins h)
    (major_mul_front c ra q inc leaf regs) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

/-- The heap size in words, stored as the domain's `stat_heap_wsz` and
`stat_top_heap_wsz`. -/
def majorSizeLog (w : BitVec 64) : List WEntry := [(domainField 336, 8, w), (domainField 344, 8, w)]

local macro "msz" : tactic => `(tactic| simp only [majorsize_line_80009390, majorsize_line_80009394, majorsize_line_80009398, majorsize_line_8000939c, majorsize_line_800093a4, majorsize_line_800093ac, majorsize_line_800093b0, majorsize_line_800093b4, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- The size in words is at least `Heap_chunk_min` and the increment. -/
theorem major_size (c : Config) (sp ra size p : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 48)
    (regs : GHolds c.σ [(2, nativeStack sp 48), (10, p), (9, firstDomainPtr)])
    (sizeSlot : bytesT c.σ.mem (nativeFrameBase sp 48 + 8) 8 = size)
    (chunkMin : 0xf000 ≤ (size >>> 3).toNat) (increment : p.toNat ≤ (size >>> 3).toNat) :
    FnSummary 0x80009390#64 (fun e => e = c) (WriteRegistersPost [15, 18, 13] (majorSizeLog (size >>> 3)) c
      0x800093b8#64 p [(15, size >>> 3), (18, p), (13, 0xf000#64), (2, nativeStack sp 48), (9, firstDomainPtr),
        (10, p)]) := by
  have word : bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 8)) = size := by rw [read8_value]; exact sizeSlot
  have lui : Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 0x0000f6b7#32 +++ 0#12) = 0xf000#64 := by decide
  apply registers_of_blocks' leaf.image (by
      constructor <;> simp only [majorSizeLog, OutLRange, domainField, show firstDomainPtr.toNat = 0x8007d150 from rfl,
        and_true] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput (caml_init_major_heapX9390TSeg ++ caml_init_major_heapX93a8TSeg ++
        caml_init_major_heapX93b0Seg) 0x80009390#64 [(2, nativeStack sp 48), (10, p), (9, firstDomainPtr)]
        [read8 c.σ.mem (nativeFrameBase sp 48 + 8)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10, 9]; decide
      shape := by change ChainOK _ [2, 10, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := majorSize_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_"
        all_goals msz
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · rw [word, srli_three _ _ rfl, lui]
          unfold guardB Functions.zopz0zKzJ_u
          simp only [Sail.BitVec.toNatInt]
          apply decide_eq_true
          apply Int.ofNat_le.mpr
          simp only [BitVec.toNat_ofNat]
          omega
        · rw [word, srli_three _ _ rfl, sext_zero, BitVec.add_zero]
          unfold guardB Functions.zopz0zKzJ_u
          simp only [Sail.BitVec.toNatInt]
          apply decide_eq_true
          apply Int.ofNat_le.mpr
          try simp only [BitVec.toNat_ofNat]
          omega
        · exact (show WriteWindow (BitVec.ofNat 64 (domainField 336)) 8 by constructor <;> decide).sd rfl (by msz; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 (domainField 344)) 8 by constructor <;> decide).sd rfl (by msz; decide) }))
  · simp only [caml_init_major_heapX9390TSeg, caml_init_major_heapX93a8TSeg, caml_init_major_heapX93b0Seg,
      List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, List.headD_cons, List.tail_cons, imm20Of, majorsize_line_80009390, majorsize_line_80009394, majorsize_line_80009398, majorsize_line_8000939c, majorsize_line_800093a4, majorsize_line_800093ac, majorsize_line_800093b0, majorsize_line_800093b4]
    rw [word, srli_three _ _ rfl, show (firstDomainPtr + Functions.sign_extend (m := 64) 336#12).toNat = domainField 336
      by decide, show (firstDomainPtr + Functions.sign_extend (m := 64) 344#12).toNat = domainField 344 by decide]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX9390TSeg, caml_init_major_heapX93a8TSeg, caml_init_major_heapX93b0Seg,
      List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, imm20Of, majorsize_line_80009390, majorsize_line_80009394, majorsize_line_80009398, majorsize_line_8000939c, majorsize_line_800093a4, majorsize_line_800093ac, majorsize_line_800093b0, majorsize_line_800093b4] at pins
    rw [word, srli_three _ _ rfl, lui, sext_zero] at pins
    simp only [BitVec.add_zero] at pins
    exact ⟨gholds_lookup (n := 15) _ pins rfl, gholds_lookup (n := 18) _ pins rfl, gholds_lookup (n := 13) _ pins rfl,
      gholds_lookup (n := 2) _ pins rfl, gholds_lookup (n := 9) _ pins rfl, gholds_lookup (n := 10) _ pins rfl,
      trivial⟩
  · rfl
  · decide

/-- `caml_alloc_for_heap(Bsize_wsize(w))`. -/
theorem major_alloc_front (c : Config) (ra w : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(15, w)]) :
    FnSummary 0x800093b8#64 (fun e => e = c) (WriteRegistersPost [10] [] c jal_800093bc_call.pc (w <<< 3)
      [(10, w <<< 3), (15, w)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_major_heapX93b8Seg 0x800093b8#64 [(15, w)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15]; decide
      shape := by change ChainOK _ [15] _; decide
      tick := leaf.tick
      facts := by
        have code := majorAllocCall_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_major_heap_at_" }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_major_heapX93b8Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, majoralloccall_line_800093b8] at pins
    exact ⟨gholds_lookup_eq pins rfl (slli_three _ _ rfl), gholds_lookup (n := 15) _ pins rfl, trivial⟩
  · rfl
  · decide

theorem major_alloc_call (c : Config) (ra w : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(15, w)]) :
    FnSummary 0x800093b8#64 (fun e => e = c) (WriteRegistersPost ([10] ++ [1]) [] c jal_800093bc_call.target (w <<< 3)
      ((1, jal_800093bc_call.link) :: [(10, w <<< 3), (15, w)])) :=
  block_then_call c jal_800093bc_call_shape jal_800093bc_call_decode (fun _ h => jal_800093bc_call_pins h)
    (major_alloc_front c ra w leaf regs) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl
end OCaml.Vm.Boot.Startup
