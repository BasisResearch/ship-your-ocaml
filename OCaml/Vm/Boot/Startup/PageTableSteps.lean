import OCaml.Vm.Boot.Startup.PageTableEntryNormalized
import OCaml.Vm.Boot.Startup.PageTableEntryImage
import OCaml.Vm.Boot.Startup.PageTableTopNormalized
import OCaml.Vm.Boot.Startup.PageTableTopImage
import OCaml.Vm.Boot.Startup.PageTableShiftNormalized
import OCaml.Vm.Boot.Startup.PageTableShiftImage
import OCaml.Vm.Boot.Startup.PageTableLoopNormalized
import OCaml.Vm.Boot.Startup.PageTableLoopImage
import OCaml.Vm.Boot.Startup.PageTableSizeNormalized
import OCaml.Vm.Boot.Startup.PageTableSizeImage
import OCaml.Vm.Boot.Startup.NativeSave
import Vsa.Sim.IndexedLoop
import OCaml.Vm.Boot.Startup.RuntimeStack
import OCaml.Vm.Boot.Startup.ReadSectionsSteps
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_page_table_initialize(0x2f8000): 2048 entries, shift 53, mask 2047,
and a cleared 16 KB table. One summary per `auipc`, so the kernel never
reduces two global addresses in one block. -/

local macro "ptk" : tactic => `(tactic| simp only [pagetabletop_line_8000acf4, pagetabletop_line_8000acf8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])
local macro "psk" : tactic => `(tactic| simp only [pagetableshift_line_8000acfc, pagetableshift_line_8000ad00, pagetableshift_line_8000ad08, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])
local macro "evk" : tactic => `(tactic| simp only [evalBlocks, evalBlock, SegEvalState.init, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, pagetableentry_line_8000acdc, pagetableentry_line_8000ace0, pagetableentry_line_8000ace4, pagetableentry_line_8000ace8, pagetableentry_line_8000acec, pagetableentry_line_8000acf0, pagetabletop_line_8000acf4, pagetabletop_line_8000acf8, pagetableshift_line_8000acfc, pagetableshift_line_8000ad00, pagetableshift_line_8000ad08])

/-- The `caml_page_table` fields. -/
abbrev pageTable : Nat := Layout.sym_caml_page_table

theorem page_table_addr0 : 2147527924#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 382743#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 1988#12 = BitVec.ofNat 64 pageTable := by decide

theorem page_table_addr1 : 2147527932#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 382743#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 1988#12 = BitVec.ofNat 64 (pageTable + 8) := by decide

theorem page_table_upper (i : MInstr) (w : i.word = 382743#32) :
    Functions.sign_extend (m := 64) (imm20Of i +++ 0#12) = 0x5d000#64 := by
  rw [imm20Of, w]; decide

/-- `(0x2f8000 >> 12) << 1`: 1520 pages. -/
def PagesOf (n pages : BitVec 64) : Prop :=
  ∀ i j : MInstr, i.imm = 12#12 → j.imm = 1#12 →
    Sail.shift_bits_left (Sail.shift_bits_right n (Sail.BitVec.extractLsb (shamtOf i) 5 0))
      (Sail.BitVec.extractLsb (shamtOf j) 5 0) = pages

theorem page_table_pages : PagesOf 0x2f8000#64 1520#64 := by
  intro i j hi hj
  rw [shamtOf, shamtOf, hi, hj]; decide

def pageTableSaveLog (sp ra : BitVec 64) : List WEntry := nativeWordLog sp 32 [(24, ra)]

/-- Entry: open the frame, save `ra`, `pages = (bytesize >> 12) * 2`. -/
theorem page_table_save (c : Config) (sp ra : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 32)
    (n pages : BitVec 64) (regs : GHolds c.σ [(2, sp), (1, ra), (10, n)]) (count : PagesOf n pages) :
    FnSummary 0x8000acdc#64 (fun e => e = c) (WriteRegistersPost [10, 15, 12, 2] (pageTableSaveLog sp ra) c
      0x8000acf4#64 pages [(10, pages), (15, 64#64), (12, 1#64), (2, nativeStack sp 32), (1, ra)]) := by
  have inside : LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (pageTableSaveLog sp ra) :=
    frame.word_log_inside fun off value member => by simp at member; omega
  apply registers_of_blocks leaf.image (frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_page_table_initializeXacdcSeg 0x8000acdc#64
        [(2, sp), (1, ra), (10, n)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 10]; decide
      shape := by change ChainOK _ [2, 1, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := pageTableEntry_code leaf.image
        have slot : WriteWindow (nativeStack sp 32 + BitVec.ofNat 64 24) 8 := by
          rw [nativeStack, frame.address _ (by decide)]
          exact frame.word (by decide) (by decide)
        chain_facts code with "Vsa.Sim.Code.caml_page_table_initialize_at_"
        exact slot.sd rfl rfl }))
  · rfl
  · rfl
  · change [(10, Sail.shift_bits_left (Sail.shift_bits_right n (Sail.BitVec.extractLsb (shamtOf (mkLine 0x8000ace0#64 0x00c55513#32)) 5 0))
        (Sail.BitVec.extractLsb (shamtOf (mkLine 0x8000acf0#64 0x00151513#32)) 5 0)), _, _, _, _] = _
    rw [count _ _ rfl rfl]
    rfl
  · rfl
  · decide

theorem pageTable_outside {n : Nat} {v : BitVec 64} (off : Nat) (_hoff : off + n ≤ 0x28) :
    ImageOutside [(pageTable + off, n, v)] := by
  have text : Image.textBase + Image.textSize ≤ pageTable := by decide
  have rodata : Image.rodataBase + Image.rodataSize ≤ pageTable := by decide
  constructor <;> simp only [OutLRange, and_true] <;> omega

/-- `caml_page_table.size = 1`. -/
theorem page_table_top (c : Config) (ra v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(12, 1#64), (10, v)]) :
    FnSummary 0x8000acf4#64 (fun e => e = c) (WriteRegistersPost [14] [(pageTable + 0, 8, 1#64)] c
      0x8000acfc#64 v [(14, 2147527924#64 + 0x5d000#64), (12, 1#64), (10, v)]) := by
  apply registers_of_blocks leaf.image (pageTable_outside 0 (by decide))
    (block_summary _ _ _ _ _ (show BlockInput caml_page_table_initializeXacf4Seg 0x8000acf4#64
        [(12, 1#64), (10, v)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [12, 10]; decide
      shape := by change ChainOK _ [12, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := pageTableTop_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_page_table_initialize_at_"
        exact (show WriteWindow (BitVec.ofNat 64 pageTable) 8 by constructor <;> decide).sd rfl
          (by ptk; exact page_table_addr0) }))
  · simp only [caml_page_table_initializeXacf4Seg]; evk
    rw [page_table_upper _ rfl, show (2147527924#64 + 0x5d000#64 + Functions.sign_extend (m := 64) 1988#12).toNat =
      pageTable + 0 by decide]
    rfl
  · rfl
  · simp only [caml_page_table_initializeXacf4Seg]; evk
    rw [page_table_upper _ rfl]
  · rfl
  · decide

/-- `caml_page_table.shift = 64`; `size = 1 < pages`, so into the doubling loop. -/
theorem page_table_shift (c : Config) (ra pages : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, 64#64), (12, 1#64), (10, pages)]) (more : guardB bop.BGEU 1#64 pages = false) :
    FnSummary 0x8000acfc#64 (fun e => e = c) (WriteRegistersPost [14, 15] [(pageTable + 8, 4, 64#64)] c
      0x8000ad0c#64 pages [(15, 63#64), (14, 2147527932#64 + 0x5d000#64), (12, 1#64), (10, pages)]) := by
  apply registers_of_blocks leaf.image (pageTable_outside 8 (by decide))
    (block_summary _ _ _ _ _ (show BlockInput (caml_page_table_initializeXacfcFSeg ++
        caml_page_table_initializeXad08Seg) 0x8000acfc#64 [(15, 64#64), (12, 1#64), (10, pages)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 12, 10]; decide
      shape := by change ChainOK _ [15, 12, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := pageTableShift_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_page_table_initialize_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 (pageTable + 8)) 4 by constructor <;> decide).sw rfl
            (by psk; exact page_table_addr1)
        · exact more }))
  · simp only [caml_page_table_initializeXacfcFSeg, caml_page_table_initializeXad08Seg, List.cons_append,
      List.nil_append]; evk
    rw [page_table_upper _ rfl, show (2147527932#64 + 0x5d000#64 + Functions.sign_extend (m := 64) 1988#12).toNat =
      pageTable + 8 by decide]
    rfl
  · rfl
  · simp only [caml_page_table_initializeXacfcFSeg, caml_page_table_initializeXad08Seg, List.cons_append,
      List.nil_append]; evk
    rw [page_table_upper _ rfl, show 0#64 + Functions.sign_extend (m := 64) 63#12 = 63#64 by decide]
  · rfl
  · decide

local macro "plk" : tactic => `(tactic| simp only [pagetableloop_line_8000ad0c, pagetableloop_line_8000ad10, pagetableloop_line_8000ad14, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

theorem page_table_double (i : MInstr) (hi : i.imm = 1#12) (k : Nat) (hk : k < 11) :
    Sail.shift_bits_left (BitVec.ofNat 64 (2 ^ k)) (Sail.BitVec.extractLsb (shamtOf i) 5 0) =
      BitVec.ofNat 64 (2 ^ (k + 1)) := by
  rw [shamtOf, hi]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem page_table_count (k : Nat) (hk : k < 11) :
    Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb
      (BitVec.ofNat 64 (63 - k) + Functions.sign_extend (m := 64) 4095#12) 31 0) = BitVec.ofNat 64 (62 - k) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem page_table_more (k : Nat) (hk : k < 11) :
    guardB bop.BLTU (BitVec.ofNat 64 (2 ^ (k + 1))) 1520#64 = decide (k + 1 < 11) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def pageTableLoopBlocks (k : Nat) : List BBlock :=
  if k + 1 < 11 then caml_page_table_initializeXad0cTSeg else caml_page_table_initializeXad0cFSeg

/-- One doubling step: `size <<= 1`, `shift--`, back while `size < pages`. -/
theorem page_table_doubling (c : Config) (ra : BitVec 64) (k : Nat) (hk : k < 11) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(12, BitVec.ofNat 64 (2 ^ k)), (15, BitVec.ofNat 64 (63 - k)), (10, 1520#64)]) :
    FnSummary 0x8000ad0c#64 (fun e => e = c) (WriteRegistersPost [12, 14, 15] [] c
      (if k + 1 < 11 then 0x8000ad0c#64 else 0x8000ad1c#64) 1520#64
      [(15, BitVec.ofNat 64 (62 - k)), (14, BitVec.ofNat 64 (63 - k)), (12, BitVec.ofNat 64 (2 ^ (k + 1))),
        (10, 1520#64)]) := by
  have input : BlockInput (pageTableLoopBlocks k) 0x8000ad0c#64
      [(12, BitVec.ofNat 64 (2 ^ k)), (15, BitVec.ofNat 64 (63 - k)), (10, 1520#64)] [] c := {
    good := leaf.good
    minstret := leaf.minstret
    regs := regs
    keys := by change KeysOK [12, 15, 10]; decide
    shape := by unfold pageTableLoopBlocks; split <;> (change ChainOK _ [12, 15, 10] _; decide)
    tick := leaf.tick
    facts := by
      have code := pageTableLoop_code leaf.image
      have more := page_table_more k hk
      unfold pageTableLoopBlocks
      split
      · chain_facts code with "Vsa.Sim.Code.caml_page_table_initialize_at_"
        plk; rw [page_table_double _ rfl k hk, more]; simp [*]
      · chain_facts code with "Vsa.Sim.Code.caml_page_table_initialize_at_"
        plk; rw [page_table_double _ rfl k hk, more]; simp [*] }
  apply registers_of_blocks leaf.image (by constructor <;> trivial) (block_summary _ _ _ _ _ input)
    (keys := by unfold pageTableLoopBlocks; split <;> decide)
    (no3 := by unfold pageTableLoopBlocks; split <;> decide)
  · unfold pageTableLoopBlocks; split <;> rfl
  · unfold pageTableLoopBlocks; split <;> rfl
  · unfold pageTableLoopBlocks
    split
    all_goals
      simp only [caml_page_table_initializeXad0cTSeg, caml_page_table_initializeXad0cFSeg, evalBlocks, evalBlock,
        SegEvalState.init, runGM, stepGM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff,
        ite_true, ite_false, pagetableloop_line_8000ad0c, pagetableloop_line_8000ad10, pagetableloop_line_8000ad14]
      rw [page_table_double _ rfl k hk, page_table_count k hk,
        show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]
  · rfl
  · unfold pageTableLoopBlocks; split <;> decide

/-- The doubling loop after `k` steps: `size = 2^k`, `shift` register `63 - k`. -/
structure DoublingAt (H : List (Nat × Nat)) (capacity : Nat) (sp ra : BitVec 64) (start : Config) (k : Nat)
    (d : Config) : Prop where
  pc : PCAt (if k < 11 then 0x8000ad0c#64 else 0x8000ad1c#64) d
  regs : GHolds d.σ [(12, BitVec.ofNat 64 (2 ^ k)), (15, BitVec.ofNat 64 (63 - k)), (10, 1520#64)]
  shift : 0 < k → gprGet d.σ 14 = some (BitVec.ofNat 64 (64 - k))
  ready : RuntimeReady H capacity sp ra d
  bound : k ≤ 11
  mem : d.σ.mem = start.σ.mem

theorem DoublingAt.index {H capacity sp ra start k d} (D : DoublingAt H capacity sp ra start k d) :
    63 - ((gprGet d.σ 15).getD 0).toNat = k := by
  rw [gholds_lookup (n := 15) _ D.regs rfl]
  have := D.bound
  simp only [Option.getD_some, BitVec.toNat_ofNat]
  omega

theorem page_table_doubling_loop {H capacity sp ra start} (frame : NativeFrame sp 32)
    (D : DoublingAt H capacity sp ra start 0 start) :
    ∃ d, Steps start d ∧ DoublingAt H capacity sp ra start 11 d := by
  have loop := indexedLoop (I := DoublingAt H capacity sp ra start)
    (index := fun d => 63 - ((gprGet d.σ 15).getD 0).toNat) (start := 0) (count := 11)
    (fun _ _ h => h.index) (fun _ _ h => h.bound) (fun k d ⟨h, lt⟩ => by
      have pc : PCAt 0x8000ad0c#64 d := by have := h.pc; simp only [lt, ite_true] at this; exact this
      obtain ⟨e, run, p⟩ := (page_table_doubling d ra k lt h.ready.toLeafInput h.regs).run d ⟨pc, rfl⟩
      exact ⟨e, run, {
        pc := p.pc
        regs := ⟨gholds_lookup (n := 12) _ p.regs rfl, by rw [gholds_lookup (n := 15) _ p.regs rfl]; congr 2; omega,
          gholds_lookup (n := 10) _ p.regs rfl, trivial⟩
        shift := fun _ => by rw [gholds_lookup (n := 14) _ p.regs rfl]; congr 2; omega
        ready := h.ready.stack_log p (by decide) (by simp only [keysG]; decide) (by decide)
          ((p.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans h.ready.stack)
          ((p.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans h.ready.raReg)
          h.ready.aligned frame (by simp only [LogInW])
        bound := by omega
        mem := p.memory.trans h.mem }⟩)
  exact loop start D

local macro "pzk" : tactic => `(tactic| simp only [pagetablesize_line_8000ad1c, pagetablesize_line_8000ad20, pagetablesize_line_8000ad24, pagetablesize_line_8000ad28, pagetablesize_line_8000ad2c, pagetablesize_line_8000ad30, pagetablesize_line_8000ad34, pagetablesize_line_8000ad38, pagetablesize_line_8000ad3c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

def pageTableFieldsLog : List WEntry :=
  [(pageTable + 8, 4, 53#64), (pageTable + 0, 8, 2048#64), (pageTable + 0x18, 8, 0#64), (pageTable + 0x10, 8, 2047#64)]

theorem pageTableFieldsLog_outside : ImageOutside pageTableFieldsLog := by
  have text : Image.textBase + Image.textSize ≤ pageTable := by decide
  have rodata : Image.rodataBase + Image.rodataSize ≤ pageTable := by decide
  constructor <;> simp only [pageTableFieldsLog, OutLRange, and_true] <;> omega

/-- The final geometry: `shift = 53`, `size = 2048`, `occupancy = 0`, `mask = 2047`. -/
theorem page_table_fields (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(12, 2048#64), (14, 53#64), (10, 1520#64)]) :
    FnSummary 0x8000ad1c#64 (fun e => e = c) (WriteRegistersPost [15, 13, 14] pageTableFieldsLog c
      0x8000ad40#64 1520#64 [(14, 0x80067d38#64), (13, 0x80067d28#64), (15, 2047#64), (12, 2048#64),
        (10, 1520#64)]) := by
  apply registers_of_blocks leaf.image pageTableFieldsLog_outside
    (block_summary _ _ _ _ _ (show BlockInput caml_page_table_initializeXad1cSeg 0x8000ad1c#64
        [(12, 2048#64), (14, 53#64), (10, 1520#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [12, 14, 10]; decide
      shape := by change ChainOK _ [12, 14, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := pageTableSize_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_page_table_initialize_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 (pageTable + 8)) 4 by constructor <;> decide).sw rfl
            (by pzk; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 (pageTable + 0)) 8 by constructor <;> decide).sd rfl
            (by pzk; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 (pageTable + 0x18)) 8 by constructor <;> decide).sd rfl
            (by pzk; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 (pageTable + 0x10)) 8 by constructor <;> decide).sd rfl
            (by pzk; decide) }))
  · decide
  · rfl
  · decide
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
