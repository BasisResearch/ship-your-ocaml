import OCaml.Vm.Boot.Startup.PageTableEntryNormalized
import OCaml.Vm.Boot.Startup.PageTableEntryImage
import OCaml.Vm.Boot.Startup.PageTableTopNormalized
import OCaml.Vm.Boot.Startup.PageTableTopImage
import OCaml.Vm.Boot.Startup.PageTableShiftNormalized
import OCaml.Vm.Boot.Startup.PageTableShiftImage
import OCaml.Vm.Boot.Startup.NativeSave
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
end OCaml.Vm.Boot.Startup
