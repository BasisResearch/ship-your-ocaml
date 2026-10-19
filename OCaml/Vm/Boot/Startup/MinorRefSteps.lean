import OCaml.Vm.Boot.Startup.MinorHeapRefANormalized
import OCaml.Vm.Boot.Startup.MinorHeapRefAImage
import OCaml.Vm.Boot.Startup.MinorHeapSteps
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_set_minor_heap_size's reset of the domain's three ref tables
(`ref_table`, `ephe_ref_table`, `custom_table`), each still without storage. -/

/-- A ref-table record of 56 bytes in the arena. -/
structure RefTableSpot (t : BitVec 64) : Prop where
  low : heapStart ≤ t.toNat
  high : t.toNat + 56 ≤ heapEnd
  aligned : t.toNat % 8 = 0

theorem RefTableSpot.field_nat {t : BitVec 64} (spot : RefTableSpot t) (off : Nat) (bound : off ≤ 56) :
    (t + BitVec.ofNat 64 off).toNat = t.toNat + off := by
  have high := spot.high
  unfold heapEnd at high
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem RefTableSpot.window {t : BitVec 64} (spot : RefTableSpot t) (off : Nat) (bound : off + 8 ≤ 56)
    (aligned : off % 8 = 0) : WriteWindow (t + BitVec.ofNat 64 off) 8 := by
  have low := spot.low
  have high := spot.high
  have al := spot.aligned
  unfold heapStart at low
  unfold heapEnd at high
  constructor <;> (try simp only [spot.field_nat off (by omega), Layout.sym_tohost]) <;> omega

theorem RefTableSpot.read {t : BitVec 64} (spot : RefTableSpot t) : ReadWindow t 8 := by
  have low := spot.low
  have high := spot.high
  unfold heapStart at low
  unfold heapEnd at high
  constructor <;> (try simp only [Layout.sym_tohost]) <;> omega

local macro "rak" : tactic => `(tactic| simp only [minorheaprefa_line_8000a318, minorheaprefa_line_8000a31c, minorheaprefa_line_8000a320, minorheaprefa_line_8000a324, minorheaprefa_line_8000a328, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- `ref_table`: read its record, clear `size` and `reserve`; no storage to free. -/
theorem minor_ref_first (c : Config) (ra t v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(9, BitVec.ofNat 64 Layout.sym_Caml_state), (8, v)])
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr)
    (ptr : bytesT c.σ.mem (domainField 104) 8 = t) (spot : RefTableSpot t) (empty : bytesT c.σ.mem t.toNat 8 = 0#64) :
    FnSummary 0x8000a318#64 (fun e => e = c) (WriteRegistersPost [15, 8, 10]
      [((t + 40#64).toNat, 8, 0#64), ((t + 48#64).toNat, 8, 0#64)] c 0x8000a334#64 0#64
      [(15, firstDomainPtr), (8, t), (10, 0#64), (9, BitVec.ofNat 64 Layout.sym_Caml_state)]) := by
  have state : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat) = firstDomainPtr := by
    rw [read8_value]; exact domain
  have tbl : bytesVal .ld (read8 c.σ.mem (firstDomainPtr + 104#64).toNat) = t := by rw [read8_value]; exact ptr
  have base : bytesVal .ld (read8 c.σ.mem t.toNat) = 0#64 := by rw [read8_value]; exact empty
  have s104 : Functions.sign_extend (m := 64) 104#12 = 104#64 := by decide
  have s40 : Functions.sign_extend (m := 64) 40#12 = BitVec.ofNat 64 40 := by decide
  have s48 : Functions.sign_extend (m := 64) 48#12 = BitVec.ofNat 64 48 := by decide
  have outside : ImageOutside [((t + 40#64).toNat, 8, 0#64), ((t + 48#64).toNat, 8, 0#64)] := by
    have low := spot.low
    unfold heapStart at low
    constructor <;> simp only [OutLRange, spot.field_nat 40 (by decide), spot.field_nat 48 (by decide),
      and_true] <;> simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;> omega
  apply registers_of_blocks' leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput caml_set_minor_heap_sizeXa318TSeg 0x8000a318#64
        [(9, BitVec.ofNat 64 Layout.sym_Caml_state), (8, v)]
        [read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat, read8 c.σ.mem (firstDomainPtr + 104#64).toNat,
          read8 c.σ.mem t.toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [9, 8]; decide
      shape := by change ChainOK _ [9, 8] _; decide
      tick := leaf.tick
      facts := by
        have code := minorHeapRefA_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_set_minor_heap_size_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 by constructor <;> decide).ld rfl
            (by rak; rw [sext_zero, BitVec.add_zero]) (read8_pins _ _)
        · exact (show ReadWindow (firstDomainPtr + 104#64) 8 by constructor <;> decide).ld rfl
            (by rak; simp only [state, s104]) (read8_pins _ _)
        · exact spot.read.ld rfl (by rak; simp only [state, s104, tbl, sext_zero, BitVec.add_zero]) (read8_pins _ _)
        · exact (spot.window 40 (by decide) (by decide)).sd rfl (by rak; simp only [state, s104, tbl, s40])
        · exact (spot.window 48 (by decide) (by decide)).sd rfl (by rak; simp only [state, s104, tbl, s48])
        · rak
          simp only [state, s104, tbl, sext_zero, BitVec.add_zero, base]
          rfl }))
  · simp only [caml_set_minor_heap_sizeXa318TSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff,
      ite_true, ite_false, List.headD_cons, List.tail_cons, minorheaprefa_line_8000a318, minorheaprefa_line_8000a31c, minorheaprefa_line_8000a320, minorheaprefa_line_8000a324, minorheaprefa_line_8000a328]
    simp only [state, s104, tbl, s40, s48]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_set_minor_heap_sizeXa318TSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, minorheaprefa_line_8000a318, minorheaprefa_line_8000a31c, minorheaprefa_line_8000a320, minorheaprefa_line_8000a324, minorheaprefa_line_8000a328] at pins
    exact ⟨gholds_lookup_eq pins rfl state, gholds_lookup_eq pins rfl (by simp only [state, s104, tbl]),
      gholds_lookup_eq pins rfl (by simp only [state, s104, tbl, sext_zero, BitVec.add_zero, base]),
      gholds_lookup (n := 9) _ pins rfl, trivial⟩
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
