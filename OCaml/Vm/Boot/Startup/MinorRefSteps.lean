import OCaml.Vm.Boot.Startup.MinorHeapRefANormalized
import OCaml.Vm.Boot.Startup.MinorHeapRefAImage
import OCaml.Vm.Boot.Startup.MinorHeapRefBNormalized
import OCaml.Vm.Boot.Startup.MinorHeapRefBImage
import OCaml.Vm.Boot.Startup.MinorHeapRefCNormalized
import OCaml.Vm.Boot.Startup.MinorHeapRefCImage
import OCaml.Vm.Boot.Startup.MinorHeapRefDNormalized
import OCaml.Vm.Boot.Startup.MinorHeapRefDImage
import OCaml.Vm.Boot.Startup.MinorHeapReturnNormalized
import OCaml.Vm.Boot.Startup.MinorHeapReturnImage
import OCaml.Vm.Boot.Startup.MinorHeapSteps
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_set_minor_heap_size's reset of the domain's three ref tables
(`ref_table`, `ephe_ref_table`, `custom_table`), each still without storage. -/

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

/-- Clearing a table's `size` and `reserve`. -/
def tableClearLog (t : BitVec 64) : List WEntry := [((t + 40#64).toNat, 8, 0#64), ((t + 48#64).toNat, 8, 0#64)]

/-- Clearing a table's `base`, `end`, `limit`, `threshold` and `ptr`. -/
def tableResetLog (t : BitVec 64) : List WEntry :=
  [(t.toNat, 8, 0#64), ((t + 8#64).toNat, 8, 0#64), ((t + 32#64).toNat, 8, 0#64), ((t + 16#64).toNat, 8, 0#64),
    ((t + 24#64).toNat, 8, 0#64)]

local macro "rbk" : tactic => `(tactic| simp only [minorheaprefb_line_8000a334, minorheaprefb_line_8000a338, minorheaprefb_line_8000a33c, minorheaprefb_line_8000a340, minorheaprefb_line_8000a344, minorheaprefb_line_8000a348, minorheaprefb_line_8000a34c, minorheaprefb_line_8000a350, minorheaprefb_line_8000a354, minorheaprefb_line_8000a358, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- Through the stores before a load: each store becomes a write-log entry the
load must miss. -/
macro "past_stores" : tactic => `(tactic| (
  repeat (first | rw [stepMemM_store rfl] | rw [stepMemM_skip rfl])
  repeat (refine memFacts_writeLog ?_ ?_)))

/-- `ref_table`'s remaining fields; `ephe_ref_table`: read its record, clear
`size` and `reserve`; no storage to free. -/
theorem minor_ref_second (c : Config) (ra t1 t2 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, t1), (9, BitVec.ofNat 64 Layout.sym_Caml_state)])
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr)
    (ptr : bytesT c.σ.mem (domainField 112) 8 = t2) (spot1 : RefTableSpot t1) (spot2 : RefTableSpot t2)
    (empty : bytesT c.σ.mem t2.toNat 8 = 0#64)
    (apart : t1.toNat + 56 ≤ t2.toNat ∨ t2.toNat + 56 ≤ t1.toNat)
    (offDomain : t1.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t1.toNat) :
    FnSummary 0x8000a334#64 (fun e => e = c) (WriteRegistersPost [14, 8, 10] (tableResetLog t1 ++ tableClearLog t2)
      c 0x8000a364#64 0#64
      [(14, firstDomainPtr), (8, t2), (10, 0#64), (9, BitVec.ofNat 64 Layout.sym_Caml_state)]) := by
  have state : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat) = firstDomainPtr := by
    rw [read8_value]; exact domain
  have tbl : bytesVal .ld (read8 c.σ.mem (firstDomainPtr + 112#64).toNat) = t2 := by rw [read8_value]; exact ptr
  have base : bytesVal .ld (read8 c.σ.mem t2.toNat) = 0#64 := by rw [read8_value]; exact empty
  have s112 : Functions.sign_extend (m := 64) 112#12 = 112#64 := by decide
  have s8 : Functions.sign_extend (m := 64) 8#12 = BitVec.ofNat 64 8 := by decide
  have s16 : Functions.sign_extend (m := 64) 16#12 = BitVec.ofNat 64 16 := by decide
  have s24 : Functions.sign_extend (m := 64) 24#12 = BitVec.ofNat 64 24 := by decide
  have s32 : Functions.sign_extend (m := 64) 32#12 = BitVec.ofNat 64 32 := by decide
  have s40 : Functions.sign_extend (m := 64) 40#12 = BitVec.ofNat 64 40 := by decide
  have s48 : Functions.sign_extend (m := 64) 48#12 = BitVec.ofNat 64 48 := by decide
  have f1 (off : Nat) (h : off ≤ 56) := spot1.field_nat off h
  have f2 (off : Nat) (h : off ≤ 56) := spot2.field_nat off h
  have low1 := spot1.low
  have low2 := spot2.low
  have high1 := spot1.high
  have domNat : firstDomainPtr.toNat = 0x8007d150 := rfl
  have stateNat : (BitVec.ofNat 64 Layout.sym_Caml_state).toNat = 0x80064d08 := rfl
  have field112 : (firstDomainPtr + 112#64).toNat = 0x8007d150 + 112 := rfl
  unfold heapStart at low1 low2
  unfold heapEnd at high1
  have outside : ImageOutside (tableResetLog t1 ++ tableClearLog t2) := by
    constructor <;> simp only [tableResetLog, tableClearLog, List.cons_append, List.nil_append, OutLRange,
      f1 8 (by decide), f1 16 (by decide), f1 24 (by decide), f1 32 (by decide), f2 40 (by decide),
      f2 48 (by decide), and_true] <;>
      simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;> omega
  apply registers_of_blocks' leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput caml_set_minor_heap_sizeXa334TSeg 0x8000a334#64
        [(8, t1), (9, BitVec.ofNat 64 Layout.sym_Caml_state)]
        [read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat, read8 c.σ.mem (firstDomainPtr + 112#64).toNat,
          read8 c.σ.mem t2.toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 9]; decide
      shape := by change ChainOK _ [8, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := minorHeapRefB_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_set_minor_heap_size_at_"
        all_goals rbk
        · exact (spot1.window 0 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · past_stores
          · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 by constructor <;> decide).ld rfl
              (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff]) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff, f1 8 (by decide), f1 16 (by decide),
            f1 24 (by decide), f1 32 (by decide), and_true]; (try simp only [stateNat, field112, domNat]); omega)
        · exact (spot1.window 8 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · exact (spot1.window 32 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · exact (spot1.window 16 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · exact (spot1.window 24 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · past_stores
          · exact (show ReadWindow (firstDomainPtr + 112#64) 8 by constructor <;> decide).ld rfl
              (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff]) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff, f1 8 (by decide), f1 16 (by decide),
            f1 24 (by decide), f1 32 (by decide), and_true]; (try simp only [stateNat, field112, domNat]); omega)
        · past_stores
          · exact spot2.read.ld rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff]) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff, f1 8 (by decide), f1 16 (by decide),
            f1 24 (by decide), f1 32 (by decide), and_true]; (try simp only [stateNat, field112, domNat]); omega)
        · exact (spot2.window 40 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · exact (spot2.window 48 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s112, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · simp only [state, s112, tbl, sext_zero, BitVec.add_zero, base]
          rfl }))
  · simp only [caml_set_minor_heap_sizeXa334TSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff,
      ite_true, ite_false, List.headD_cons, List.tail_cons, minorheaprefb_line_8000a334, minorheaprefb_line_8000a338, minorheaprefb_line_8000a33c, minorheaprefb_line_8000a340, minorheaprefb_line_8000a344, minorheaprefb_line_8000a348, minorheaprefb_line_8000a34c, minorheaprefb_line_8000a350, minorheaprefb_line_8000a354, minorheaprefb_line_8000a358]
    simp only [state, s112, tbl, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_set_minor_heap_sizeXa334TSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, minorheaprefb_line_8000a334, minorheaprefb_line_8000a338, minorheaprefb_line_8000a33c, minorheaprefb_line_8000a340, minorheaprefb_line_8000a344, minorheaprefb_line_8000a348, minorheaprefb_line_8000a34c, minorheaprefb_line_8000a350, minorheaprefb_line_8000a354, minorheaprefb_line_8000a358] at pins
    exact ⟨gholds_lookup_eq pins rfl state, gholds_lookup_eq pins rfl (by simp only [state, s112, tbl]),
      gholds_lookup_eq pins rfl (by simp only [state, s112, tbl, sext_zero, BitVec.add_zero, base]),
      gholds_lookup (n := 9) _ pins rfl, trivial⟩
  · rfl
  · decide
local macro "rck" : tactic => `(tactic| simp only [minorheaprefc_line_8000a364, minorheaprefc_line_8000a368, minorheaprefc_line_8000a36c, minorheaprefc_line_8000a370, minorheaprefc_line_8000a374, minorheaprefc_line_8000a378, minorheaprefc_line_8000a37c, minorheaprefc_line_8000a380, minorheaprefc_line_8000a384, minorheaprefc_line_8000a388, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- `ephe_ref_table`'s remaining fields; `custom_table`: read its record,
clear `size` and `reserve`; no storage to free. -/
theorem minor_ref_third (c : Config) (ra t2 t3 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, t2), (9, BitVec.ofNat 64 Layout.sym_Caml_state)])
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr)
    (ptr : bytesT c.σ.mem (domainField 120) 8 = t3) (spot2 : RefTableSpot t2) (spot3 : RefTableSpot t3)
    (empty : bytesT c.σ.mem t3.toNat 8 = 0#64)
    (apart : t2.toNat + 56 ≤ t3.toNat ∨ t3.toNat + 56 ≤ t2.toNat)
    (offDomain : t2.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t2.toNat) :
    FnSummary 0x8000a364#64 (fun e => e = c) (WriteRegistersPost [14, 8, 10] (tableResetLog t2 ++ tableClearLog t3)
      c 0x8000a394#64 0#64
      [(14, firstDomainPtr), (8, t3), (10, 0#64), (9, BitVec.ofNat 64 Layout.sym_Caml_state)]) := by
  have state : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat) = firstDomainPtr := by
    rw [read8_value]; exact domain
  have tbl : bytesVal .ld (read8 c.σ.mem (firstDomainPtr + 120#64).toNat) = t3 := by rw [read8_value]; exact ptr
  have base : bytesVal .ld (read8 c.σ.mem t3.toNat) = 0#64 := by rw [read8_value]; exact empty
  have s120 : Functions.sign_extend (m := 64) 120#12 = 120#64 := by decide
  have s8 : Functions.sign_extend (m := 64) 8#12 = BitVec.ofNat 64 8 := by decide
  have s16 : Functions.sign_extend (m := 64) 16#12 = BitVec.ofNat 64 16 := by decide
  have s24 : Functions.sign_extend (m := 64) 24#12 = BitVec.ofNat 64 24 := by decide
  have s32 : Functions.sign_extend (m := 64) 32#12 = BitVec.ofNat 64 32 := by decide
  have s40 : Functions.sign_extend (m := 64) 40#12 = BitVec.ofNat 64 40 := by decide
  have s48 : Functions.sign_extend (m := 64) 48#12 = BitVec.ofNat 64 48 := by decide
  have f2 (off : Nat) (h : off ≤ 56) := spot2.field_nat off h
  have f3 (off : Nat) (h : off ≤ 56) := spot3.field_nat off h
  have low2 := spot2.low
  have low3 := spot3.low
  have high2 := spot2.high
  have domNat : firstDomainPtr.toNat = 0x8007d150 := rfl
  have stateNat : (BitVec.ofNat 64 Layout.sym_Caml_state).toNat = 0x80064d08 := rfl
  have field120 : (firstDomainPtr + 120#64).toNat = 0x8007d150 + 120 := rfl
  unfold heapStart at low2 low3
  unfold heapEnd at high2
  have outside : ImageOutside (tableResetLog t2 ++ tableClearLog t3) := by
    constructor <;> simp only [tableResetLog, tableClearLog, List.cons_append, List.nil_append, OutLRange,
      f2 8 (by decide), f2 16 (by decide), f2 24 (by decide), f2 32 (by decide), f3 40 (by decide),
      f3 48 (by decide), and_true] <;>
      simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;> omega
  apply registers_of_blocks' leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput caml_set_minor_heap_sizeXa364TSeg 0x8000a364#64
        [(8, t2), (9, BitVec.ofNat 64 Layout.sym_Caml_state)]
        [read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat, read8 c.σ.mem (firstDomainPtr + 120#64).toNat,
          read8 c.σ.mem t3.toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 9]; decide
      shape := by change ChainOK _ [8, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := minorHeapRefC_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_set_minor_heap_size_at_"
        all_goals rck
        · exact (spot2.window 0 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · past_stores
          · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 by constructor <;> decide).ld rfl
              (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff]) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff, f2 8 (by decide), f2 16 (by decide),
            f2 24 (by decide), f2 32 (by decide), and_true]; (try simp only [stateNat, field120, domNat]); omega)
        · exact (spot2.window 8 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · exact (spot2.window 32 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · exact (spot2.window 16 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · exact (spot2.window 24 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · past_stores
          · exact (show ReadWindow (firstDomainPtr + 120#64) 8 by constructor <;> decide).ld rfl
              (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff]) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff, f2 8 (by decide), f2 16 (by decide),
            f2 24 (by decide), f2 32 (by decide), and_true]; (try simp only [stateNat, field120, domNat]); omega)
        · past_stores
          · exact spot3.read.ld rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff]) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff, f2 8 (by decide), f2 16 (by decide),
            f2 24 (by decide), f2 32 (by decide), and_true]; (try simp only [stateNat, field120, domNat]); omega)
        · exact (spot3.window 40 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · exact (spot3.window 48 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48, s120, state, tbl, ite_true, ite_false, Nat.reduceEqDiff])
        · simp only [state, s120, tbl, sext_zero, BitVec.add_zero, base]
          rfl }))
  · simp only [caml_set_minor_heap_sizeXa364TSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff,
      ite_true, ite_false, List.headD_cons, List.tail_cons, minorheaprefc_line_8000a364, minorheaprefc_line_8000a368, minorheaprefc_line_8000a36c, minorheaprefc_line_8000a370, minorheaprefc_line_8000a374, minorheaprefc_line_8000a378, minorheaprefc_line_8000a37c, minorheaprefc_line_8000a380, minorheaprefc_line_8000a384, minorheaprefc_line_8000a388]
    simp only [state, s120, tbl, sext_zero, BitVec.add_zero, s8, s16, s24, s32, s40, s48]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_set_minor_heap_sizeXa364TSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, minorheaprefc_line_8000a364, minorheaprefc_line_8000a368, minorheaprefc_line_8000a36c, minorheaprefc_line_8000a370, minorheaprefc_line_8000a374, minorheaprefc_line_8000a378, minorheaprefc_line_8000a37c, minorheaprefc_line_8000a380, minorheaprefc_line_8000a384, minorheaprefc_line_8000a388] at pins
    exact ⟨gholds_lookup_eq pins rfl state, gholds_lookup_eq pins rfl (by simp only [state, s120, tbl]),
      gholds_lookup_eq pins rfl (by simp only [state, s120, tbl, sext_zero, BitVec.add_zero, base]),
      gholds_lookup (n := 9) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- `custom_table`'s remaining fields, in the order the code clears them. -/
def tableTailLog (t : BitVec 64) : List WEntry :=
  [((t + 8#64).toNat, 8, 0#64), ((t + 32#64).toNat, 8, 0#64), ((t + 16#64).toNat, 8, 0#64),
    ((t + 24#64).toNat, 8, 0#64), (t.toNat, 8, 0#64)]

theorem minor_ref_last (c : Config) (ra t v : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(8, t), (10, v)])
    (spot : RefTableSpot t) :
    FnSummary 0x8000a394#64 (fun e => e = c) (WriteRegistersPost [] (tableTailLog t) c 0x8000a3a8#64 v
      [(8, t), (10, v)]) := by
  have s8 : Functions.sign_extend (m := 64) 8#12 = BitVec.ofNat 64 8 := by decide
  have s16 : Functions.sign_extend (m := 64) 16#12 = BitVec.ofNat 64 16 := by decide
  have s24 : Functions.sign_extend (m := 64) 24#12 = BitVec.ofNat 64 24 := by decide
  have s32 : Functions.sign_extend (m := 64) 32#12 = BitVec.ofNat 64 32 := by decide
  have f (off : Nat) (h : off ≤ 56) := spot.field_nat off h
  have low := spot.low
  unfold heapStart at low
  have outside : ImageOutside (tableTailLog t) := by
    constructor <;> simp only [tableTailLog, OutLRange, f 8 (by decide), f 16 (by decide), f 24 (by decide),
      f 32 (by decide), and_true] <;>
      simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;> omega
  apply registers_of_blocks' leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput caml_set_minor_heap_sizeXa394Seg 0x8000a394#64 [(8, t), (10, v)] [] c
      from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 10]; decide
      shape := by change ChainOK _ [8, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := minorHeapRefD_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_set_minor_heap_size_at_"
        · exact (spot.window 8 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, stepGM, eraseG, wvalM, stepLdsM, List.headD, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, minorheaprefd_line_8000a394, minorheaprefd_line_8000a398, minorheaprefd_line_8000a39c, minorheaprefd_line_8000a3a0, minorheaprefd_line_8000a3a4, s8])
        · exact (spot.window 32 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, stepGM, eraseG, wvalM, stepLdsM, List.headD, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, minorheaprefd_line_8000a394, minorheaprefd_line_8000a398, minorheaprefd_line_8000a39c, minorheaprefd_line_8000a3a0, minorheaprefd_line_8000a3a4, s32])
        · exact (spot.window 16 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, stepGM, eraseG, wvalM, stepLdsM, List.headD, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, minorheaprefd_line_8000a394, minorheaprefd_line_8000a398, minorheaprefd_line_8000a39c, minorheaprefd_line_8000a3a0, minorheaprefd_line_8000a3a4, s16])
        · exact (spot.window 24 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, stepGM, eraseG, wvalM, stepLdsM, List.headD, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, minorheaprefd_line_8000a394, minorheaprefd_line_8000a398, minorheaprefd_line_8000a39c, minorheaprefd_line_8000a3a0, minorheaprefd_line_8000a3a4, s24])
        · exact (spot.window 0 (by decide) (by decide)).sd rfl
            (by simp only [eaddrM, srcVal, lookupG, stepGM, eraseG, wvalM, stepLdsM, List.headD, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, minorheaprefd_line_8000a394, minorheaprefd_line_8000a398, minorheaprefd_line_8000a39c, minorheaprefd_line_8000a3a0, minorheaprefd_line_8000a3a4, sext_zero]) }))
  · simp only [caml_set_minor_heap_sizeXa394Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, wlogM,
      wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, minorheaprefd_line_8000a394, minorheaprefd_line_8000a398, minorheaprefd_line_8000a39c, minorheaprefd_line_8000a3a0, minorheaprefd_line_8000a3a4, s8, s16, s24, s32, sext_zero, BitVec.add_zero]
    rfl
  · rfl
  · intro σ pins
    exact pins
  · rfl
  · decide

def minorSavedLoads (m : Std.ExtHashMap Nat (BitVec 8)) (sp : BitVec 64) : List (List (BitVec 8)) :=
  [read8 m (nativeFrameBase sp 64 + 56), read8 m (nativeFrameBase sp 64 + 48), read8 m (nativeFrameBase sp 64 + 40),
    read8 m (nativeFrameBase sp 64 + 32), read8 m (nativeFrameBase sp 64 + 24)]

/-- Restore ra, s0–s3 and return. -/
theorem minor_return (c : Config) (sp ra s0 s1 s2 s3 v oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ [(2, nativeStack sp 64), (10, v)])
    (saved : ∀ off value, (off, value) ∈ minorSlots ra s0 s1 s2 s3 →
      bytesT c.σ.mem (nativeFrameBase sp 64 + off) 8 = value)
    (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8000a3a8#64 (fun e => e = c) (WriteRegistersPost [1, 8, 9, 18, 19, 2] [] c ra v
      [(2, sp), (19, s3), (18, s2), (9, s1), (8, s0), (1, ra), (10, v)]) := by
  have word (off : Nat) (value : BitVec 64) (member : (off, value) ∈ minorSlots ra s0 s1 s2 s3) :
      bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + off)) = value := by
    rw [read8_value]; exact saved off value member
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_set_minor_heap_sizeXa3a8Seg 0x8000a3a8#64
        [(2, nativeStack sp 64), (10, v)] (minorSavedLoads c.σ.mem sp) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := minorHeapReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_set_minor_heap_size_at_"
        · exact (frame.read_slot (off := 56) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 48) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 56)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [word 56 ra (by simp [minorSlots]), ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 56)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [word 56 ra (by simp [minorSlots]), ret_tgt ra aligned]
  · simp only [caml_set_minor_heap_sizeXa3a8Seg, minorSavedLoads, evalBlocks, evalBlock, SegEvalState.init, runGM,
      stepGM, stepLdsM, ldsRunM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, List.headD_cons, List.tail_cons, minorheapreturn_line_8000a3a8, minorheapreturn_line_8000a3ac, minorheapreturn_line_8000a3b0, minorheapreturn_line_8000a3b4, minorheapreturn_line_8000a3b8, minorheapreturn_line_8000a3bc]
    rw [show Functions.sign_extend (m := 64) 64#12 = 64#64 by decide, nativeStack_restore,
      word 56 ra (by simp [minorSlots]), word 48 s0 (by simp [minorSlots]), word 40 s1 (by simp [minorSlots]),
      word 32 s2 (by simp [minorSlots]), word 24 s3 (by simp [minorSlots])]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
