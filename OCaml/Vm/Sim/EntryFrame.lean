import OCaml.Vm.Caller
import OCaml.Vm.Sim.InterpEntrySaveSegment
import OCaml.Vm.Sim.InterpEntrySavePins
import OCaml.Vm.Primitives.ImageFrame
import Vsa.Sim.SegToTripleFramed

/-!
# Native frame addressing for `caml_interprete`'s entry

The generated entry segments address the interpreter frame as
`(sp + sext 0xdf0) + sext off` (the prologue's `addi sp, sp, -528`, then an
`sd` offset). `slot_nat` normalizes every such address to `sp - 528 + off`
once; `slot_tac` then closes each store's RAM/HTIF/alignment/code-range
premise by `omega` from the caller's frame bounds (`InterpCaller`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem sext12_pos (x : BitVec 12) (h : x.toNat < 2048) :
    (sign_extend (m := 64) x).toNat = x.toNat := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · simp only [BitVec.toNat_setWidth]; omega
  · simp [BitVec.msb_eq_decide]; omega

theorem sext12_neg (x : BitVec 12) (h : 2048 ≤ x.toNat) :
    (sign_extend (m := 64) x).toNat = x.toNat + (18446744073709551616 - 4096) := by
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  have : x.msb = true := by simp [BitVec.msb_eq_decide]; omega
  simp only [this, ite_true]
  have := x.isLt
  omega

/-- The interpreter frame's slot addresses, normalized. -/
theorem slot_nat (sp : Nat) (x : BitVec 12) (h1 : 528 ≤ sp) (h2 : sp < 4294967296) (hx : x.toNat < 2048) :
    ((BitVec.ofNat 64 sp + sign_extend (m := 64) (0xdf0#12)) + sign_extend (m := 64) x).toNat =
      sp - 528 + x.toNat := by
  have hneg : (sign_extend (m := 64) (0xdf0#12)).toNat = 18446744073709551088 := by
    rw [sext12_neg _ (by decide)]; rfl
  have hs : (BitVec.ofNat 64 sp).toNat = sp := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, BitVec.toNat_add, hneg, sext12_pos x hx, hs]
  have e1 : (sp + 18446744073709551088) % 18446744073709551616 = sp - 528 := by omega
  rw [show (2:Nat)^64 = 18446744073709551616 from rfl, e1]
  omega

/-- The new native sp itself. -/
theorem frame_sp (sp : Nat) (h1 : 528 ≤ sp) (h2 : sp < 4294967296) :
    BitVec.ofNat 64 sp + sign_extend (m := 64) (0xdf0#12) = BitVec.ofNat 64 (sp - 528) := by
  apply BitVec.eq_of_toNat_eq
  have hneg : (sign_extend (m := 64) (0xdf0#12)).toNat = 18446744073709551088 := by
    rw [sext12_neg _ (by decide)]; rfl
  rw [BitVec.toNat_add, hneg, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (2:Nat)^64 = 18446744073709551616 from rfl]
  omega

/-- The frame bounds every entry store premise needs, from the caller. -/
structure EntryFrame (sp : Nat) : Prop where
  low : Vsa.Sim.DlHeap.heapEnd + Layout.interpFrameBytes ≤ sp
  high : sp + Layout.camlMainFrameBytes ≤ Layout.sym_stack_top
  aligned : sp % 16 = 0

theorem EntryFrame.of_caller {P : OCaml.Bytecode.Prog} {c : Config} {pl : OCaml.Vm.Place}
    {cp : OCaml.Vm.ChanPlace} {high sp : Nat} {callerRegs mainSaved : Nat → BitVec 64}
    (h : OCaml.Vm.InterpCaller P c pl cp high sp callerRegs mainSaved) : EntryFrame sp :=
  ⟨h.frameLow, h.frameHigh, h.aligned⟩

theorem EntryFrame.nat {sp : Nat} (h : EntryFrame sp) :
    0x86800210 ≤ sp ∧ sp + 112 ≤ 0x88000000 ∧ sp % 16 = 0 := by
  have := h.low; have := h.high; have := h.aligned
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.interpFrameBytes, Layout.camlMainFrameBytes,
    Layout.sym_stack_top] at *
  omega

/-- A log whose entries all start at or above `lo` misses any range ending at `lo`. -/
theorem outLRange_of_above {log : List WEntry} {lo a n : Nat}
    (h : ∀ e ∈ log, lo ≤ e.1) (hr : a + n ≤ lo) : OutLRange log a n := by
  induction log with
  | nil => trivial
  | cons e log ih =>
    exact ⟨Or.inl (by have := h e (by simp); omega), ih (fun e' he' => h e' (by simp [he']))⟩

/-- Logs above the allocator arena miss the executable image. -/
theorem image_outside_of_above {log : List WEntry}
    (h : ∀ e ∈ log, Vsa.Sim.DlHeap.heapEnd ≤ e.1) : OCaml.Vm.Primitives.ImageOutside log :=
  ⟨outLRange_of_above h (by decide), outLRange_of_above h (by decide)⟩

/-- A step frame preserves every listed GPR it does not write (one `decide`). -/
theorem _root_.Vsa.Sim.StepFrameOut.gpr_list {W : List Register} {σ σ' : MState} (h : StepFrameOut W σ σ')
    {L : List Nat} (hL : ∀ n ∈ L, 1 ≤ n ∧ n ≤ 31 ∧ ∀ r ∈ W, (r == gprReg n) = false) :
    ∀ n ∈ L, gprGet σ' n = gprGet σ n := by
  intro n hn
  obtain ⟨h1, h31, hw⟩ := hL n hn
  gpr_cases n => exact h.frame _ hw

end OCaml.Vm.Sim

/-- Close a generated store premise about a normalized frame address. -/
macro "slot_tac" : tactic =>
  `(tactic| first
    | omega
    | (simp only [Vsa.Sim.tohostAddr, Vsa.Sim.LibraryLayout.tohostAddr]; omega)
    | (right; omega))
