import OCaml.Vm.Gc.CustomMem
import OCaml.Vm.Gc.Readback

/-! Conditional obstruction to the former global record-separation law.
The two writes below are memory observations, not a Sail execution. Empty
readiness/state predicates are not excluded by this result. -/
namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives
set_option autoImplicit false

/-- The rejected law: separation from every list reconstructed from memory,
without a selected allocator ledger or record ownership. -/
def GlobalRecordApart (state : Config → Nat → Prop) : Prop :=
  ∀ c x, state c x → ∀ chs, OpenChannelList c.σ.mem chs →
    ∀ r ∈ chs, x < r ∨ r + chanOffBuff + OCaml.Bytecode.ioBufferSize ≤ x

/-- Only the old contract's local apart and outside-write frame laws are
needed; accounting, physical completeness and native execution play no role. -/
structure CustomOutsideFrame (Ready : Nat → Config → Prop)
    (state : Config → Nat → Prop) : Prop where
  apart : ∀ c a, state c a → CallerApart c a
  frame : ∀ k c d, Ready k c →
    (∀ a, state c a → (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) →
    word d Layout.sym_Caml_state = word c Layout.sym_Caml_state →
    Ready k d ∧ (∀ a, state d a ↔ state c a)

/-- At a valid pinned domain with a retained minor-resource byte, unrestricted
outside-write framing cannot coexist with `GlobalRecordApart`. -/
theorem global_records_frame_obstruction
    {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (custom : CustomOutsideFrame Ready state) (global : GlobalRecordApart state)
    {c : Config} {k D : Nat} (ready : Ready k c)
    (pin : (word c Layout.sym_Caml_state).toNat = D)
    (low : Vsa.Sim.DlHeap.heapStart ≤ D)
    (high : D + Layout.domainStateBytes ≤ Vsa.Sim.DlHeap.heapEnd)
    (retained : state c (D + Layout.off_extra_heap_resources_minor)) : False := by
  let a := D + Layout.off_extra_heap_resources_minor
  let log : List WEntry :=
    [(Layout.sym_caml_all_opened_channels, 8, BitVec.ofNat 64 a),
      (a + chanOffNext, 8, 0#64)]
  let d : Config := { c with σ := { c.σ with mem := writeLog c.σ.mem log } }
  have constants : Layout.off_extra_heap_resources_minor = 96 ∧
      Layout.domainStateBytes = 928 ∧ chanOffNext = 48 := by decide
  obtain ⟨off, size, next⟩ := constants
  have bounds : Layout.sym_caml_all_opened_channels + 8 ≤ Vsa.Sim.DlHeap.heapStart ∧
      Layout.sym_Caml_state + 8 ≤ Vsa.Sim.DlHeap.heapStart ∧
      (Layout.sym_Caml_state + 8 ≤ Layout.sym_caml_all_opened_channels ∨
        Layout.sym_caml_all_opened_channels + 8 ≤ Layout.sym_Caml_state) ∧
      (Layout.sym_caml_extra_heap_resources + 8 ≤ Layout.sym_caml_all_opened_channels ∨
        Layout.sym_caml_all_opened_channels + 8 ≤ Layout.sym_caml_extra_heap_resources) := by decide
  have outside (x : Nat) (hs : state c x) : OutL log x := by
    have ap := custom.apart c x hs
    have static := ap.static
    have domain := ap.domainField
    simp only [domainAddr, pin] at domain
    have headOut : x < Layout.sym_caml_all_opened_channels ∨
        Layout.sym_caml_all_opened_channels + 8 ≤ x := by
      by_cases below : x < Vsa.Sim.DlHeap.heapStart
      · have h := static below
        unfold VsaIris.InExt at h
        omega
      · omega
    have nextOut : x < a + chanOffNext ∨ a + chanOffNext + 8 ≤ x := by
      apply Classical.byContradiction
      intro no
      have inDomain : VsaIris.InExt (D, Layout.domainStateBytes) x := by
        dsimp only [a] at no
        simp only [off, size, next] at *
        constructor <;> dsimp only <;> omega
      have h := domain inDomain
      unfold VsaIris.InExt at h
      dsimp only [a] at *
      simp only [off, next] at *
      omega
    simpa only [log, OutL, and_true] using And.intro headOut nextOut
  have memory : ∀ x, state c x → (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 :=
    fun x hs => congrArg (fun b : Option (BitVec 8) => b.getD 0)
      (writeLog_out c.σ.mem log x (outside x hs))
  have domain : word d Layout.sym_Caml_state = word c Layout.sym_Caml_state := by
    change bytesT (writeLog c.σ.mem log) Layout.sym_Caml_state 8 = _
    apply bytesT_writeLog_out
    simp only [log, OutLRange, and_true]
    dsimp only [a]
    simp only [off, next]
    constructor <;> omega
  obtain ⟨_, same⟩ := custom.frame k c d ready memory domain
  have aSmall : a < 2 ^ 64 := by
    dsimp only [a]
    simp only [Vsa.Sim.DlHeap.heapEnd, size] at high
    rw [off]
    omega
  have head : bytesT d.σ.mem Layout.sym_caml_all_opened_channels 8 = BitVec.ofNat 64 a := by
    exact word_writeLog_at c.σ.mem log 0 _ _ rfl (by
      simp only [log, List.drop, OutLRange, and_true]
      dsimp only [a]
      rw [off, next]
      omega)
  have tail : bytesT d.σ.mem (a + chanOffNext) 8 = 0#64 := by
    exact word_writeLog_at c.σ.mem log 1 _ _ rfl True.intro
  have opened : OpenChannelList d.σ.mem [a] := by
    unfold OpenChannelList
    rw [head, BitVec.toNat_ofNat, Nat.mod_eq_of_lt aSmall]
    apply OpenChannels.cons (by dsimp only [a]; rw [off]; omega)
    rw [tail]
    exact OpenChannels.nil
  have apart := global d a ((same a).mpr retained) [a] opened a List.mem_cons_self
  have positive : 0 < chanOffBuff + OCaml.Bytecode.ioBufferSize := by decide
  omega

end OCaml.Vm.Gc
