import OCaml.Vm.Primitives.Blocks
import Vsa.Sim.Muldi3Spec

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- Keep a callee's control fact separate from its load/pin certificate. -/
theorem singleton_chain_facts {mc m : Std.ExtHashMap Nat (BitVec 8)}
    {L : GRegs} {loads : List (List (BitVec 8))} {body : List MInstr} {term : Option TInstr}
    (hb : ProgFactsM mc m L loads body) (hp : TermPins mc term)
    (ht : TermFactsO (runGM body L loads) term) :
    ChainFacts mc m L loads [{body, term}] := ⟨⟨hb, hp, ht⟩, True.intro⟩

/-- A reusable return-alignment fact over an abstract register state.
This prevents the bit-vector return update from expanding concrete load values. -/
theorem return_facts (t : TInstr) {L : GRegs} {ra : BitVec 64}
    (hk : t.kind = .jr) (hs : t.rs1 = 1) (hi : t.imm12 = 0#12)
    (hr : srcVal 1 L = ra) (ha : ra.toNat % 4 = 0) : TermFactsO L (some t) := by
  simp only [TermFactsO, TermFactsT, hk, hs, hi]
  rw [hr, ret_tgt ra ha]
  exact ha

/-- A structural certificate independent of register values and load bytes. -/
def ReadOnlyBody (body : List MInstr) : Prop :=
  ∀ a ∈ body, a.kind ≠ .sw ∧ a.kind ≠ .sd ∧ a.kind ≠ .sb ∧ a.kind ≠ .sh

/-- Reflect the absence of stores without evaluating any data operands. -/
theorem readonly_wlog {body : List MInstr} (h : ReadOnlyBody body)
    (L : GRegs) (loads : List (List (BitVec 8))) : wlogM body L loads = [] := by
  induction body generalizing L loads with
  | nil => rfl
  | cons a body ih =>
    have ha := h a (by simp)
    have hb : ReadOnlyBody body := fun b hm => h b (by simp [hm])
    cases hk : a.kind <;> simp_all [wlogM]

/-- The read-only certificate is reusable for any initial ABI operands. -/
theorem readonly_log {body : List MInstr} (term : Option TInstr)
    (h : ReadOnlyBody body) (L : GRegs) (loads : List (List (BitVec 8))) :
    (evalBlocks [{body, term}] (SegEvalState.init L loads)).log = [] := by
  change [] ++ wlogM body L loads = []
  rw [readonly_wlog h, List.nil_append]

/-- Compose read-only certificates at a register-state checkpoint. The
intermediate register equality may be proved once and reused opaquely. -/
theorem readonly_facts_append {front back : List MInstr}
    {mc m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs}
    {loads : List (List (BitVec 8))} (h : ReadOnlyBody front)
    (hp : ProgFactsM mc m L loads front)
    (hs : ProgFactsM mc m (runGM front L loads) (ldsRunM front loads) back) :
    ProgFactsM mc m L loads (front ++ back) := by
  induction front generalizing L loads with
  | nil => exact hs
  | cons a front ih =>
    have ha := h a (by simp)
    have hr : ReadOnlyBody front := fun b hm => h b (by simp [hm])
    have hm : stepMemM m a L = m := by
      cases hk : a.kind <;> simp_all [stepMemM]
    obtain ⟨pins, decoded, memory, rest⟩ := hp
    change _ ∧ _ ∧ _ ∧ _
    refine ⟨pins, decoded, memory, ?_⟩
    rw [hm] at rest ⊢
    exact ih hr rest hs

/-- Code certificates have no dependency on symbolic data operands. -/
def CodeFacts (mc : Std.ExtHashMap Nat (BitVec 8)) : List MInstr → Prop
  | [] => True
  | a :: rest => BytePinsM mc a ∧ DecodeFactM a ∧ CodeFacts mc rest

def MemoryFree (k : MKind) : Prop :=
  match k with
  | .lw | .lwu | .ld | .lbu | .lh | .lhu | .sw | .sd | .sb | .sh => False
  | _ => True

/-- Register-only spans need code certificates, independently of their data. -/
theorem memory_free_facts {body : List MInstr} {mc : Std.ExtHashMap Nat (BitVec 8)}
    (code : CodeFacts mc body) (free : ∀ a ∈ body, MemoryFree a.kind)
    (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (loads : List (List (BitVec 8))) :
    ProgFactsM mc m L loads body := by
  induction body generalizing m L loads with
  | nil => trivial
  | cons a rest ih =>
    obtain ⟨pins, decoded, tailCode⟩ := code
    have ha := free a (by simp)
    have hr : ∀ b ∈ rest, MemoryFree b.kind := fun b hm => free b (by simp [hm])
    have hm : MemFacts m L (loads.headD []) a := by
      cases hk : a.kind <;> simp_all [MemoryFree, MemFacts]
    exact ⟨pins, decoded, hm, ih tailCode hr _ _ _⟩

/-- One scalar access followed by register-only work needs only its access fact. -/
theorem access_then_free_facts {a : MInstr} {rest : List MInstr}
    {mc m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs}
    {loads : List (List (BitVec 8))} (code : CodeFacts mc (a :: rest))
    (free : ∀ b ∈ rest, MemoryFree b.kind)
    (memory : MemFacts m L (loads.headD []) a) :
    ProgFactsM mc m L loads (a :: rest) := by
  obtain ⟨pins, decoded, tailCode⟩ := code
  exact ⟨pins, decoded, memory, memory_free_facts tailCode free _ _ _⟩

end OCaml.Vm.Primitives
