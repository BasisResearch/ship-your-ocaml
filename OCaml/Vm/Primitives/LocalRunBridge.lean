import VsaIris.Vsa.SymRun
import Vsa.Sim.DeriveLoop
import Vsa.Sim.FnSummary
import Batteries.Data.Fin.Lemmas

/-! Reuse the library's confined-run certificates as machine triples. The
least remaining certificate is a loop measure; the run kernel and
`loopFromBody` supply composition, without induction on a machine run. -/
namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst LeanRV64DExecutable

noncomputable def boundedRank (P : Nat → Prop) (bound : Nat) : Nat := by
  classical
  exact if h : ∃ i : Fin (bound + 1), P i.val then
    (Classical.choose ((Fin.exists_iff_exists_minimal (fun i : Fin (bound + 1) => P i.val)).mp h)).val
  else 0

structure BoundedRankSpec (P : Nat → Prop) (limit rank : Nat) : Prop where
  holds : P rank
  bound : rank ≤ limit
  least : ∀ k, k ≤ limit → P k → rank ≤ k

theorem boundedRank_spec {P : Nat → Prop} {bound : Nat}
    (h : ∃ i : Fin (bound + 1), P i.val) : BoundedRankSpec P bound (boundedRank P bound) := by
  classical
  simp only [boundedRank, dif_pos h]
  let found := (Fin.exists_iff_exists_minimal (fun i : Fin (bound + 1) => P i.val)).mp h
  have spec := Classical.choose_spec found
  refine ⟨spec.1, Nat.le_of_lt_succ (Classical.choose found).isLt, ?_⟩
  intro k hk hp
  by_cases good : (Classical.choose found).val ≤ k
  · exact good
  · exact False.elim (spec.2 ⟨k, by omega⟩ (by change k < (Classical.choose found).val; omega) hp)

/-- Read-only cells are outside the local run's owned mutable footprint. -/
structure LocalSeparation (ro : List (Nat × BitVec 64)) (text : List (Nat × BitVec 8))
    (rs : List Nat) (S : Nat → Prop) : Prop where
  registers : ∀ p ∈ ro, p.1 ∉ rs
  bytes : ∀ p ∈ text, ¬ S p.1

/-- The library model's observational frame, with its full well-formedness
invariant. It does not equate optional memory maps or raw output lists. -/
structure LocalFrame (live : Nat → Prop) (ro : List (Nat × BitVec 64))
    (text : List (Nat × BitVec 8)) (rs : List Nat) (S : Nat → Prop)
    (before after : Config) : Prop where
  good : VsaOk live after
  readOnly : ROHolds (vsaModel live) after ro text
  registers : ∀ r, r ∉ rs → (vsaModel live).reg after r = (vsaModel live).reg before r
  memory : ∀ a, ¬ S a → (vsaModel live).mem after a = (vsaModel live).mem before a
  output : (vsaModel live).out after = (vsaModel live).out before

structure LocalPost (live : Nat → Prop) (ro : List (Nat × BitVec 64))
    (text : List (Nat × BitVec 8)) (rs : List Nat) (S : Nat → Prop)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (before after : Config) : Prop extends LocalFrame live ro text rs S before after where
  result : Q ((vsaModel live).reg after) ((vsaModel live).mem after)

def localCertificate (live : Nat → Prop) (ro : List (Nat × BitVec 64))
    (text : List (Nat × BitVec 8)) (rs : List Nat) (S : Nat → Prop)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (c : Config) (n : Nat) : Prop :=
  LocalRun (vsaModel live) ro text rs S Q n ((vsaModel live).reg c) ((vsaModel live).mem c)

structure LocalInvariant (live : Nat → Prop) (ro : List (Nat × BitVec 64))
    (text : List (Nat × BitVec 8)) (rs : List Nat) (S : Nat → Prop)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (bound : Nat)
    (before after : Config) : Prop extends LocalFrame live ro text rs S before after where
  remaining : ∃ i : Fin (bound + 1), localCertificate live ro text rs S Q after i.val

/-- Fold a confined library certificate through the standard loop rule. -/
theorem localRun_triple {live ro text rs S Q bound} (before : Config)
    (separate : LocalSeparation ro text rs S)
    (good : VsaOk live before) (readOnly : ROHolds (vsaModel live) before ro text)
    (certificate : localCertificate live ro text rs S Q before bound) :
    Vsa.Logic.Triple (fun c => c = before) (LocalPost live ro text rs S Q before) := by
  classical
  let I := LocalInvariant live ro text rs S Q bound before
  let rank := fun c => boundedRank (localCertificate live ro text rs S Q c) bound
  let guard := fun c => ¬ Q ((vsaModel live).reg c) ((vsaModel live).mem c)
  have body : ∀ n, Vsa.Logic.Triple (fun c => I c ∧ guard c ∧ rank c = n)
      (fun c => I c ∧ rank c < n) := by
    intro n c h
    obtain ⟨inv, notDone, hn⟩ := h
    have least := boundedRank_spec inv.remaining
    have remaining := least.holds
    cases he : rank c with
    | zero =>
      have done : Q ((vsaModel live).reg c) ((vsaModel live).mem c) := by
        change localCertificate live ro text rs S Q c (rank c) at remaining
        rw [he] at remaining
        exact remaining
      exact False.elim (notDone done)
    | succ k =>
      change localCertificate live ro text rs S Q c (rank c) at remaining
      rw [he] at remaining
      rcases remaining with done | ⟨steps, segment⟩
      · exact False.elim (notDone done)
      obtain ⟨after, run, ok, regs, mem, out, next⟩ := segment c inv.good inv.readOnly
        (fun _ _ => rfl) (fun _ _ => rfl)
      have frame : LocalFrame live ro text rs S before after := {
        good := ok
        readOnly := ⟨fun p hp => (regs p.1 (separate.registers p hp)).trans (inv.readOnly.1 p hp),
          fun p hp => (mem p.1 (separate.bytes p hp)).trans (inv.readOnly.2 p hp)⟩
        registers := fun r hr => (regs r hr).trans (inv.registers r hr)
        memory := fun a ha => (mem a ha).trans (inv.memory a ha)
        output := out.trans inv.output }
      have kb : k ≤ bound := by
        have bound' := least.bound
        change rank c ≤ bound at bound'
        omega
      have ih : I after := ⟨frame, ⟨⟨k, by omega⟩, next⟩⟩
      have afterLeast := boundedRank_spec ih.remaining
      have decrease := afterLeast.least k kb next
      refine ⟨after, ?_, ih, ?_⟩
      · exact OCaml.Run.vsa_steps_iff.mpr
          ⟨steps + 1, OCaml.Run.vsa_stepsN_iff.mp (stepsN_of_reachesN run)⟩
      · change rank after ≤ k at decrease
        omega
  have loop := loopFromBody (I := I) (B := guard) rank body
  apply Vsa.Logic.Triple.conseq loop
  · intro c eq
    subst c
    exact ⟨⟨good, readOnly, fun _ _ => rfl, fun _ _ => rfl, rfl⟩,
      ⟨⟨bound, by omega⟩, certificate⟩⟩
  · intro after h
    exact ⟨h.1.toLocalFrame, Classical.not_not.mp h.2⟩

/-- Machine observations instantiate a symbolic library precondition. The
entry PC comes from FnSummary's own parked-entry premise. -/
structure SymbolicInput (live : Nat → Prop) (text : List (Nat × BitVec 8))
    (rs : List Nat) (S : Nat → Prop) (R : Nat → BitVec 64) (Mt : Vsa.MemRepr.Mem)
    (c : Config) : Prop where
  good : VsaOk live c
  readOnly : ROHolds (vsaModel live) c VsaIris.MallocFast.roR text
  registers : ∀ r ∈ rs, r ≠ VsaIris.PC → (vsaModel live).reg c r = R r
  memory : ∀ a, S a → (vsaModel live).mem c a = VsaIris.MallocFast.imgM Mt a

/-- Adapt any landed SWP library certificate to the function-summary API. -/
theorem symbolic_summary {live text rs S Q entry R Mt} (c : Config)
    (separate : LocalSeparation VsaIris.MallocFast.roR text rs S)
    (input : SymbolicInput live text rs S R Mt c)
    (spec : VsaIris.Sym.SWP live text rs S Q entry R Mt) :
    FnSummary entry (fun d => d = c)
      (LocalPost live VsaIris.MallocFast.roR text rs S Q c) := by
  constructor
  rintro before ⟨pc, rfl⟩
  obtain ⟨bound, certificate⟩ := spec
  have observations : VsaIris.Sym.Matches rs S entry R Mt
      ((vsaModel live).reg before) ((vsaModel live).mem before) := {
    pc := by
      change (before.σ.regs.get? Register.PC).getD 0 = entry
      rw [pc]
      rfl
    regs := input.registers
    img := input.memory }
  exact localRun_triple before separate input.good input.readOnly (certificate _ _ observations) before rfl

end OCaml.Vm.Primitives
