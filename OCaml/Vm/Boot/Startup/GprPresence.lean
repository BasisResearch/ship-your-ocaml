import Vsa.Sim.SegToTripleFramed
import OCaml.Vm.Primitives.Blocks
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Presence, independent of values, of the architectural integer registers. -/
structure GprPresent (s : MState) : Prop where
  get : ∀ n, 1 ≤ n → n < 32 → (gprGet s n).isSome

private theorem no_noise : ∀ n, n < 32 → 1 ≤ n →
    ∀ r ∈ noiseRegs, (r == gprReg n) = false := by decide

/-- A finite write set and its output pins preserve complete GPR presence. -/
theorem GprPresent.of_frame {before after : MState} {writes : List Nat}
    (p : GprPresent before) (keys : KeysOK writes)
    (written : ∀ n ∈ writes, (gprGet after n).isSome)
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ writes, (gprReg n == r) = false) →
      after.regs.get? r = before.regs.get? r) : GprPresent after := by
  constructor
  intro n lo hi
  by_cases hw : n ∈ writes
  · exact written n hw
  · rw [gprGet_of_frame n lo (by omega) (no_noise n hi lo) ?_ frame]
    · exact p.get n lo hi
    · intro m hm
      have bound := keys m hm
      exact gprReg_beq_false m (by omega) n hi bound.1 lo (fun eq => hw (eq ▸ hm))

/-- A symbolic pin list covers all changed registers by a finite key check. -/
theorem GprPresent.of_regs {before after : MState} {writes : List Nat} {L : GRegs}
    (p : GprPresent before) (keys : KeysOK writes) (pins : GHolds after L)
    (cover : ∀ n ∈ writes, n ∈ keysG L)
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ writes, (gprReg n == r) = false) →
      after.regs.get? r = before.regs.get? r) : GprPresent after := by
  apply p.of_frame keys ?_ frame
  intro n hn
  obtain ⟨v, value⟩ := lookup_of_mem L (cover n hn)
  rw [gholds_lookup L pins value]
  rfl

/-- Generated blocks retain their full architectural presence invariant. -/
theorem BlockPost.gpr_present {bs entry L loads before after}
    (p : BlockPost bs entry L loads before after) (beforePins : GprPresent before.σ)
    (keys : KeysOK (wrChain bs))
    (cover : ∀ n ∈ wrChain bs, n ∈ keysG (evalBlocks bs (SegEvalState.init L loads)).regs) :
    GprPresent after.σ := beforePins.of_regs keys p.regs cover p.frame

/-- Direct calls change only the return-link GPR. -/
theorem GprPresent.of_link {before after : MState} {link : BitVec 64}
    (p : GprPresent before) (saved : gprGet after 1 = some link)
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) → r ≠ .x1 →
      after.regs.get? r = before.regs.get? r) : GprPresent after := by
  apply p.of_frame (writes := [1]) (by decide)
  · intro n hn
    have eq : n = 1 := List.mem_singleton.mp hn
    subst n
    rw [saved]; rfl
  · intro r noise outside
    apply frame r noise
    intro eq
    subst r
    have := outside 1 (by decide)
    contradiction

/-- The same rule for public call-boundary frames, whose exclusions use `≠`. -/
theorem GprPresent.of_regs_ne {before after : MState} {writes : List Nat} {L : GRegs}
    (p : GprPresent before) (keys : KeysOK writes) (pins : GHolds after L)
    (cover : ∀ n ∈ writes, n ∈ keysG L)
    (frame : ∀ r : Register, (∀ n ∈ writes, gprReg n ≠ r) →
      (∀ q ∈ noiseRegs, (q == r) = false) →
      after.regs.get? r = before.regs.get? r) : GprPresent after :=
  p.of_regs keys pins cover fun r noise outside =>
    frame r (fun n hn => beq_eq_false_iff_ne.mp (outside n hn)) noise
end OCaml.Vm.Boot.Startup
