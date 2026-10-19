import OCaml.Vm.Gc.StackScan
import OCaml.Vm.Gc.LoopFold

/-! # The whole VM-stack loop of `caml_oldify_local_roots`

`StackScan.iteration` folded with the shared loop kernel (`loop_to_exit`).
The caller's invariant `Inv p copies c` (slot pointer `p`, published table
`copies`) supplies each iteration's input, its `caml_oldify_one` route and the
callee frame, and is re-established after it; `Done` holds at the exit. The
rank is `stack_high - s0`, with `stack_high` fixed by the invariant. -/
namespace OCaml.Vm.Gc.StackScan
open Vsa.Machine Vsa.Sim Vsa.Logic Primitives LeanRV64DExecutable

/-- **The loop's obligations** for a caller invariant `Inv` and exit condition `Done`. -/
structure ScanStep (R : Nat → BitVec 64) (high : BitVec 64) (pl : Place)
    (Inv : BitVec 64 → List PendingCopy → Config → Prop) (Done : Config → Prop) : Prop where
  head : ∀ p copies c, Inv p copies c → HeadInput R p c ∧ p.toNat + 8 ≤ high.toNat
  supply : ∀ p copies c, Inv p copies c → ∀ e, Jumped R p c e →
    SlotCall (LocalRootsSites.stackSite.linked (calleeR R p c.σ.mem)) copies pl e
  frame : ∀ p copies c, Inv p copies c → ∀ e copies' mid, Jumped R p c e →
    SlotDone (LocalRootsSites.stackSite.linked (calleeR R p c.σ.mem)) copies copies' pl e mid → CalleeFrame c mid
  next : ∀ p copies c after, Inv p copies c → Iterated R p copies pl c after → PCAt bodyPc after →
    ∃ copies', Inv (p + 8#64) copies' after
  done : ∀ p copies c after, Inv p copies c → Iterated R p copies pl c after → PCAt exitPc after → Done after
  donePc : ∀ c, Done c → PCAt exitPc c

/-- The distance from `s0` to `stack_high`. -/
def rank (high : BitVec 64) (c : Config) : Nat := high.toNat - ((gprGet c.σ 8).getD 0).toNat

theorem exit_ne_body : exitPc ≠ bodyPc := by decide

/-- **The VM-stack loop**, from any invariant state at the head to `Done`. -/
theorem loop {R : Nat → BitVec 64} {high : BitVec 64} {pl : Place}
    {Inv : BitVec 64 → List PendingCopy → Config → Prop} {Done : Config → Prop}
    (step : ScanStep R high pl Inv Done) :
    Triple (fun c => ∃ p copies, Inv p copies c) Done := by
  apply loop_to_exit (entry := bodyPc) (rank high)
  · rintro c ⟨p, copies, inv⟩
    exact (step.head p copies c inv).1.pc
  · intro c done onBody
    have exitAt := step.donePc c done
    rw [PCAt] at exitAt onBody
    rw [exitAt] at onBody
    exact exit_ne_body (Option.some.inj onBody)
  · rintro c ⟨p, copies, inv⟩
    obtain ⟨input, room⟩ := step.head p copies c inv
    obtain ⟨after, run, post⟩ := (iteration input (step.supply p copies c inv) (step.frame p copies c inv)).run
      c ⟨input.pc, rfl⟩
    refine ⟨after, run, ?_, ?_⟩
    · obtain ⟨e, copies', mid, jumped, done, memory, pc⟩ := post.slot
      by_cases more : continues (p + 8#64) mid.σ.mem = true
      · rw [if_pos more] at pc
        obtain ⟨copies'', inv'⟩ := step.next p copies c after inv post pc
        exact Or.inl ⟨_, _, inv'⟩
      · rw [if_neg more] at pc
        exact Or.inr (step.done p copies c after inv post pc)
    · have before : gprGet c.σ 8 = some p := gholds_lookup _ input.registers rfl
      have now : gprGet after.σ 8 = some (p + 8#64) := gholds_lookup _ post.registers rfl
      have sum : (p + 8#64).toNat = p.toNat + 8 := by
        rw [BitVec.toNat_add]
        have bound := high.isLt
        simp only [BitVec.toNat_ofNat]
        omega
      simp only [rank, before, now, Option.getD_some, sum]
      omega

end OCaml.Vm.Gc.StackScan
