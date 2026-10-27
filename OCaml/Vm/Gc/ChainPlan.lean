import OCaml.Vm.Primitives.AccessPlan
import Vsa.Sim.SegmentSummary

namespace OCaml.Vm.Gc
open Vsa.Sim OCaml.Vm.Primitives

/-- Code-only facts for a generated block, independent of data operands. -/
structure BlockCode (mem : Std.ExtHashMap Nat (BitVec 8)) (b : BBlock) : Prop where
  body : CodeFacts mem b.body
  term : TermPins mem b.term

/-- A code certificate can be reused at every visit to a collector loop. -/
def ChainCode (mem : Std.ExtHashMap Nat (BitVec 8)) (bs : List BBlock) : Prop :=
  ∀ b ∈ bs, BlockCode mem b

/-- Scalar accesses and the branch choice at one generated block. -/
structure BlockAccess (mem : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs)
    (lds : List (List (BitVec 8))) (b : BBlock) : Prop where
  data : AccessPlan mem L lds b.body
  control : TermFactsO (runGM b.body L lds) b.term

/-- Finite access certificates follow the evaluator's symbolic memory and
register updates. They contain no execution or collector-correctness premise. -/
inductive ChainAccess : Std.ExtHashMap Nat (BitVec 8) → GRegs →
    List (List (BitVec 8)) → List BBlock → Prop where
  | nil {m L lds} : ChainAccess m L lds []
  | cons {m L lds b bs} : BlockAccess m L lds b →
      ChainAccess (writeLog m (wlogM b.body L lds)) (runGM b.body L lds)
        (ldsRunM b.body lds) bs → ChainAccess m L lds (b :: bs)

/-- Recombine generated code facts and scalar access plans through the
existing block kernel. This is a finite certificate fold, not run induction. -/
theorem chainPlan_facts {mc m L lds bs}
    (code : ChainCode mc bs) (access : ChainAccess m L lds bs) :
    ChainFacts mc m L lds bs := by
  induction access with
  | nil => trivial
  | @cons m L lds b bs block tail ih =>
      have pins := code b (by simp)
      exact ⟨⟨accessPlan_facts pins.body block.data, pins.term, block.control⟩,
        ih (fun b hb => code b (by simp [hb]))⟩

/-- Reuse the complete block kernel result wherever a reflected-segment post
is expected; machine clients keep the original result's frame as well. -/
theorem segmentPost_of_block {bs entry L lds before after}
    (post : BlockPost bs entry L lds before after) :
    SegmentPost bs L lds entry before.σ.mem after :=
  ⟨post.good, post.memory, post.pc, post.tick, post.minstret, post.regs⟩

/-- The memory `AccessPlan` threads through a body: each store applied in turn. -/
def memAfter : Std.ExtHashMap Nat (BitVec 8) → List MInstr → GRegs → List (List (BitVec 8)) →
    Std.ExtHashMap Nat (BitVec 8)
  | m, [], _, _ => m
  | m, a :: rest, L, lds => memAfter (stepMemM m a L) rest (stepGM a L (lds.headD [])) (stepLdsM a.kind lds)

/-- The threaded memory is the body's write log applied: a store mid-body
is read back through `writeLog`, not by unfolding the store chain. -/
theorem memAfter_eq (m : Std.ExtHashMap Nat (BitVec 8)) (body : List MInstr) (L : GRegs)
    (lds : List (List (BitVec 8))) : memAfter m body L lds = writeLog m (wlogM body L lds) := by
  induction body generalizing m L lds with
  | nil => rfl
  | cons a rest ih =>
    cases hk : a.kind <;> simp [memAfter, wlogM, stepMemM, stepGM, stepLdsM, hk, ih, writeLog]

/-- Compose bounded scalar-access certificates using the certified first-order
log; intermediate register states are supplied by the chunk certificates. -/
theorem accessPlan_append {m L loads xs ys}
    (first : AccessPlan m L loads xs)
    (second : AccessPlan (writeLog m (wlogM xs L loads)) (runGM xs L loads)
      (ldsRunM xs loads) ys) : AccessPlan m L loads (xs ++ ys) := by
  rw [← memAfter_eq] at second
  induction xs generalizing m L loads with
  | nil => exact second
  | cons a xs ih => exact ⟨first.1, ih first.2 second⟩

end OCaml.Vm.Gc
