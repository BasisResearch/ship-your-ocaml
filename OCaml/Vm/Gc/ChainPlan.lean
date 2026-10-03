import OCaml.Vm.Primitives.AccessPlan

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

end OCaml.Vm.Gc
