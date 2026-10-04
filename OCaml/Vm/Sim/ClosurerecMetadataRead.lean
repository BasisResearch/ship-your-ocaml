import OCaml.Vm.Sim.ClosurerecObject
import OCaml.Vm.Sim.ClosurerecEncoding
import OCaml.Vm.Sim.ClosurerecInfixRead
import OCaml.Vm.Sim.ValueRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Native infix readbacks represent the model's three metadata values. -/
theorem closurerec_infix_values_read {after : Config} {pl : Place}
    {a functions index dest : Nat} (positive : 0 < index)
    (bound : index < functions) (small : 6 * functions < 2^64)
    (native : InfixHeapWords after.σ.mem pl a functions index dest) :
    ∀ i v, (closurerecFunctionGroup functions dest index)[i]? = some v →
      valWord pl v = some (word after (a + 24 * index - 8 + 8 * i)) := by
  simp only [closurerecFunctionGroup, if_neg (Nat.ne_of_gt positive), List.singleton_append]
  apply value_read_cons
  · change some _ = some (bytesT after.σ.mem _ 8)
    rw [native.header, infix_header_word]
  · have address : a + 24 * index - 8 + 8 = a + 24 * index := by omega
    rw [address]
    apply value_read_cons
    · change some _ = some (bytesT after.σ.mem _ 8)
      rw [native.code]
    · apply value_read_cons
      · have arity : Int.ofNat (3 * functions - 1) - 3 * Int.ofNat index =
            Int.ofNat (3 * functions - 1 - 3 * index) := by
          simp only [Int.ofNat_eq_natCast]
          omega
        rw [arity]
        change some (tag64 (BitVec.ofNat 63 (3 * functions - 1 - 3 * index))) =
          some (bytesT after.σ.mem _ 8)
        rw [native.arity, infix_arity_word functions index bound small]
      · intro i v selected
        simp at selected

/-- Consecutive infix groups form one consecutive represented field array. -/
theorem closurerec_tail_values_read {after : Config} {pl : Place} {a functions : Nat}
    (targets : List Nat) (index : Nat) (positive : 0 < index)
    (bound : index + targets.length ≤ functions) (small : 6 * functions < 2^64)
    (native : ∀ j dest, targets[j]? = some dest →
      InfixHeapWords after.σ.mem pl a functions (index + j) dest) :
    ∀ i v, ((targets.zipIdx index).map (fun (dest, k) =>
      closurerecFunctionGroup functions dest k)).flatten[i]? = some v →
      valWord pl v = some (word after (a + 24 * index - 8 + 8 * i)) := by
  induction targets generalizing index with
  | nil => simp
  | cons dest targets ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.flatten_cons]
    apply value_read_append
    · exact closurerec_infix_values_read positive (by simp only [List.length_cons] at bound; omega)
        small (native 0 dest rfl)
    · have size : (closurerecFunctionGroup functions dest index).length = 3 := by
        simp [closurerecFunctionGroup, Nat.ne_of_gt positive]
      rw [size]
      have address : a + 24 * index - 8 + 8 * 3 = a + 24 * (index + 1) - 8 := by omega
      rw [address]
      apply ih (index + 1) (by omega) (by simp only [List.length_cons] at bound; omega)
      intro j target selected
      have result := native (j + 1) target selected
      simpa only [Nat.add_assoc, Nat.add_comm 1 j] using result

/-- The first two fields and all infix triples form the represented metadata. -/
theorem closurerec_metadata_read {after : Config} {pl : Place} {a dest : Nat}
    (targets : List Nat) (small : 6 * (targets.length + 1) < 2^64)
    (firstCode : word after a = BitVec.ofNat 64 (pl.codeBase + 4 * dest))
    (firstArity : word after (a + 8) = BitVec.ofNat 64 (2 * (3 * (targets.length + 1) - 1) + 1))
    (native : ∀ j target, targets[j]? = some target →
      InfixHeapWords after.σ.mem pl a (targets.length + 1) (j + 1) target) :
    ∀ i v, (closurerecFunctionValues (dest :: targets))[i]? = some v →
      valWord pl v = some (word after (a + 8 * i)) := by
  simp only [closurerecFunctionValues, List.zipIdx_cons, List.map_cons,
    List.flatten_cons, List.length_cons]
  apply value_read_append
  · change ∀ i v, [Val.code dest, Val.ofInt (Int.ofNat (3 * (targets.length + 1) - 1))][i]? = some v → _
    apply value_read_cons
    · change some _ = some (word after a)
      rw [firstCode]
    · apply value_read_cons
      · change some (tag64 (BitVec.ofNat 63 (3 * (targets.length + 1) - 1))) = some (word after (a + 8))
        rw [firstArity, tagged_nat_word]
      · intro i v selected
        simp at selected
  · have size : (closurerecFunctionGroup (targets.length + 1) dest 0).length = 2 := by
      simp [closurerecFunctionGroup]
    rw [size]
    have address : a + 8 * 2 = a + 24 * 1 - 8 := by omega
    rw [address]
    apply closurerec_tail_values_read targets 1 (by omega) (by omega) small
    intro j target selected
    simpa only [Nat.add_comm 1 j] using native j target selected

end OCaml.Vm.Sim
