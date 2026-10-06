import OCaml.Vm.Sim.SwitchRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode

/-- A successful tag lookup excludes integers and exposes SWITCH's block rule
(behind the guard rejecting atom and interior-pointer selectors). -/
theorem switch_tag_step {P : Prog} {s : St} {tag : Nat} (sizes : Int) (table : List Int)
    (tagOf : tag? s.heap s.accu = some tag) :
    stepI P s ⟨.SWITCH, sizes :: table⟩ = if s.accu.switchExotic then .unsupported else
      opt (if tag < sizes.toNat / 65536 then some (sizes.toNat % 65536 + tag) else none)
        (fun k => opt table[k]? fun ofs => opt (target s.pc 1 ofs) fun dest => .next {s with pc := dest}) := by
  cases ha : s.accu with
  | int n => simp [tag?, ha] at tagOf
  | code pc => simp [tag?, ha] at tagOf
  | raw w => simp [tag?, ha] at tagOf
  | atom t =>
    simp only [ha] at tagOf
    simp only [stepI, ha, tagOf, Option.bind_some]
  | ptr l k =>
    simp only [ha] at tagOf
    simp only [stepI, ha, tagOf, Option.bind_some]

/-- Nonnegative packed size operands have identical native and semantic naturals. -/
theorem switch_sizes_nat (sizes : BitVec 32) (positive : 0 ≤ sizes.toInt) :
    sizes.toInt.toNat = sizes.toNat := by
  have bound := sizes.isLt
  rw [BitVec.toInt_eq_toNat_cond] at positive ⊢
  split <;> omega

end OCaml.Vm.Sim
