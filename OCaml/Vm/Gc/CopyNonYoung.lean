import OCaml.Vm.Gc.CopyEffect

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Shared union of writes from the immediate and non-young pointer routes. -/
def copyWrites : List Nat := [8,9,10,11,14,15]

/-- Actual field load/classification/store/advance for any value requiring
no oldification. Odd fields use the direct route; even fields execute both
strict nursery tests. The premise constrains data, not branch execution. -/
theorem copy_nonYoung {slot delta target index domain c}
    (input : ReadInput slot delta target index c)
    (domainReg : gprGet c.σ 22 = some (BitVec.ofNat 64 Layout.sym_Caml_state))
    (root : word c Layout.sym_Caml_state = domain) (windows : Young.Windows domain)
    (safe : (word c slot.toNat).toNat % 2 = 0 →
      ¬ ((Young.lowerWord domain c).toNat < (word c slot.toNat).toNat ∧
        (word c slot.toNat).toNat < (Young.upperWord domain c).toNat))
    (destination : WriteWindow (delta + slot) 8) (header : ReadWindow (target - 8#64) 8) :
    FnSummary pc (fun d => d = c) (CopyEffect copyWrites slot delta target index c) := by
  generalize choice : immediate slot c = tagged
  cases tagged
  · have even := even_of_immediate_false choice
    exact copy_even input even domainReg root windows (safe even) destination header
  · have immediateInput : Input slot delta target index c :=
      ⟨input.good, input.minstret, input.registers, input.tick, input.code,
        ⟨input.window, destination, header⟩, choice⟩
    apply (copy_machine immediateInput).weaken (fun _ h => h)
    intro after post
    exact (post.effect immediateInput).mono (by decide)

end OCaml.Vm.Gc.FieldCopy
