import OCaml.Vm.Sim.IndexedCopyState

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def forwardWrites : List Register := [Register.x13, Register.x14, Register.x15] ++ noiseRegs

abbrev restartCopyShape : IndexedCopyShape :=
  ⟨true, 3, 25, 13, 15, 12, 0x80002b94#64, 0x80002bb0#64, forwardWrites⟩

/-- RESTART specializes the indexed source / advancing destination copy. -/
abbrev ForwardCopyRegion := IndexedCopyRegion restartCopyShape
abbrev ForwardCopyAt := IndexedCopyAt restartCopyShape
abbrev ForwardCopyPost := IndexedCopyPost restartCopyShape
abbrev forwardIndex := indexedCopyIndex restartCopyShape

/-- Every loop store belongs to the final, image-separated write log. -/
theorem ForwardCopyRegion.entry {a target i : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : ForwardCopyRegion a target words initial) (bound : i < words.length) :
    (target + 8 * i, 8, words[i]) ∈ valueLog target words :=
  copy_store_entry bound

theorem forward_copy_loop {a target : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : ForwardCopyRegion a target words initial)
    (body : ∀ i, Vsa.Logic.Triple (fun c => ForwardCopyAt a target words initial i c ∧ i < words.length)
      (ForwardCopyAt a target words initial (i + 1))) :
    Vsa.Logic.Triple (ForwardCopyAt a target words initial 0)
      (ForwardCopyAt a target words initial words.length) :=
  indexed_copy_loop region body

end OCaml.Vm.Sim
