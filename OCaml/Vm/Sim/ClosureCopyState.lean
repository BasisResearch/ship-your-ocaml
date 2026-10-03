import OCaml.Vm.Sim.IndexedCopyState

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def closureCopyWrites : List Register := [Register.x12, Register.x13, Register.x14, Register.x15] ++ noiseRegs

abbrev closureCopyShape : IndexedCopyShape :=
  ⟨false, 2, 13, 16, 15, 11, 0x80002a44#64, 0x80002a60#64, closureCopyWrites⟩

/-- CLOSURE advances the source cursor and indexes destination fields after metadata. -/
abbrev ClosureCopyRegion := IndexedCopyRegion closureCopyShape
abbrev ClosureCopyAt := IndexedCopyAt closureCopyShape
abbrev ClosureCopyPost := IndexedCopyPost closureCopyShape

end OCaml.Vm.Sim
