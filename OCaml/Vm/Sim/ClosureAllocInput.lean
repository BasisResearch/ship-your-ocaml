import OCaml.Vm.Sim.ClosureReady

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The final two metadata stores have writable, aligned native addresses. -/
structure ClosureMetadataWrites (a : Nat) : Prop where
  code : RamWriteAt a 8
  arity : RamWriteAt (a + 8) 8

/-- Named G1 input for the complete ordinary closure constructor. -/
structure ClosureAllocInput (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high count dest a domain limit : Nat) (accu : BitVec 64) : Prop
    extends ClosureWriteOk P s c pl cp sp high count dest a domain accu where
  young : count ≤ 254
  push : ClosurePushInput sp count accu
  nursery : ClosureNurseryInput sp count a domain limit accu c
  initializer : ClosureInitInput sp count a domain accu c
  metadata : ClosureMetadataWrites a

end OCaml.Vm.Sim
