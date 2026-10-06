import OCaml.Vm.Sim.RaiseUncaughtCheck
import OCaml.Vm.Sim.RaiseUncaughtReturn

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Select and execute the entire native root-uncaught return through the shared epilogue.
The abstract pending-exception continuation remains a separate simulation obligation. -/
theorem raise_uncaught {nativeSp : Nat} {saved : Nat → BitVec 64} {value : BitVec 64} {high : Nat} {c : Config}
    (h : UncaughtCheckInput nativeSp saved value high c) :
    ∃ count after, StepsN count c after ∧ UncaughtReturnPost c nativeSp saved value (BitVec.ofNat 64 high) after := by
  obtain ⟨checkCount, checked, checkRun, checkPost⟩ := raise_uncaught_check h
  obtain ⟨returnCount, after, returnRun, returned⟩ := raise_uncaught_return checkPost.state
  refine ⟨checkCount + returnCount, after, checkRun.append returnRun, returned.good,
    returned.image, returned.tick, returned.pc, returned.stack, returned.value,
    returned.registers, ?_, returned.output.trans checkPost.output,
    returned.htif.trans checkPost.htif⟩
  simpa only [uncaughtLog, stopDepth, word, checkPost.memory] using returned.memory

end OCaml.Vm.Sim
