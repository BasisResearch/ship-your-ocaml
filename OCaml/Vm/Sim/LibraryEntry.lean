import OCaml.Vm.Sim.CcallSetup
import OCaml.Vm.Primitives.Memmove

/-!
# Library readiness at a C_CALL entry

newlib's library model (`LibraryReady`, for memmove and the stdio path)
needs every integer register present, the C runtime's global pointer, and an
idle HTIF device. The loop registers carry all three through the C_CALL setup
(`setup.input.loop`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **`LibraryReady` at a C_CALL callee entry.** -/
theorem CcallSetupPost.libraryReady {ra : BitVec 64} {args : List Val} {L : OCaml.Layout} {P : Prog}
    {s : St} {pl : Place} {cp : ChanPlace} {sp high domain entry : Nat} {env : BitVec 64} {c : Config}
    (setup : CcallSetupPost ra args L P s pl cp sp high domain entry env c) : LibraryReady c :=
  ⟨fun n lo hi => setup.input.loop.gprs.get n lo (by omega), setup.input.loop.gp, setup.input.loop.htifIdle⟩

end OCaml.Vm.Sim
