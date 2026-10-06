import OCaml.Vm.Sim.CcallSetup
import OCaml.Vm.Primitives.Memmove

/-!
# Library readiness at a C_CALL entry

newlib's library model (`LibraryReady`, for memmove and the stdio path)
needs every integer register present, the C runtime's global pointer, and an
idle HTIF device. The loop registers carry `gp` and the idle device through
the C_CALL setup (`setup.input.loop`); register presence is supplied by the
caller until the loop invariant carries it.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **`LibraryReady` at a C_CALL callee entry.** -/
theorem CcallSetupPost.libraryReady {ra : BitVec 64} {args : List Val} {L : OCaml.Layout} {P : Prog}
    {s : St} {pl : Place} {cp : ChanPlace} {sp high domain entry : Nat} {env : BitVec 64} {c : Config}
    (setup : CcallSetupPost ra args L P s pl cp sp high domain entry env c)
    (gprs : OCaml.Vm.Boot.Startup.GprPresent c.σ) : LibraryReady c :=
  ⟨fun n lo hi => gprs.get n lo (by omega), setup.input.loop.gp, setup.input.loop.htifIdle⟩

end OCaml.Vm.Sim
