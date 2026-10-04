import OCaml.Vm.Sim.StopState

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Uncaught return restores the two domain fields before decrementing callback depth. -/
def uncaughtLog (nativeSp : Nat) (vmSp : BitVec 64) (c : Config) : List WEntry :=
  [((word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp, 8, vmSp),
   ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise, 8, word c (nativeSp + 24)),
   (Layout.sym_caml_callback_depth, 4, stopDepth c)]

/-- Both return paths touch the same byte ranges, in different orders. -/
theorem uncaught_outside {nativeSp : Nat} {vmSp : BitVec 64} {c : Config} {a width : Nat}
    (outside : OutLRange (stopLog nativeSp vmSp c) a width) :
    OutLRange (uncaughtLog nativeSp vmSp c) a width := by
  simpa only [uncaughtLog, stopLog, OutLRange, and_assoc, and_left_comm, and_comm] using outside

/-- The native uncaught branch has already computed the enclosing VM stack cut. -/
structure UncaughtReturnInput (nativeSp : Nat) (saved : Nat → BitVec 64) (value vmSp : BitVec 64) (c : Config) : Prop
    extends StopInvocation nativeSp saved vmSp c where
  good : GoodState c.σ
  image : ExecutableImage c
  pc : pcOf c = some (0x800035f0#64)
  tick : c.tick < 2
  domain : gpr c 15 = some (word c Layout.sym_Caml_state)
  vmStack : gpr c 13 = some vmSp
  value : gpr c Layout.reg_accu = some value

/-- The exception marker is added before the same native ABI restoration. -/
abbrev UncaughtReturnPost (before : Config) (nativeSp : Nat) (saved : Nat → BitVec 64)
    (value vmSp : BitVec 64) (after : Config) :=
  InterpRuntimeReturnPost before nativeSp saved (value ||| 2#64) (uncaughtLog nativeSp vmSp before) after

end OCaml.Vm.Sim
