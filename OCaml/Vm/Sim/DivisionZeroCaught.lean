import OCaml.Vm.Sim.DivisionZero
import OCaml.Vm.Sim.DivisionZeroSemantics
import OCaml.Vm.Sim.NativeCaught

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- The complete dispatched zero path agrees with the caught bytecode exception step.
Representation readiness is stated on the explicit eight-store memory view. -/
theorem division_zero_caught_step (kind : DivisionKind)
    {L : OCaml.Layout} {P : Prog} {s s' : St} {pl : Place} {cp : ChanPlace}
    {code stackWord envWord domain nativeStack global value : BitVec 64}
    {buffer nativeSp sp high dest : Nat} {saved : Nat → BitVec 64} {c : Config}
    {x : BitVec 63} {tail rest : List Val} {exn env : Val} {link extra : BitVec 63}
    (select : DivisionZeroInput stackWord c)
    (native : DivisionZeroNativeInput code stackWord envWord domain nativeStack global value buffer saved c)
    (memory : ReentryMemory nativeSp c)
    (outside : ∀ a ∈ reentryControlWords c,
      OutLRange (divisionZeroNativeLog code stackWord envWord domain nativeStack value) a 8)
    (ready : CaughtReentryReady L P (divisionRaiseState s exn) pl cp nativeSp (sp + 8) high dest link extra env rest
      (nativeMemoryView c (divisionZeroNativeLog code stackWord envWord domain nativeStack value)))
    (returnPc : saved 1 = 0x80001e80#64) (returnSp : saved 2 = BitVec.ofNat 64 nativeSp)
    (accu : s.accu = .int x) (stack : s.stack = .int 0#63 :: tail)
    (field : field? s.heap P.globals 5 = some exn)
    (step : stepI P s ⟨divisionOpcode kind, []⟩ = .next s') :
    FnSummary (divisionZeroEntry kind) (fun start => start = c) (Running L P s') := by
  have result := native_caught (division_zero kind select native) memory outside ready returnPc returnSp
  have state : {divisionRaiseState s exn with pc := dest, env := env, extra := extra.toNat, stack := rest, trap := (divisionRaiseState s exn).trap - link.toNat} = s' :=
    division_zero_state kind accu stack field ready.frame step
  simpa only [state] using result

end OCaml.Vm.Sim
