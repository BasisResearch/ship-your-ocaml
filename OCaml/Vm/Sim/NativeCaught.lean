import OCaml.Vm.Sim.NativeReentry
import OCaml.Vm.Sim.ReentryHandler

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- A checked native raising summary reaches the represented caught handler.
The readiness predicate is on the explicit write-log memory view, independent of execution. -/
theorem native_caught {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {nativeSp sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val}
    {entry : BitVec 64} {log : List WEntry} {saved : Nat → BitVec 64} {c : Config}
    (summary : FnSummary entry (fun start => start = c) (NativeRaisePost log saved c))
    (memory : ReentryMemory nativeSp c)
    (outside : ∀ a ∈ reentryControlWords c, OutLRange log a 8)
    (ready : CaughtReentryReady L P s pl cp nativeSp sp high dest link extra env rest (nativeMemoryView c log))
    (returnPc : saved 1 = 0x80001e80#64) (returnSp : saved 2 = BitVec.ofNat 64 nativeSp) :
    FnSummary entry (fun start => start = c) (Running L P
      {s with pc := dest, env := env, extra := extra.toNat, stack := rest, trap := s.trap - link.toNat}) := by
  constructor
  intro start initial
  obtain ⟨pc, eq⟩ := initial
  subst start
  obtain ⟨middle, nativeRun, post⟩ := (native_reentry summary memory outside returnPc returnSp).run c ⟨pc, rfl⟩
  obtain ⟨count, after, run, represented⟩ := reentry_handler ready post
  exact ⟨after, nativeRun.trans run.toSteps, represented⟩

end OCaml.Vm.Sim
