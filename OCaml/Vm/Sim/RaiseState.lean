import OCaml.Vm.Sim.RaiseRestore

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Represented data shared by the quiet entry, caught check and handler body.
The handler restores environment/extra from its trap frame, so their old
register values are not required at these internal cuts. -/
structure RaiseContext (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (sp high dest : Nat) (link : BitVec 63) (env : Val) (extra : BitVec 63) (rest : List Val) (c : Config) : Prop where
  data : VmPayload P s c pl cp sp high
  bindings : PrimitiveBindings P c
  platform : PlatformOk L.runtimeOk c
  frame : RaiseFrame s dest link env extra rest
  accu : ∃ w, gpr c Layout.reg_accu = some w ∧ valWord pl s.accu = some w
  tick : c.tick < 2

/-- Native exception cuts retain the domain and current trap pointer. -/
structure RaiseAt (entry : BitVec 64) (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (sp high dest : Nat) (link : BitVec 63) (env : Val) (extra : BitVec 63) (rest : List Val) (c : Config) : Prop
    extends RaiseContext L P s pl cp sp high dest link env extra rest c where
  pc : pcOf c = some entry
  trapReg : gpr c 14 = some (BitVec.ofNat 64 (high - 8 * s.trap))
  domainReg : gpr c 15 = some (word c Layout.sym_Caml_state)

/-- A read-only exception prefix also retains the saved native-stack frame. -/
structure RaiseReadPost (entry : BitVec 64) (before : Config) (L : OCaml.Layout) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high dest : Nat) (link : BitVec 63) (env : Val)
    (extra : BitVec 63) (rest : List Val) (after : Config) : Prop where
  state : RaiseAt entry L P s pl cp sp high dest link env extra rest after
  memory : after.σ.mem = before.σ.mem
  nativeStack : gpr after 2 = gpr before 2

abbrev RaiseHandlerInput := RaiseAt (0x80001ef0#64)
abbrev RaiseCheckInput := RaiseAt (0x80001ed4#64)

/-- All memory data and the exception value survive a read-only native prefix. -/
theorem RaiseContext.after_read {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val} {c after : Config}
    (h : RaiseContext L P s pl cp sp high dest link env extra rest c)
    (stable : MemoryStable L.runtimeOk) (good : GoodState after.σ) (tick : after.tick < 2)
    (memory : after.σ.mem = c.σ.mem) (out : after.σ.sailOutput = c.σ.sailOutput)
    (accu : gpr after Layout.reg_accu = gpr c Layout.reg_accu) :
    RaiseContext L P s pl cp sp high dest link env extra rest after := by
  refine ⟨h.data.frame memory out, h.bindings.frame memory,
    ⟨good, image_of_writeLog (log := []) h.platform.image ⟨trivial, trivial⟩ memory,
      stable c after memory h.platform.runtime⟩, h.frame, ?_, tick⟩
  obtain ⟨w, reg, value⟩ := h.accu
  exact ⟨w, accu.trans reg, value⟩

/-- An active represented trap is strictly below the full stack-high boundary. -/
theorem RaiseContext.caught_guard {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val} {c : Config}
    (h : RaiseContext L P s pl cp sp high dest link env extra rest c) :
    (BitVec.ofNat 64 (high - 8 * s.trap)).ult (BitVec.ofNat 64 high) = true := by
  have highBound : high < 2^64 := by
    rw [← h.data.stackHigh]
    exact (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).isLt
  have shape := h.data.stack.1
  have active := h.frame.active
  have bound := h.frame.bound
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

end OCaml.Vm.Sim
