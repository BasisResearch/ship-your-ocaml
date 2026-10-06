import OCaml.Vm.Sim.RaiseUncaughtState
import OCaml.Vm.Sim.RaiseCheck
import OCaml.Vm.Sim.RaiseUncaughtCheckSegment
import OCaml.Vm.Sim.RaiseUncaughtCheckPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- No represented trap remains in the root invocation; startup supplies the
saved equal stack cut and the interpreter-return frame. -/
structure UncaughtCheckInput (nativeSp : Nat) (saved : Nat → BitVec 64) (value : BitVec 64) (high : Nat) (c : Config) : Prop
    extends StopInvocation nativeSp saved (BitVec.ofNat 64 high) c where
  good : GoodState c.σ
  image : ExecutableImage c
  pc : pcOf c = some (0x80001ed4#64)
  tick : c.tick < 2
  boundary : RaiseStackFrame nativeSp c
  highRead : RamReadAt ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) 8
  highWord : word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) = BitVec.ofNat 64 high
  domain : gpr c 15 = some (word c Layout.sym_Caml_state)
  trap : gpr c 14 = some (BitVec.ofNat 64 high)
  value : gpr c Layout.reg_accu = some value

/-- The common check is read-only and retains the state needed by the return stores. -/
structure UncaughtChecked (before : Config) (nativeSp : Nat) (saved : Nat → BitVec 64)
    (value : BitVec 64) (high : Nat) (after : Config) : Prop where
  state : UncaughtReturnInput nativeSp saved value (BitVec.ofNat 64 high) after
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  htif : after.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes =
    before.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes

/-- The native root-invocation comparison selects the uncaught return; no branch premise is assumed. -/
theorem raise_uncaught_check {nativeSp : Nat} {saved : Nat → BitVec 64} {value : BitVec 64} {high : Nat} {c : Config}
    (h : UncaughtCheckInput nativeSp saved value high c) :
    ∃ count after, StepsN count c after ∧ UncaughtChecked c nativeSp saved value high after := by
  have savedHigh : sign_extend (m := 64) (bytesT8 c.σ.mem nativeSp) = word c nativeSp := by
    simp only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have savedSp : sign_extend (m := 64) (bytesT8 c.σ.mem (nativeSp + 8)) = word c nativeSp := by
    simpa only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] using h.boundary.equalSaved.symm
  have highValue : sign_extend (m := 64) (bytesT8 c.σ.mem ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)) = BitVec.ofNat 64 high := by
    simpa only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] using h.highWord
  have highAddress : word c Layout.sym_Caml_state + sign_extend (m := 64) (0x090#12) =
      BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat]; rfl
  have stackNext : BitVec.ofNat 64 nativeSp + 8#64 = BitVec.ofNat 64 (nativeSp + 8) := by simp [BitVec.ofNat_add]
  have bp : SegSt (0x80001ed4#64)
      [⟨Register.x2, BitVec.ofNat 64 nativeSp⟩, ⟨Register.x15, word c Layout.sym_Caml_state⟩,
       ⟨Register.x14, BitVec.ofNat 64 high⟩]
      (fun σ => Vsa.Sim.Code.CamlRaiseUncaughtCheckLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.good, h.pc, ⟨h.stack, h.domain, h.trap, trivial⟩, h.good.minstret, h.tick,
      raise_uncaught_check_loaded h.image, rfl, rfl⟩
  have native := tr_raise_uncaught_check (BitVec.ofNat 64 nativeSp) (word c Layout.sym_Caml_state)
    (BitVec.ofNat 64 high) c.σ.mem c.σ
  simp only [show sign_extend (m := 64) (0x000#12) = 0#64 from rfl,
    show sign_extend (m := 64) (0x008#12) = 8#64 from rfl, BitVec.add_zero,
    stackNext, h.boundary.highRead.toNat, h.boundary.spRead.toNat, highAddress, h.highRead.toNat] at native
  have guard : zopz0zI_u (BitVec.ofNat 64 high)
      (BitVec.ofNat 64 high - (word c nativeSp - word c nativeSp)) = false := by
    simp only [BitVec.sub_self, BitVec.sub_zero, native_ult, BitVec.ule_eq_not_ult, Bool.not_not, BitVec.ult, Nat.lt_irrefl, decide_false]
  obtain ⟨count, after, _, run, post⟩ := native h.boundary.highRead.lower h.boundary.highRead.upper h.boundary.highRead.htif
    (word c nativeSp) savedHigh.symm h.boundary.spRead.lower h.boundary.spRead.upper h.boundary.spRead.htif
    (word c nativeSp) savedSp.symm h.highRead.lower h.highRead.upper h.highRead.htif (BitVec.ofNat 64 high) highValue.symm guard c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  refine ⟨count, after, run, ?_, memory, frame.out, frame.frame _ (by decide)⟩
  refine {
    toStopInvocation := h.toStopInvocation.frame_read memory (frame.frame _ (by decide))
    good := post.good
    image := image_of_writeLog (log := []) h.image ⟨trivial, trivial⟩ memory
    pc := post.pcAt
    tick := post.tick
    domain := ?_
    vmStack := ?_
    value := (frame.frame _ (by decide)).trans h.value }
  · have domain : gpr after 15 = some (word c Layout.sym_Caml_state) := (frame.frame _ (by decide)).trans h.domain
    simpa only [word, memory] using domain
  · have observed : gpr after 13 = some (BitVec.ofNat 64 high - (word c nativeSp - word c nativeSp)) := PinsHold.get post.pins ⟨0, by simp⟩
    simpa only [BitVec.sub_self, BitVec.sub_zero] using observed

end OCaml.Vm.Sim
