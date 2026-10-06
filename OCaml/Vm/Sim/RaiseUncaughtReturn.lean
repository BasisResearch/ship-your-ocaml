import OCaml.Vm.Sim.RaiseUncaughtState
import OCaml.Vm.Sim.RaiseUncaughtReturnSegment
import OCaml.Vm.Sim.RaiseUncaughtReturnPins
import OCaml.Vm.Sim.InterpReturn

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- Execute the uncaught stores, tag the result and restore the complete native ABI frame. -/
theorem raise_uncaught_return {nativeSp : Nat} {saved : Nat → BitVec 64} {value vmSp : BitVec 64} {c : Config}
    (h : UncaughtReturnInput nativeSp saved value vmSp c) :
    ∃ count after, StepsN count c after ∧ UncaughtReturnPost c nativeSp saved value vmSp after := by
  obtain ⟨m1, m1Eq⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 c.σ.mem ((word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp) (sdData_val vmSp) := ⟨_, rfl⟩
  obtain ⟨m2, m2Eq⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 m1 ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise) (sdData_val (word c (nativeSp + 24))) := ⟨_, rfl⟩
  obtain ⟨m3, m3Eq⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap4 m2 Layout.sym_caml_callback_depth (swData (stopDepth c)) := ⟨_, rfl⟩
  have memoryLog : m3 = writeLog c.σ.mem (uncaughtLog nativeSp vmSp c) := by
    rw [m3Eq, m2Eq, m1Eq]; rfl
  have savedRead : word c (nativeSp + 24) = sign_extend (m := 64) (bytesT8 c.σ.mem (nativeSp + 24)) := by
    simp only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have fieldAddress (offset : Nat) : word c Layout.sym_Caml_state + BitVec.ofNat 64 offset =
      BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + offset) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have bp : SegSt (0x800035f0#64) [⟨Register.x2, BitVec.ofNat 64 nativeSp⟩,
      ⟨Register.x15, word c Layout.sym_Caml_state⟩, ⟨Register.x13, vmSp⟩, ⟨Register.x21, value⟩]
      (fun σ => Vsa.Sim.Code.CamlRaiseUncaughtReturnLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.good, h.pc, ⟨h.stack, h.domain, h.vmStack, h.value, trivial⟩, h.good.minstret, h.tick,
      raise_uncaught_return_loaded h.image, rfl, rfl⟩
  have native := tr_raise_uncaught_return (BitVec.ofNat 64 nativeSp) (word c Layout.sym_Caml_state) vmSp value c.σ.mem c.σ
  simp only [show ((0x800035f0#64) + sign_extend (m := 64) ((0x00061#20) +++ 0x000#12)) + sign_extend (m := 64) (0x648#12) = BitVec.ofNat 64 Layout.sym_caml_callback_depth from by decide,
    show ((0x8000360c#64) + sign_extend (m := 64) ((0x00061#20) +++ 0x000#12)) + sign_extend (m := 64) (0x62c#12) = BitVec.ofNat 64 Layout.sym_caml_callback_depth from by decide,
    show sign_extend (m := 64) (0x018#12) = BitVec.ofNat 64 24 from rfl,
    show sign_extend (m := 64) (0x0a0#12) = BitVec.ofNat 64 Layout.off_extern_sp from rfl,
    show sign_extend (m := 64) (0x0b8#12) = BitVec.ofNat 64 Layout.off_external_raise from rfl,
    fieldAddress, ← BitVec.ofNat_add, h.depthWrite.read.toNat, h.savedRaiseRead.toNat,
    h.stackWrite.read.toNat, h.raiseWrite.read.toNat] at native
  obtain ⟨count, middle, _, run, post⟩ := native
    h.depthWrite.read.lower h.depthWrite.read.upper h.depthWrite.read.htif _ rfl
    h.savedRaiseRead.lower h.savedRaiseRead.upper h.savedRaiseRead.htif (word c (nativeSp + 24)) savedRead
    h.stackWrite.lower h.stackWrite.upper h.stackWrite.htif h.stackWrite.aligned
    (image_entry_code (w := vmSp) h.imageOutside (by simp [stopLog]) (by decide) (by decide)) m1 m1Eq
    h.raiseWrite.lower h.raiseWrite.upper h.raiseWrite.htif h.raiseWrite.aligned
    (image_entry_code (w := word c (nativeSp + 24)) h.imageOutside (by simp [stopLog]) (by decide) (by decide)) m2 m2Eq
    h.depthWrite.lower h.depthWrite.upper h.depthWrite.htif h.depthWrite.aligned (by decide) m3 m3Eq c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have writes := memory.trans memoryLog
  have imageOutside : ImageOutside (uncaughtLog nativeSp vmSp c) :=
    ⟨uncaught_outside h.imageOutside.text, uncaught_outside h.imageOutside.rodata⟩
  have input : InterpReturnInput nativeSp saved (value ||| 2#64) middle :=
    ⟨post.good, image_of_writeLog h.image imageOutside writes, post.pcAt, post.tick,
      h.frame.frame (fun r hr => uncaught_outside (h.frameOutside r hr)) writes,
      PinsHold.get post.pins ⟨4, by simp⟩, PinsHold.get post.pins ⟨2, by simp⟩, h.aligned⟩
  obtain ⟨returnCount, after, returnRun, returned⟩ := interp_return input
  exact ⟨count + returnCount, after, run.append returnRun, returned.good, returned.image,
    returned.tick, returned.pc, returned.stack, returned.value, returned.registers,
    returned.memory.trans writes, returned.frame.out.trans frame.out,
    (returned.frame.frame LeanRV64DExecutable.Register.htif_payload_writes (by decide)).trans
      (frame.frame LeanRV64DExecutable.Register.htif_payload_writes (by decide))⟩

end OCaml.Vm.Sim
