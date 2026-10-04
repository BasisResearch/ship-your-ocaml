import OCaml.Vm.Sim.StopState
import OCaml.Vm.Sim.StopPrefixSegment
import OCaml.Vm.Sim.StopPrefixPins
import OCaml.Vm.Sim.InterpReturn

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- Execute STOP and the shared interpreter epilogue, including all three runtime stores. -/
theorem stop_return {nativeSp : Nat} {saved : Nat → BitVec 64} {value vmSp : BitVec 64} {c : Config}
    (h : StopInput nativeSp saved value vmSp c) :
    ∃ count after, StepsN count c after ∧ StopReturnPost c nativeSp saved value vmSp after := by
  obtain ⟨m1, m1Eq⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeLog c.σ.mem [(Layout.sym_caml_callback_depth, 4, stopDepth c)] := ⟨_, rfl⟩
  obtain ⟨m2, m2Eq⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 m1 ((word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp) (sdData_val vmSp) := ⟨_, rfl⟩
  obtain ⟨m3, m3Eq⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 m2 ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise) (sdData_val (word c (nativeSp + 24))) := ⟨_, rfl⟩
  have memoryLog : m3 = writeLog c.σ.mem (stopLog nativeSp vmSp c) := by
    rw [m3Eq, m2Eq, m1Eq]; rfl
  have savedRead : sign_extend (m := 64) (bytesT8 m1 (nativeSp + 24)) = word c (nativeSp + 24) := by
    rw [m1Eq]
    have same := bytesT_writeLog_out c.σ.mem h.savedRaiseOutside
    simpa only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] using same
  have domainRead : word c Layout.sym_Caml_state = sign_extend (m := 64) (bytesT8 c.σ.mem Layout.sym_Caml_state) := by
    simp only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have fieldAddress (offset : Nat) : word c Layout.sym_Caml_state + BitVec.ofNat 64 offset =
      BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + offset) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have bp : SegSt (0x800032f4#64) [⟨Register.x2, BitVec.ofNat 64 nativeSp⟩, ⟨Register.x9, vmSp⟩]
      (fun σ => Vsa.Sim.Code.CamlStopPrefixLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.good, h.pc, ⟨h.stack, h.vmStack, trivial⟩, h.good.minstret, h.tick, stop_prefix_loaded h.image, rfl, rfl⟩
  have native := tr_stop_prefix (BitVec.ofNat 64 nativeSp) vmSp c.σ.mem c.σ
  simp only [show ((0x800032f4#64) + sign_extend (m := 64) ((0x00062#20) +++ 0x000#12)) + sign_extend (m := 64) (0x944#12) = BitVec.ofNat 64 Layout.sym_caml_callback_depth from by decide,
    show ((0x800032fc#64) + sign_extend (m := 64) ((0x00062#20) +++ 0x000#12)) + sign_extend (m := 64) (0xa0c#12) = BitVec.ofNat 64 Layout.sym_Caml_state from by decide,
    show ((0x80003308#64) + sign_extend (m := 64) ((0x00062#20) +++ 0x000#12)) + sign_extend (m := 64) (0x930#12) = BitVec.ofNat 64 Layout.sym_caml_callback_depth from by decide,
    h.depthWrite.read.toNat, h.domainRead.toNat] at native
  have native := native h.depthWrite.read.lower h.depthWrite.read.upper h.depthWrite.read.htif _ rfl
    h.domainRead.lower h.domainRead.upper h.domainRead.htif (word c Layout.sym_Caml_state) domainRead
  simp only [show sign_extend (m := 64) (0x018#12) = BitVec.ofNat 64 24 from rfl,
    show sign_extend (m := 64) (0x0a0#12) = BitVec.ofNat 64 Layout.off_extern_sp from rfl,
    show sign_extend (m := 64) (0x0b8#12) = BitVec.ofNat 64 Layout.off_external_raise from rfl,
    fieldAddress, ← BitVec.ofNat_add, h.savedRaiseRead.toNat, h.stackWrite.read.toNat, h.raiseWrite.read.toNat] at native
  obtain ⟨count, middle, _, run, post⟩ := native
    h.depthWrite.lower h.depthWrite.upper h.depthWrite.htif h.depthWrite.aligned (by decide) m1 m1Eq
    h.savedRaiseRead.lower h.savedRaiseRead.upper h.savedRaiseRead.htif (word c (nativeSp + 24)) savedRead.symm
    h.stackWrite.lower h.stackWrite.upper h.stackWrite.htif h.stackWrite.aligned
    (image_entry_code (w := vmSp) h.imageOutside (by simp [stopLog]) (by decide) (by decide)) m2 m2Eq
    h.raiseWrite.lower h.raiseWrite.upper h.raiseWrite.htif h.raiseWrite.aligned
    (image_entry_code (w := word c (nativeSp + 24)) h.imageOutside (by simp [stopLog]) (by decide) (by decide)) m3 m3Eq c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have writes := memory.trans memoryLog
  have input : InterpReturnInput nativeSp saved value middle :=
    ⟨post.good, image_of_writeLog h.image h.imageOutside writes, post.pcAt, post.tick,
      h.frame.frame h.frameOutside writes, PinsHold.get post.pins ⟨3, by simp⟩,
      (frame.frame _ (by decide)).trans h.value, h.aligned⟩
  obtain ⟨returnCount, after, returnRun, returned⟩ := interp_return input
  exact ⟨count + returnCount, after, run.append returnRun, returned.good, returned.image,
    returned.tick, returned.pc, returned.stack, returned.value, returned.registers,
    returned.memory.trans writes, returned.frame.out.trans frame.out⟩

end OCaml.Vm.Sim
