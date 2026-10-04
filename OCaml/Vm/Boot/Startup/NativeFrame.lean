import OCaml.Vm.Primitives.Effects
import OCaml.Vm.Primitives.Write
import Vsa.Sim.DlHeap
import OCaml.Vm.Sim.LogWindow
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives

/-- An aligned C frame lies above the allocator arena and below stack_top. -/
structure NativeFrame (sp : BitVec 64) (size : Nat) : Prop where
  lower : heapEnd + size ≤ sp.toNat
  upper : sp.toNat ≤ Layout.sym_stack_top
  aligned : sp.toNat % 16 = 0
  sizeAligned : size % 16 = 0

def nativeFrameBase (sp : BitVec 64) (size : Nat) : Nat := sp.toNat - size

theorem NativeFrame.address {sp size} (h : NativeFrame sp size) (off : Nat) (bound : off ≤ size) :
    sp + (-BitVec.ofNat 64 size) + BitVec.ofNat 64 off = BitVec.ofNat 64 (nativeFrameBase sp size + off) := by
  rw [← BitVec.sub_eq_add_neg]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, nativeFrameBase]
  have lower := h.lower
  have upper := h.upper
  unfold heapEnd Layout.sym_stack_top at *
  omega

theorem NativeFrame.slot_nat {sp size} (h : NativeFrame sp size) {off : Nat} (bound : off ≤ size) :
    (BitVec.ofNat 64 (nativeFrameBase sp size + off)).toNat = nativeFrameBase sp size + off := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have upper := h.upper
  have lower := h.lower
  unfold nativeFrameBase Layout.sym_stack_top at *
  omega

theorem NativeFrame.word {sp size} (h : NativeFrame sp size) {off : Nat}
    (bound : off + 8 ≤ size) (aligned : off % 8 = 0) :
    WriteWindow (BitVec.ofNat 64 (nativeFrameBase sp size + off)) 8 := by
  have addr := h.slot_nat (by omega : off ≤ size)
  have lower := h.lower
  have upper := h.upper
  have spAlign := h.aligned
  have sizeAlign := h.sizeAligned
  constructor <;> rw [addr]
  all_goals simp only [nativeFrameBase, heapEnd, Layout.sym_stack_top, Layout.sym_tohost] at *
  all_goals omega

theorem NativeFrame.image_outside {sp size log} (h : NativeFrame sp size)
    (inside : LogInW [⟨nativeFrameBase sp size, sp.toNat⟩] log) : ImageOutside log := by
  have lower := h.lower
  have text : Image.textBase + Image.textSize ≤ heapEnd := by decide
  have rodata : Image.rodataBase + Image.rodataSize ≤ heapEnd := by decide
  constructor
  all_goals apply OCaml.Vm.Sim.outLRange_of_windows inside
  all_goals change (_ ≤ nativeFrameBase sp size ∨ sp.toNat ≤ _) ∧ True
  all_goals exact ⟨Or.inl (by unfold nativeFrameBase; omega), trivial⟩
end OCaml.Vm.Boot.Startup
