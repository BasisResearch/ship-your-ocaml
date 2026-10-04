import OCaml.Vm.Boot.Startup.NativeRead
import OCaml.Vm.Gc.Readback
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The symbolic word stores emitted by a native frame's saving prologue. -/
def nativeWordLog (sp : BitVec 64) (size : Nat) (slots : List (Nat × BitVec 64)) : List WEntry :=
  slots.map fun (off, value) => ((nativeStack sp size + BitVec.ofNat 64 off).toNat, 8, value)

theorem NativeFrame.word_log_slots {sp size slots} (frame : NativeFrame sp size)
    (bounds : ∀ off value, (off, value) ∈ slots → off + 8 ≤ size) :
    nativeWordLog sp size slots = slots.map (fun (off, value) => (nativeFrameBase sp size + off, 8, value)) := by
  apply List.map_congr_left
  rintro ⟨off, value⟩ member
  have bound := bounds off value member
  change ((nativeStack sp size + BitVec.ofNat 64 off).toNat, 8, value) = _
  rw [nativeStack, frame.address off (by omega), frame.slot_nat (off := off) (by omega)]

theorem NativeFrame.word_log_inside {sp size slots} (frame : NativeFrame sp size)
    (bounds : ∀ off value, (off, value) ∈ slots → off + 8 ≤ size) :
    LogInW [⟨nativeFrameBase sp size, sp.toNat⟩] (nativeWordLog sp size slots) := by
  rw [frame.word_log_slots bounds]
  induction slots with
  | nil => trivial
  | cons slot rest ih =>
    obtain ⟨off, value⟩ := slot
    have bound := bounds off value (by simp)
    have lower := frame.lower
    refine ⟨Or.inl ⟨by change nativeFrameBase sp size ≤ nativeFrameBase sp size + off; omega, ?_⟩, ih (fun i v hm => bounds i v (by simp [hm]))⟩
    change nativeFrameBase sp size + off + 8 ≤ sp.toNat
    unfold nativeFrameBase
    omega

/-- Read any separated word from a native saving prologue's exact store log. -/
theorem NativeFrame.word_log_read {sp size slots} (frame : NativeFrame sp size)
    (bounds : ∀ off value, (off, value) ∈ slots → off + 8 ≤ size)
    (separate : slots.Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1))
    (mem : Std.ExtHashMap Nat (BitVec 8)) {off value} (member : (off, value) ∈ slots) :
    bytesT (writeLog mem (nativeWordLog sp size slots)) (nativeFrameBase sp size + off) 8 = value := by
  rw [frame.word_log_slots bounds]
  let cells := slots.map (fun (off, value) => (nativeFrameBase sp size + off, value))
  have separated : cells.Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1) := by
    apply List.pairwise_map.mpr
    apply separate.imp
    intro x y h
    change nativeFrameBase sp size + x.1 + 8 ≤ nativeFrameBase sp size + y.1 ∨
      nativeFrameBase sp size + y.1 + 8 ≤ nativeFrameBase sp size + x.1
    omega
  have read := OCaml.Vm.Gc.word_writeLog_cells mem cells separated
    (List.mem_map.mpr ⟨(off, value), member, rfl⟩)
  simpa only [cells, List.map_map, Function.comp_def] using read
end OCaml.Vm.Boot.Startup
