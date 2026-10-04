import OCaml.Vm.Boot.Startup.StartupAux
import OCaml.Vm.Boot.Startup.RuntimeReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

theorem startupAuxSave_inside {sp ra} (frame : NativeFrame sp 16) :
    LogInW [⟨nativeFrameBase sp 16, sp.toNat⟩] (startupAuxSave sp ra) := by
  apply frame.word_log_inside
  intro off value member
  have eq := List.mem_singleton.mp member
  cases eq
  decide

/-- The only non-stack write is the four-byte startup count. -/
theorem startupAux_byte {sp ra} (frame : NativeFrame sp 16) (mem : Vsa.MemRepr.Mem)
    (a : Nat) (below : a < heapEnd) (outside : a < Layout.sym_startup_count ∨ Layout.sym_startup_count + 4 ≤ a) :
    (writeLog mem (startupAuxLog sp ra))[a]? = mem[a]? := by
  rw [startupAuxLog, writeLog_append, writeLog_out _ _ _ (show OutL [(Layout.sym_startup_count, 4, 1#64)] a from ⟨outside, trivial⟩)]
  apply frameOn_writeLog _ _ _ (startupAuxSave_inside frame)
  have lower := frame.lower
  exact ⟨Or.inl (by change a < nativeFrameBase sp 16; unfold nativeFrameBase; omega), trivial⟩

/-- Allocator pins lie before the mutable startup count. -/
theorem AllocatorByteSource.before_startup_count {pin} (source : AllocatorByteSource pin) :
    pin.1 < Layout.sym_startup_count := by
  have geometry : Image.textBase + Image.textSize ≤ Layout.sym_startup_count ∧
      allocatorImpureAddr + 8 ≤ Layout.sym_startup_count := by decide
  unfold AllocatorByteSource at source
  split at source <;> omega

theorem startup_count_outside_allocator {H a} (owned : vsaFoot H a) :
    a < Layout.sym_startup_count ∨ Layout.sym_startup_count + 4 ≤ a := by
  unfold vsaFoot allocGlobal InRange at owned
  unfold Layout.sym_startup_count heapStart at *
  omega
end OCaml.Vm.Boot.Startup
