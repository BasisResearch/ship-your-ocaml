import OCaml.Vm.Boot.Startup.FindStart
import OCaml.Vm.Boot.Startup.NameFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- C-string representation supplies the first-byte load and both name tests,
including preservation through the s4 save. -/
theorem findStart_of_name {sp name s4 value env ra cs c} (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ (findStartInput sp name s4 value))
    (data : EnvName name cs c) (positive : 0 < cs.length)
    (below : name.toNat + cs.length + 1 ≤ nativeFrameBase sp 80)
    (environment : bytesT c.σ.mem Layout.sym_environ 8 = env) (nonnull : env ≠ 0#64) :
    ∃ b, FindStartInput sp name s4 value env ra b c := by
  obtain ⟨b, byte⟩ := data.byte (k := 0) (Nat.zero_le _)
  refine ⟨b, {
    toLeafInput := leaf
    regs := regs
    frame := frame
    environment := environment
    envNonzero := nonnull
    window := ?_
    pin := ?_
    nonzero := fun eq => by have := byte.zero.mp eq; omega
    notEquals := byte.notEquals }⟩
  · have window := name_window data.region (k := 0) (Nat.zero_le _)
    change ReadWindow (name + 0#64) 1 at window
    simpa only [BitVec.add_zero] using window
  · have same := frameOn_writeLog _ c.σ.mem _ (findStart_log_inside (s4 := s4) frame) name.toNat
      (show OutW [⟨nativeFrameBase sp 80, sp.toNat⟩] name.toNat from
        ⟨Or.inl (by change name.toNat < nativeFrameBase sp 80; omega), trivial⟩)
    rw [same]
    simpa only [Nat.add_zero] using byte.pin
end OCaml.Vm.Boot.Startup
