import OCaml.Vm.Gc.AllocEntryAccess

namespace OCaml.Vm.Gc.AllocEntry
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The free-list ABI pins preserved by the linking jump, excluding old RA. -/
def callRegs (R : Nat → BitVec 64) (target : BitVec 64) : GRegs :=
  [(8,R 10),(15,target),(9,BitVec.ofNat 64 Layout.sym_caml_fl_p_allocate),
   (2,frameSp R),(10,R 10),(11,R 11)]

theorem call_registers {R target} {c : Config} (holds : GHolds c.σ (atCall R target)) :
    GHolds c.σ (callRegs R target) := by
  exact ⟨gholds_lookup _ holds rfl, gholds_lookup _ holds rfl,
    gholds_lookup _ holds rfl, gholds_lookup _ holds rfl,
    gholds_lookup _ holds rfl, gholds_lookup _ holds rfl, True.intro⟩

/-- Execute the decoded free-list JALR using the pointer actually loaded
by the allocator. Alignment identifies the bit-cleared target with that pointer. -/
theorem call_free_list {R target c}
    (good : GoodState c.σ) (tick : c.tick < 2)
    (minstret : ∃ v, c.σ.regs.get? Register.minstret = some v)
    (code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem)
    (holds : GHolds c.σ (atCall R target)) (aligned : target.toNat % 4 = 0) :
    FnSummary callPc (fun d => d = c)
      (SegCallFacts [] (callRegs R target) [] target returnPc c) := by
  have summary := indirect_summary call_shape call_decode c (call_pins code) good tick minstret
    (callRegs R target) (call_registers holds)
    (by change KeysOK [8,15,9,2,10,11]; decide)
    (by change ∀ n ∈ [8,15,9,2,10,11], n ≠ 1; decide)
    target rfl (by rw [call_target target aligned]; exact aligned)
  rw [call_target target aligned, call_link] at summary
  exact summary

end OCaml.Vm.Gc.AllocEntry
