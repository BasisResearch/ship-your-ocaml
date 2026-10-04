import OCaml.Vm.Boot.Startup.CustomRegistered
import OCaml.Vm.Boot.Startup.CustomPrefix
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives

structure CustomFirstRegistered (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra s0 head : BitVec 64) (before after : Config) where
  saved : Config
  called : Config
  setup : WriteRegistersPost [2, 10] (customSaveLog sp ra s0) before jal_80024a3c_call.pc 16#64
    (customSaveRegs sp ra s0) saved
  call : RegistersPost [1] saved.σ.mem saved jal_80024a3c_call.target 16#64
    [(1, jal_80024a3c_call.link), (10, 16#64), (2, nativeStack sp 16), (8, s0)] called
  registration : CustomRegistered H capacity .int32 (nativeStack sp 16) s0 head called after

/-- The initializer's prologue and first actual checked call create the int32 node. -/
theorem custom_first (c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra s0 head : BitVec 64) (ready : RuntimeReady H (capacity + 32) sp ra c)
    (frame : NativeFrame sp 560) (saved0 : gprGet c.σ 8 = some s0)
    (headWord : bytesT c.σ.mem Layout.sym_custom_ops_table 8 = head) :
    FnSummary 0x80024a2c#64 (fun d => d = c)
      (fun after => Nonempty (CustomFirstRegistered H capacity sp ra s0 head c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have short := frame.resize (small := 16) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  obtain ⟨saved, run1, setup⟩ := (custom_save c sp ra s0 ready.toLeafInput short
    ⟨ready.stack, ready.raReg, saved0, trivial⟩).run c ⟨pc, rfl⟩
  have savedReady := ready.stack_log setup (by decide)
    (by simp only [customSaveRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ setup.regs (by rfl))
    (gholds_lookup (n := 1) _ setup.regs (by rfl)) ready.aligned short (customSaveLog_inside short)
  have args : GHolds saved.σ [(10, 16#64), (2, nativeStack sp 16), (8, s0)] :=
    holds_project setup.regs (by simp [customSaveRegs, lookupG])
  obtain ⟨called, run2, call⟩ := (call_registers_summary jal_80024a3c_call_shape jal_80024a3c_call_decode saved
    (jal_80024a3c_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ args
    (by change KeysOK [10, 2, 8]; decide) (by simp only [KeysAvoidRa, keysG]; decide) (by rfl)).run saved ⟨setup.pc, rfl⟩
  have calledReady := savedReady.effect call (by decide)
    (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ call.regs (by rfl))
    (gholds_lookup (n := 1) _ call.regs (by rfl)) (by decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have preserved : bytesT called.σ.mem Layout.sym_custom_ops_table 8 = head := by
    rw [call.memory, setup.memory, bytesT_writeLog_out _ (show OutLRange (customSaveLog sp ra s0) Layout.sym_custom_ops_table 8 from ?_)]
    · exact headWord
    · apply OCaml.Vm.Sim.outLRange_of_windows (customSaveLog_inside short)
      have lower := short.lower
      have bound : Layout.sym_custom_ops_table + 8 ≤ heapEnd := by decide
      exact ⟨Or.inl (by change _ ≤ nativeFrameBase sp 16; unfold nativeFrameBase; omega), trivial⟩
  obtain ⟨after, run3, ⟨registered⟩⟩ := (custom_allocate_publish called H capacity .int32 _ s0 head
    calledReady nested (gholds_lookup (n := 8) _ call.regs (by rfl)) (fun h => False.elim (h rfl))
    call.result preserved).run called ⟨call.pc, rfl⟩
  exact ⟨after, run1.trans (run2.trans run3), ⟨saved, called, setup, call, registered⟩⟩
end OCaml.Vm.Boot.Startup
