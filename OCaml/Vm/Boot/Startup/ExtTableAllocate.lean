import OCaml.Vm.Boot.Startup.ExtTableReady
import OCaml.Vm.Boot.Startup.CallerFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim VsaIris.Inst OCaml.Vm.Primitives

def extTableCallRegs (sp : BitVec 64) : GRegs :=
  [(1, jal_80003dd4_call.link), (10, 64#64), (8, sharedTableAddress), (2, nativeStack sp 16), (11, 8#64)]

structure ExtTableAllocated (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 : BitVec 64)
    (before after : Config) where
  saved : Config
  called : Config
  setup : WriteRegistersPost [2, 8, 10] (extTableLog sp ra s0) before jal_80003dd4_call.pc 64#64
    (extTableRegs sp ra) saved
  call : RegistersPost [1] saved.σ.mem saved jal_80003dd4_call.target 64#64
    (extTableCallRegs sp) called
  allocation : StatCheckedReturned H capacity (nativeStack sp 16) jal_80003dd4_call.link sharedTableAddress 64#64 called after

/-- Initialize the eight-slot table and complete its real checked allocation. -/
theorem ext_table_allocate (c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra s0 : BitVec 64) (ready : RuntimeReady H (capacity + 64) sp ra c)
    (frame : NativeFrame sp 560) (saved0 : gprGet c.σ 8 = some s0)
    (table : gprGet c.σ 10 = some sharedTableAddress) (count : gprGet c.σ 11 = some 8#64) :
    FnSummary 0x80003db8#64 (fun d => d = c)
      (fun after => Nonempty (ExtTableAllocated H capacity sp ra s0 c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have short := frame.resize (small := 16) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  obtain ⟨saved, run1, setup⟩ := (ext_table_prefix c sp ra s0 ready.toLeafInput short
    ⟨ready.stack, saved0, ready.raReg, table, count, trivial⟩).run c ⟨pc, rfl⟩
  have savedReady := ext_table_prefix_ready ready short setup
  have args : GHolds saved.σ [(10, 64#64), (8, sharedTableAddress), (2, nativeStack sp 16), (11, 8#64)] :=
    holds_project setup.regs (by simp [extTableRegs, lookupG])
  obtain ⟨called, run2, call⟩ := (call_registers_summary jal_80003dd4_call_shape jal_80003dd4_call_decode saved
    (jal_80003dd4_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ args
    (by change KeysOK [10, 8, 2, 11]; decide) (by simp only [KeysAvoidRa, keysG]; decide) (by rfl)).run saved ⟨setup.pc, rfl⟩
  have calledReady := savedReady.effect call (by decide)
    (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ call.regs (by rfl))
    (gholds_lookup (n := 1) _ call.regs (by rfl)) (by decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  obtain ⟨after, run3, ⟨allocated⟩⟩ := (stat_checked called H capacity 64 _ jal_80003dd4_call.link sharedTableAddress 64#64
    calledReady nested (gholds_lookup (n := 8) _ call.regs (by rfl)) call.result
    (by constructor <;> decide)).run called ⟨call.pc, rfl⟩
  exact ⟨after, run1.trans (run2.trans run3), ⟨saved, called, setup, call, allocated⟩⟩
end OCaml.Vm.Boot.Startup
