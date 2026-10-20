import OCaml.Vm.Boot.Startup.GcMessageQuiet
import OCaml.Vm.Boot.Startup.SearchTableReset
import OCaml.Vm.Boot.Startup.RuntimeStack
import OCaml.Vm.Boot.Startup.GprsSame

/-! `caml_gc_message` at verbosity zero under readiness: the arguments it
spills are whatever the registers hold, the spill stays below `sp`, and it
returns. One lemma for every quiet message site. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- A quiet `caml_gc_message` returned. -/
structure GcQuiet (H : List (Nat × Nat)) (capacity : Nat) (sp ra : BitVec 64) (before after : Config) : Prop where
  pc : PCAt ra after
  ready : RuntimeReady H capacity sp ra after
  regs : GHolds after.σ [(2, sp), (1, ra), (10, 0#64), (6, 0#64)]
  memory : after.σ.mem = writeLog before.σ.mem (gcMessageLog sp ra (vsaReg before 12) (vsaReg before 13)
    (vsaReg before 14) (vsaReg before 15) (vsaReg before 16) (vsaReg before 17))
  same : GprsSame before after [6, 2, 10, 1]

theorem ready_gc_message (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (sp ra v : BitVec 64)
    (pc : PCAt 0x80003cb0#64 c) (ready : RuntimeReady H capacity sp ra c) (frame : NativeFrame sp 80)
    (a0 : gprGet c.σ 10 = some v) (quiet : LPins8 c.σ.mem Layout.sym_caml_verb_gc (List.replicate 8 0#8)) :
    ∃ after, Steps c after ∧ GcQuiet H capacity sp ra c after := by
  obtain ⟨after, run, gc⟩ := (gc_message_quiet c sp ra (vsaReg c 12) (vsaReg c 13) (vsaReg c 14) (vsaReg c 15)
    (vsaReg c 16) (vsaReg c 17) v ready.toLeafInput frame
    ⟨ready.stack, ready.raReg, OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready ready 12 (by decide) (by decide), OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready ready 13 (by decide) (by decide),
      OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready ready 14 (by decide) (by decide), OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready ready 15 (by decide) (by decide),
      OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready ready 16 (by decide) (by decide), OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready ready 17 (by decide) (by decide), a0, trivial⟩
    quiet).run c ⟨pc, rfl⟩
  exact ⟨after, run, {
    pc := gc.pc
    ready := ready.stack_log gc (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ gc.regs rfl) (gholds_lookup (n := 1) _ gc.regs rfl) ready.aligned frame
      (gcMessageLog_inside frame)
    regs := gc.regs
    memory := gc.memory
    same := GprsSame.of_post gc (by decide) }⟩

end OCaml.Vm.Boot.Startup
