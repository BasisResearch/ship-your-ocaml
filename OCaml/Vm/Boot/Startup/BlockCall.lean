import OCaml.Vm.Boot.Startup.PrefixCall
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A generated block followed by its direct call: the block summary plus the
call seam, for every "set up arguments, then `jal`" span. -/
theorem block_then_call {entry : BitVec 64} {writes : List Nat} {log : List WEntry} {value : BitVec 64}
    {regs : GRegs} {a : CallInstr} (c : Config) (shape : CallShape a) (decode : CallDecode a)
    (pins : ∀ d : Config, ExecutableImage d → CallPins a d)
    (front : FnSummary entry (fun d => d = c) (WriteRegistersPost writes log c a.pc value regs))
    (keys : KeysOK (keysG regs)) (avoid : KeysAvoidRa regs) (result : lookupG 10 regs = some value) :
    FnSummary entry (fun d => d = c)
      (WriteRegistersPost (writes ++ [1]) log c a.target value ((1, a.link) :: regs)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  obtain ⟨after, run2, called⟩ := (call_registers_summary shape decode request (pins _ setup.image) setup.good
    setup.image setup.tick setup.minstret _ setup.regs keys avoid result).run request ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩
end OCaml.Vm.Boot.Startup
