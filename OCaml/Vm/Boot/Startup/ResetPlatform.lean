import OCaml.Vm.Boot.Startup.ResetSys
import Vsa.Sim.GoodState
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
namespace OCaml.Vm.Boot.Startup
structure ResetPost (before after : MState) : Prop where
  run : (reset ()).run before = .ok () after
  good : GoodState after
  memory : after.mem = before.mem
  output : after.sailOutput = before.sailOutput
  cycles : after.cycleCount = before.cycleCount
  gprs : ∀ n, 1 ≤ n → n < 32 → gprGet after n = gprGet before n

/-- All architectural reset stages establish the running platform invariant. -/
theorem reset_run (s : MState) (seed : ModelSeed s) (defs : RunnerDefaults s)
    (host : HostPins tohostAddr s) : ∃ t, ResetPost s t := by
  let u : MState := { s with regs := s.regs.insert .hart_state (.HART_ACTIVE ()) }
  have useed : ModelSeed u := by
    cases seed
    constructor <;> simp_all [u, Std.ExtDHashMap.get?_insert]
  have udefs : RunnerDefaults u := by
    constructor
    all_goals try (solve | cases defs; simp_all [u, Std.ExtDHashMap.get?_insert])
    intro n lo hi
    have initialized := defs.gprs n lo hi
    gpr_cases n => simpa [gprGet, u, Std.ExtDHashMap.get?_insert] using initialized
  obtain ⟨mid, sys⟩ := reset_sys_run u useed udefs
  refine ⟨?state, {run := ?runProof, good := ?_, memory := ?_, output := ?_, cycles := ?_, gprs := ?_}⟩
  case runProof =>
    simp only [reset, EStateM.run, Bind.bind, EStateM.bind, writeReg, PreSail.writeReg,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
    rw [show reset_sys () u = .ok () mid from sys.run]
    simp only [reset_vmem, reset_TLB, reset_elp, writeReg, PreSail.writeReg,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure, EStateM.pure]
    rfl
  · constructor <;> simp [Std.ExtDHashMap.get?_insert]
    all_goals try (first | exact sys.privilege | exact sys.misa | exact sys.mstatus | exact sys.mseccfg)
    all_goals try rw [sys.frame _ (by decide)]
    all_goals try simp only [u]
    all_goals try simp [Std.ExtDHashMap.get?_insert]
    all_goals try (cases seed; cases defs; cases host; first | assumption | exact ⟨_, by assumption⟩)
    all_goals first | rfl | exact Or.inl defs.increment | exact ⟨_, sys.nextPC⟩ | exact ⟨_, sys.pc⟩
  · exact sys.memory
  · exact sys.output
  · exact sys.cycles
  · intro n lo hi
    gpr_cases n =>
      simp only [gprGet]
      simp only [Std.ExtDHashMap.get?_insert]
      rw [sys.frame _ (by decide)]
      simp [u, Std.ExtDHashMap.get?_insert]
end OCaml.Vm.Boot.Startup
