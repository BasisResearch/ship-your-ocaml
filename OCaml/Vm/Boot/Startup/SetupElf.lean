import OCaml.Vm.Boot.Startup.InitModel
import Vsa.Sim.Frame
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
namespace OCaml.Vm.Boot.Startup
structure SetupElfPost (elf : ELF64File) (before after : MState) : Prop where
  run : (Vsa.setupElf elf).run before = .ok () after
  good : GoodState after
  memory : after.mem = before.mem
  output : after.sailOutput = before.sailOutput
  cycles : after.cycleCount = before.cycleCount + 1
  pc : after.regs.get? .PC = some elf.file_header.e_entry.toBitVec
  idle : after.regs.get? .htif_payload_writes = some 0#4
  gprs : ∀ n, 1 ≤ n → n < 32 → gprGet after n = some 0#64

/-- Expose the proved runner stage without reducing its register-write program. -/
theorem setupElf_program (elf : ELF64File) : Vsa.setupElf elf = (do
    runnerSetup elf
    init_model ""
    cycle_count ()
    writeReg .PC elf.file_header.e_entry.toBitVec) := by
  simp only [Vsa.setupElf, runnerSetup, bind_assoc]

/-- Complete Sail setup, including validation, architectural reset and entry PC. -/
theorem setupElf_run (elf : ELF64File) (s : MState)
    (ht : tohostMetadata elf = some tohostAddr) : ∃ t, SetupElfPost elf s t := by
  obtain ⟨ready, runner⟩ := runner_setup elf tohostAddr s ht
  obtain ⟨mid, init⟩ := init_model_run ready runner.toModelSeed runner.toRunnerDefaults (runner.host _ ht)
  let final : MState := { mid with
    regs := mid.regs.insert .PC elf.file_header.e_entry.toBitVec
    cycleCount := mid.cycleCount + 1 }
  refine ⟨final, {run := ?_, good := ?_, memory := ?_, output := ?_, cycles := ?_, pc := ?_, idle := ?_, gprs := ?_}⟩
  · rw [setupElf_program]
    simp only [EStateM.run, Bind.bind, EStateM.bind]
    simp only [show runnerSetup elf s = .ok () ready from runner.run,
      show init_model "" ready = .ok () mid from init.init_run]
    rfl
  · exact GoodState.of_regs_eq
      (σ := {mid with regs := mid.regs.insert .PC elf.file_header.e_entry.toBitVec}) rfl
      (init.good.insert_nonpinned (r := .PC) (by decide) _)
  · exact init.memory.trans runner.memory
  · exact init.output.trans runner.output
  · exact congrArg (fun n => n + 1) (init.cycles.trans runner.cycles)
  · simp [final]
  · simpa [final, Std.ExtDHashMap.get?_insert] using init.idle.trans runner.idle
  · intro n lo hi
    have same : gprGet final n = gprGet mid n := by
      gpr_cases n => simp [gprGet, final, Std.ExtDHashMap.get?_insert]
    exact same.trans ((init.gprs n lo hi).trans (runner.gprs n lo hi))

/-- The machine's own reset state has the running platform invariant and loader memory. -/
structure ElfResetReady (elf : ELF64File) (c : Config) : Prop extends ElfReset elf c where
  good : GoodState c.σ
  memory : c.σ.mem = initializeMemory .B64 elf
  output : c.σ.sailOutput = #[]
  cycles : c.σ.cycleCount = 1
  idle : c.σ.regs.get? .htif_payload_writes = some 0#4
  gprs : ∀ n, 1 ≤ n → n < 32 → gprGet c.σ n = some 0#64

/-- Existence of the reset configuration follows from Sail setup, not a captured state. -/
theorem elf_reset_exists (elf : ELF64File) (ht : tohostMetadata elf = some tohostAddr) :
    ∃ c, ElfResetReady elf c := by
  obtain ⟨t, post⟩ := setupElf_run elf (resetSeed elf) ht
  exact ⟨⟨t, 0, 0⟩, {
    setup := post.run, tick := rfl, steps := rfl, good := post.good
    memory := post.memory, output := post.output, cycles := post.cycles, idle := post.idle, gprs := post.gprs}⟩
/-- Every successful reset has the same platform and loader facts. -/
theorem ElfReset.ready {elf : ELF64File} {c : Config} (reset : ElfReset elf c)
    (ht : tohostMetadata elf = some tohostAddr) : ElfResetReady elf c := by
  obtain ⟨t, post⟩ := setupElf_run elf (resetSeed elf) ht
  have eq : t = c.σ := (EStateM.Result.ok.inj (post.run.symm.trans reset.setup)).2
  subst t
  exact {
    toElfReset := reset, good := post.good, memory := post.memory
    output := post.output, cycles := post.cycles, idle := post.idle, gprs := post.gprs}

/-- Specialization to the metadata of the pinned while_min image. Loader correspondence
is still explicit in `WhileMinElf`; this theorem does not assume a startup run. -/
theorem whileMin_reset_exists (elf : ELF64File) (image : WhileMinElf elf) :
    ∃ c, ElfResetReady elf c := by
  apply elf_reset_exists
  exact image.tohost
end OCaml.Vm.Boot.Startup
