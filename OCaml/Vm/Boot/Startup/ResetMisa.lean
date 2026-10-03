import OCaml.Vm.Boot.Startup.RunnerSetup
open Vsa.Machine LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
namespace OCaml.Vm.Boot.Startup
structure MisaResetPost (before after : MState) : Prop where
  run : (reset_misa ()).run before = .ok () after
  misa : after.regs.get? .misa = some Vsa.Sim.initMisa
  memory : after.mem = before.mem
  output : after.sailOutput = before.sailOutput
  cycles : after.cycleCount = before.cycleCount
  frame : ∀ r, r ≠ .misa → after.regs.get? r = before.regs.get? r

/-- Architectural reset installs the running ISA flags from the model seed. -/
theorem reset_misa_run (s : MState) (h : s.regs.get? .misa = some 0x8000000000000000#64) :
    ∃ t, MisaResetPost s t := by
  have callback (v : BitVec 64) : csr_name_write_callback "misa" v = (pure () : SailM Unit) := by
    unfold csr_name_write_callback
    have map : csr_name_map_backwards "misa" = (pure 0x301#12 : SailM (BitVec 12)) := by
      unfold csr_name_map_backwards; rfl
    rw [map]; rfl
  refine ⟨?state, { run := ?runProof, misa := ?_, memory := ?_, output := ?_, cycles := ?_, frame := ?_ }⟩
  case runProof =>
    simp only [reset_misa, EStateM.run, bind, EStateM.bind, writeReg, PreSail.writeReg,
      readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      callback, pure, EStateM.pure, h, hartSupports]
    simp [Std.ExtDHashMap.get?_insert, EStateM.pure, EStateM.bind, EStateM.get, EStateM.modifyGet]
    rfl
  · simp [Std.ExtDHashMap.get?_insert]
    decide +kernel
  · rfl
  · rfl
  · rfl
  · intro r other
    simp [Std.ExtDHashMap.get?_insert, Ne.symm other]

end OCaml.Vm.Boot.Startup
