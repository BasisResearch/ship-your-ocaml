import OCaml.Vm.Boot.Startup.LegalizeReset
import Vsa.Sim.InitValues
open Vsa.Machine LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
namespace OCaml.Vm.Boot.Startup
/-- Model-initialized controls retained by the runner's register setup. -/
structure ModelSeed (s : MState) : Prop where
  misa : s.regs.get? .misa = some 0x8000000000000000#64
  mstatus : s.regs.get? .mstatus = some Vsa.Sim.initMstatus
  mseccfg : s.regs.get? .mseccfg = some 0#64
  senvcfg : s.regs.get? .senvcfg = some 0#64
  menvcfg : s.regs.get? .menvcfg = some 0#64
  resetPC : s.regs.get? .pc_reset_address = some 0#64
  pma : s.regs.get? .pma_regions = some Vsa.Sim.initPmaRegions
  meip : s.regs.get? .sig_meip = some 0#1
  seip : s.regs.get? .sig_seip = some 0#1

/-- Effects needed by the subsequent register initialization and architectural reset. -/
structure ModelInitPost (before after : MState) : Prop extends ModelSeed after where
  run : (sail_model_init ()).run before = .ok () after
  memory : after.mem = before.mem
  output : after.sailOutput = before.sailOutput
  cycles : after.cycleCount = before.cycleCount
  done : after.regs.get? .htif_done = some false

/-- Successful source model initialization for every input state. -/
theorem model_init (s : MState) : ∃ t, ModelInitPost s t := by
  have hs (s : MState) (hm : s.regs.get? .misa = some 0x8000000000000000#64) :
      legalize_senvcfg 0#64 0#64 s = .ok 0#64 s := legalize_senvcfg_zero s _ hm
  have hm (s : MState) (hm : s.regs.get? .misa = some 0x8000000000000000#64) :
      legalize_mseccfg 0#64 0#64 s = .ok 0#64 s := legalize_mseccfg_zero s _ hm
  have he (s : MState) (hm : s.regs.get? .misa = some 0x8000000000000000#64) :
      legalize_menvcfg 0#64 0#64 s = .ok 0#64 s := legalize_menvcfg_zero s _ hm
  have bits32 : to_bits_checked (l := 32) 0 = (pure 0#32 : SailM (BitVec 32)) := by rfl
  have bits64 : to_bits_checked (l := 64) 0 = (pure 0#64 : SailM (BitVec 64)) := by rfl
  refine ⟨?state, { run := ?runProof, memory := ?_, output := ?_, cycles := ?_, misa := ?_, mstatus := ?_, mseccfg := ?_, senvcfg := ?_, menvcfg := ?_, resetPC := ?_, done := ?_, pma := ?_, meip := ?_, seip := ?_ }⟩
  case runProof =>
    simp (disch := (simp [Std.ExtDHashMap.get?_insert]; decide)) only [sail_model_init, EStateM.run, bind, EStateM.bind,
      writeReg, PreSail.writeReg, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      hs, hm, he, Mk_SEnvcfg, Mk_Seccfg, Mk_MEnvcfg, zeros, BitVec.zero, BitVec.ofNatLT_zero, bits32, bits64, pure, EStateM.pure]
    rfl
  all_goals first | rfl | (simp [Std.ExtDHashMap.get?_insert] <;> first | rfl | decide +kernel)

end OCaml.Vm.Boot.Startup
