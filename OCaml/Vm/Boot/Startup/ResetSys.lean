import OCaml.Vm.Boot.Startup.ResetMisaEffect
import OCaml.Vm.Boot.Startup.ResetTvec
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
namespace OCaml.Vm.Boot.Startup
/-- Registers written by the architectural system-reset source. -/
def sysResetWrites : List Register :=
  [.cur_privilege, .mstatus, .misa, .PC, .nextPC, .mcause, .mseccfg,
   .mstateen0, .mstateen1, .mstateen2, .mstateen3, .vstart, .vl, .vcsr, .vtype]

structure SysResetPost (before after : MState) : Prop where
  run : (reset_sys ()).run before = .ok () after
  memory : after.mem = before.mem
  output : after.sailOutput = before.sailOutput
  cycles : after.cycleCount = before.cycleCount
  misa : after.regs.get? .misa = some initMisa
  mstatus : after.regs.get? .mstatus = some initMstatus
  privilege : after.regs.get? .cur_privilege = some .Machine
  mseccfg : after.regs.get? .mseccfg = some 0#64
  pc : after.regs.get? .PC = some 0#64
  nextPC : after.regs.get? .nextPC = some 0#64
  frame : ∀ r, r ∉ sysResetWrites → after.regs.get? r = before.regs.get? r

/-- Source system reset succeeds from the actual model and runner initial values. -/
theorem reset_sys_run (s : MState) (seed : ModelSeed s) (defs : RunnerDefaults s) :
    ∃ t, SysResetPost s t := by
  have callback (name : String) (csr : BitVec 12)
      (map : csr_name_map_backwards name = (pure csr : SailM (BitVec 12))) (v : BitVec 64) :
      csr_name_write_callback name v = (pure () : SailM Unit) := by
    unfold csr_name_write_callback; rw [map]; rfl
  have status (v : BitVec 64) : long_csr_write_callback "mstatus" "mstatush" v = (pure () : SailM Unit) := by
    unfold long_csr_write_callback
    apply callback _ 0x300#12
    unfold csr_name_map_backwards; rfl
  have cause (v : BitVec 64) : csr_name_write_callback "mcause" v = (pure () : SailM Unit) := by
    apply callback _ 0x342#12
    unfold csr_name_map_backwards; rfl
  have misa (t : MState) (h : t.regs.get? .misa = some 0x8000000000000000#64) :
      reset_misa () t = .ok () { t with regs := t.regs.insert .misa initMisa } := reset_misa_effect t h
  have pmp (t : MState) (h : t.regs.get? .pmpcfg_n = some initPmpcfg) :
      reset_pmp () t = .ok () t := reset_pmp_run t h
  have tvec (t : MState) (hm : t.regs.get? .mtvec = some 0#64) (hs : t.regs.get? .stvec = some 0#64) :
      reset_tvecs () t = .ok () t := reset_tvecs_run t hm hs
  refine ⟨?state, { run := ?runProof, memory := ?_, output := ?_, cycles := ?_, misa := ?_, mstatus := ?_, privilege := ?_, mseccfg := ?_, pc := ?_, nextPC := ?_, frame := ?_ }⟩
  case runProof =>
    simp (disch := (simp [Std.ExtDHashMap.get?_insert, seed.misa, defs.pmpcfg, defs.mtvec, defs.stvec]))
      [reset_sys, EStateM.run, Bind.bind, EStateM.bind,
       readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
       writeReg, PreSail.writeReg, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
       pure, EStateM.pure, misa, pmp, tvec, status, cause, cancel_reservation, dbgTrace,
       reset_stateen, hartSupports,
       Std.ExtDHashMap.get?_insert, seed.mstatus, seed.mseccfg, seed.resetPC, defs.vcsr, defs.vtype]
    rfl
  · rfl
  · rfl
  · rfl
  · simp [Std.ExtDHashMap.get?_insert]
  · simp [Std.ExtDHashMap.get?_insert]
    decide +kernel
  · simp [Std.ExtDHashMap.get?_insert]
  · simp [Std.ExtDHashMap.get?_insert]; decide +kernel
  · simp [Std.ExtDHashMap.get?_insert]
  · simp [Std.ExtDHashMap.get?_insert]
  · intro r hr
    clear callback status cause misa pmp tvec seed defs
    simp (disch := decide) only [register_insert_frame sysResetWrites r hr]
end OCaml.Vm.Boot.Startup
