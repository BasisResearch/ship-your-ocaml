import OCaml.Vm.Boot.Startup.InitializerFrame

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine LeanRV64DExecutable Vsa.Sim.RegisterWrites

/-- Source-initialized defaults needed by reset and the running-platform invariant. -/
structure RunnerDefaults (s : MState) : Prop where
  mie : s.regs.get? .mie = some 0#64
  satp : s.regs.get? .satp = some 0#64
  mtvec : s.regs.get? .mtvec = some 0#64
  stvec : s.regs.get? .stvec = some 0#64
  mideleg : s.regs.get? .mideleg = some 0#64
  medeleg : s.regs.get? .medeleg = some 0#64
  done : s.regs.get? .htif_done = some false
  pmpcfg : s.regs.get? .pmpcfg_n = some Vsa.Sim.initPmpcfg
  pmpaddr : s.regs.get? .pmpaddr_n = some Vsa.Sim.initPmpaddr
  inhibit : s.regs.get? .mcountinhibit = some 0#32
  cyclecfg : s.regs.get? .mcyclecfg = some 0#64
  instretcfg : s.regs.get? .minstretcfg = some 0#64
  mip : s.regs.get? .mip = some 0#64
  time : s.regs.get? .mtime = some 0#64
  timecmp : s.regs.get? .mtimecmp = some 0#64
  instret : s.regs.get? .minstret = some 0#64
  increment : s.regs.get? .minstret_increment = some false
  cycle : s.regs.get? .mcycle = some 0#64
  nextPC : s.regs.get? .nextPC = some 0#64
  vcsr : s.regs.get? .vcsr = some 0#3
  vtype : s.regs.get? .vtype = some 0#64

/-- Finite readback certificates over the generated register-write list. -/
theorem runner_defaults (elf : ELF64File) (host : Nat) (s : MState) :
    RunnerDefaults (apply (elfRegisterAssignments elf host) s) := by
  constructor <;> apply initializer_read_tail <;> decide +kernel

end OCaml.Vm.Boot.Startup
