import OCaml.Vm.Boot.Startup.Crt0Run
import OCaml.Vm.Boot.Startup.Crt0Calls
import OCaml.Vm.Boot.Startup.Main

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

structure MainEntry (initial c : Config) : Prop where
  ready : MainReady 0x8000003c#64 c
  pc : PCAt (BitVec.ofNat 64 Layout.sym_main) c
  memory : c.σ.mem = clearWords initial.σ.mem Layout.sym_bss_start bssWords
  gp : gprGet c.σ 3 = some (BitVec.ofNat 64 Layout.sym_global_pointer)
  argc : gprGet c.σ 10 = some 0#64
  argv : gprGet c.σ 11 = some 0#64
  output : c.σ.sailOutput = initial.σ.sailOutput

/-- A complete crt0 summary, including its direct call into main.
The startup platform and image hypotheses are explicit; reset supplies them. -/
theorem crt0_to_main (initial : Config) (h : CrtReady initial)
    (mainCode : Code.MainLoaded initial.σ.mem) :
    FnSummary (BitVec.ofNat 64 Layout.sym_start) (fun c => c = initial)
      (MainEntry initial) := by
  constructor
  rintro c ⟨pc, eq⟩
  subst c
  obtain ⟨call, front, p⟩ := (crt0_to_call initial h).run initial ⟨pc, rfl⟩
  obtain ⟨d, jump, q⟩ := (call_80000038 call p.ready.good p.ready.tick p.ready.code).run call ⟨p.pc, rfl⟩
  have memory := q.memory.trans p.memory
  have code : Code.MainLoaded d.σ.mem := Code.main_transport mainCode (by
    intro a lo hi
    rw [memory]
    apply clearWords_below
    unfold Layout.sym_bss_start
    omega)
  refine ⟨d, front.trans jump, ⟨⟨q.good, q.tick, code, ?_, q.linkReg⟩,
    q.pc, memory, ?_, ?_, ?_, q.output.trans p.output⟩⟩
  · exact (q.frame .x2 (by decide) (by decide)).trans p.stack
  · exact (q.frame .x3 (by decide) (by decide)).trans p.gp
  · exact (q.frame .x10 (by decide) (by decide)).trans p.argc
  · exact (q.frame .x11 (by decide) (by decide)).trans p.argv

end OCaml.Vm.Boot.Startup
