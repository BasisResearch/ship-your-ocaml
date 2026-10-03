import OCaml.Vm.Boot.Startup.Crt0Run
import OCaml.Vm.Boot.Startup.Crt0Calls
import OCaml.Vm.Boot.Startup.Main

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

structure MainEntry (initial c : Config) : Prop where
  gprs : GprPresent initial.σ → GprPresent c.σ
  ready : MainReady 0x8000003c#64 c
  pc : PCAt (BitVec.ofNat 64 Layout.sym_main) c
  memory : c.σ.mem = clearWords initial.σ.mem Layout.sym_bss_start bssWords
  gp : gprGet c.σ 3 = some (BitVec.ofNat 64 Layout.sym_global_pointer)
  argc : gprGet c.σ 10 = some 0#64
  argv : gprGet c.σ 11 = some 0#64
  output : c.σ.sailOutput = initial.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1, 2, 3, 5, 6, 10, 11], (gprReg n == r) = false) →
    c.σ.regs.get? r = initial.σ.regs.get? r

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
  refine ⟨d, front.trans jump, ⟨?_, ⟨q.good, q.tick, code, ?_, q.linkReg⟩,
    q.pc, memory, ?_, ?_, ?_, q.output.trans p.output, ?_⟩⟩
  · exact fun beforePins => (p.gprs beforePins).of_link q.linkReg q.frame
  · exact (q.frame .x2 (by decide) (by decide)).trans p.stack
  · exact (q.frame .x3 (by decide) (by decide)).trans p.gp
  · exact (q.frame .x10 (by decide) (by decide)).trans p.argc
  · exact (q.frame .x11 (by decide) (by decide)).trans p.argv

  · intro r noise outside
    have x1 : r ≠ .x1 := by
      intro eq; subst r
      have no := outside 1 (by decide)
      contradiction
    exact (q.frame r noise x1).trans
      (p.frame r noise (fun n hn => outside n (by simp_all)))

end OCaml.Vm.Boot.Startup
