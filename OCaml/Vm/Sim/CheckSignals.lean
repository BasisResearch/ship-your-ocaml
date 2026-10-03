import OCaml.Vm.Sim.Immediate
import OCaml.Vm.Sim.CheckSignalsSegment
import OCaml.Vm.Sim.CheckSignalsPins
import OCaml.Vm.Runtime

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- Runtime supplies the no-pending branch condition at CHECK_SIGNALS. -/
structure SignalCheckReady (c : Config) : Prop where
  clear : word32 c Layout.sym_caml_something_to_do = 0#32

/-- The concrete runtime invariant discharges CHECK_SIGNALS readiness. -/
theorem signalCheckReady_of_runtime {freeList : Config → Prop} {c : Config}
    (h : RuntimeOk freeList c) : SignalCheckReady c := by
  constructor
  apply BitVec.eq_of_toNat_eq
  exact h.noPending

/-- CHECK_SIGNALS takes its no-pending branch and advances the bytecode PC.
Its fixed data address and read geometry come from the pinned ELF layout. -/
theorem check_signals_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .CHECK_SIGNALS c pl cp sp high)
    (quiet : SignalCheckReady c) :
    ∃ after, Plus c after ∧ Running L P {s with pc := s.pc + 1} after := by
  apply control_arm stable h
  intro d dp w accu _
  have bp : SegSt (0x800035cc#64)
      [⟨Register.x23, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64⟩,
       ⟨Register.x20, BitVec.ofNat 64 Layout.sym_caml_something_to_do⟩]
      (fun σ => Vsa.Sim.Code.CamlCheckSignalsLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨dp.nextCode, (dp.frame.frame Register.x20 (by decide)).trans h.dispatch.loop.pending, trivial⟩,
      dp.good.minstret, dp.tick, check_signals_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have pending : bytesT4 d.σ.mem (BitVec.ofNat 64 Layout.sym_caml_something_to_do).toNat = 0#32 := by
    simpa only [word32, bytesT_four_eq, dp.memory,
      show (BitVec.ofNat 64 Layout.sym_caml_something_to_do).toNat =
        Layout.sym_caml_something_to_do from by decide] using quiet.clear
  have run := tr_check_signals (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64)
    (BitVec.ofNat 64 Layout.sym_caml_something_to_do) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, pending] at run
  obtain ⟨nb, after, _, steps, post⟩ := run (by decide) (by decide) (by decide) (by decide) d bp
  obtain ⟨_, memory, frame⟩ := post.extra
  refine ⟨nb, after, steps, post.good, post.pcAt, ?_,
    (frame.frame Register.x21 (by decide)).trans accu, memory, frame.out,
    immediate_preserved frame (by decide)⟩
  have pc : gpr after Layout.reg_pc = some
      (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) := PinsHold.get post.pins ⟨1, by simp⟩
  simpa only [codePc_succ] using pc

/-- Bridge the actual CHECK_SIGNALS bytecode transition. -/
theorem check_signals_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .CHECK_SIGNALS c pl cp sp high)
    (quiet : SignalCheckReady c)
    (step : stepI P s ⟨.CHECK_SIGNALS, []⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have state : {s with pc := s.pc + 1} = s' := by simpa [stepI, St.adv] using step
  rw [← state]
  exact check_signals_arm stable h quiet

end OCaml.Vm.Sim
