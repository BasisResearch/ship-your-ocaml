import OCaml.Vm.Boot.Startup.InterpreterInitSteps
import OCaml.Vm.Boot.Startup.ReturnStub
import OCaml.Vm.Boot.Startup.CustomLive
import OCaml.Vm.Boot.Startup.RuntimeStack

namespace OCaml.Vm.Boot.Startup
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable OCaml.Vm.Primitives
open VsaIris.Inst
open OCaml.Vm.Sim (InterpReturnPost InterpReturnInput interp_return interpReturnWrites)

/-- The epilogue's actual GPR write set. -/
def interpreterReturnRegs : List Nat := Layout.interpSavedRegs ++ [2,10]

theorem interpreter_return_present {c after : Config} {saved : Nat → BitVec 64}
    (R : InterpReturnPost c (nativeFrameBase parameterStack Layout.interpFrameBytes) saved 1 after) :
    WrittenPresent interpreterReturnRegs after := by
  intro n member _ _
  rcases List.mem_append.mp member with savedReg | other
  · change (OCaml.Vm.gpr after n).isSome
    rw [R.registers n savedReg]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at other
    rcases other with rfl | rfl
    · change (gpr after 2).isSome; rw [R.stack]; rfl
    · change (gpr after 10).isSome; rw [R.value]; rfl

/-- Adapt the existing checked epilogue to the startup runtime-frame interface. -/
theorem interpreter_return_post {c after : Config} {saved : Nat → BitVec 64}
    (R : InterpReturnPost c (nativeFrameBase parameterStack Layout.interpFrameBytes) saved 1 after) :
    WriteRegistersPost interpreterReturnRegs [] c (saved 1) 1
      [(2,parameterStack),(10,1),(1,saved 1)] after := by
  have stack : gprGet after.σ 2 = some parameterStack := by
    simpa only [OCaml.Vm.gpr, show BitVec.ofNat 64 (nativeFrameBase parameterStack Layout.interpFrameBytes + Layout.interpFrameBytes) =
      parameterStack by decide] using R.stack
  have frame : StepFrameOut (interpreterReturnRegs.map gprReg ++ noiseRegs) c.σ after.σ := by
    simpa only [interpreterReturnRegs, interpReturnWrites, List.map_append, List.map_cons, List.map_nil,
      show gprReg 2 = Register.x2 from rfl, show gprReg 10 = Register.x10 from rfl] using R.frame
  have written := interpreter_return_present R
  exact {
    good := R.good
    image := R.image
    minstret := R.good.minstret
    tick := R.tick
    pc := R.pc
    result := R.value
    memory := R.memory
    output := frame.out
    frame := fun r hr hn => frame.frame r fun q hq => by
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨n,hm,rfl⟩ := List.mem_map.mp hq
        exact beq_eq_false_iff_ne.mpr (hr n hm)
      · exact hn q hq
    kept := GprsKept.of_stepFrame (by decide) (by decide) (fun n hn => written n hn
      (by have := (show KeysOK interpreterReturnRegs by decide) n hn; omega)
      (by have := (show KeysOK interpreterReturnRegs by decide) n hn; omega)) frame
    regs := ⟨stack,R.value,R.registers 1 (by decide),trivial⟩ }

/-- All initialization preconditions come from the backtrace return's runtime contract. -/
structure InterpreterInitInput (H : List (Nat × Nat)) (capacity : Nat) (ra : BitVec 64) (c : Config) : Prop where
  pc : PCAt 0x80004e84#64 c
  ready : RuntimeReady H capacity parameterStack ra c

/-- Initialization returns through the debugger at the next actual main instruction.
The log contains only the thirteen interpreter saves; no threaded-code setup occurs. -/
structure InterpreterInitDone (H : List (Nat × Nat)) (capacity : Nat) (before after : Config) where
  bank : Nat → BitVec 64
  bankLink : bank 1 = 0x80004e90#64
  bankAbi : ∀ k ∈ abiSaved, gprGet before.σ k = some (bank k)
  pc : PCAt 0x80004e94#64 after
  unit : gprGet after.σ 10 = some 1
  ready : RuntimeReady H capacity parameterStack 0x80004e94#64 after
  memory : after.σ.mem = writeLog before.σ.mem (interpreterInitLog bank)
  saved : ∀ k ∈ abiSaved, gprGet after.σ k = gprGet before.σ k
  live : LiveFrame H before after
  caller : CallerFrame parameterStack before after
  htif : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ

theorem InterpreterInitDone.abi {H capacity before after} (D : InterpreterInitDone H capacity before after) :
    GprsSame before after abiClobbered := GprsSame.of_saved D.saved

/-- The exact stack stores preserve every byte below the interpreter frame. -/
theorem InterpreterInitDone.below {H capacity before after} (D : InterpreterInitDone H capacity before after)
    (x : Nat) (lower : x < nativeFrameBase parameterStack Layout.interpFrameBytes) :
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := by
  rw [D.memory, frameOn_writeLog _ _ _ (interpreterInit_inside D.bank) x ⟨Or.inl lower,trivial⟩]

/-- Compose the generated NULL-program branch with the existing interpreter epilogue
and the generated debugger JAL/return stub. -/
theorem interpreter_debugger_init (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (ra : BitVec 64)
    (A : InterpreterInitInput H capacity ra c) :
    ∃ after, Steps c after ∧ Nonempty (InterpreterInitDone H capacity c after) := by
  have frame := interpreterInit_frame
  obtain ⟨d,run1,P⟩ := (caml_interpreter_init_call c ra A.ready.toLeafInput).run c ⟨A.pc,rfl⟩
  have gP := GprsSame.of_post P (by decide)
  have readyD := A.ready.stack_log P (by decide) (by simp only [keysG]; decide) (by decide)
    (gP.get (by decide) (by decide) (by decide) A.ready.stack)
    (gholds_lookup (n := 1) _ P.regs rfl) (by decide) frame (by simp only [LogInW])
  let saved : Nat → BitVec 64 := vsaReg d
  have bank (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : gprGet d.σ n = some (saved n) :=
    library_gpr readyD.platform lo hi rfl
  have regs : GHolds d.σ (interpreterInitBank saved) :=
    ⟨readyD.stack,bank 1 (by decide) (by decide),bank 8 (by decide) (by decide),bank 9 (by decide) (by decide),
      bank 18 (by decide) (by decide),bank 19 (by decide) (by decide),bank 20 (by decide) (by decide),
      bank 21 (by decide) (by decide),bank 22 (by decide) (by decide),bank 23 (by decide) (by decide),
      bank 24 (by decide) (by decide),bank 25 (by decide) (by decide),bank 26 (by decide) (by decide),
      bank 27 (by decide) (by decide),gholds_lookup (n := 10) _ P.regs rfl,trivial⟩
  have link : saved 1 = jal_80004e8c_call.link := Option.some.inj ((bank 1 (by decide) (by decide)).symm.trans readyD.raReg)
  have leafD : LeafInput (saved 1) d := by rw [link]; exact readyD.toLeafInput
  obtain ⟨e,run2,Q⟩ := (interpreter_init_save d saved leafD regs).run d
    ⟨by rw [← jal_80004e8c_call_target]; exact P.pc,rfl⟩
  have gQ := GprsSame.of_post Q (by decide)
  have readyE := readyD.stack_log Q (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ Q.regs rfl)
    (gQ.get (by decide) (by decide) (by decide) readyD.raReg) (by decide) frame (interpreterInit_inside saved)
  obtain ⟨f,run3,J⟩ := (interpreter_init_jump e _ readyE.toLeafInput
    (gholds_lookup (n := 10) _ Q.regs rfl)).run e ⟨Q.pc,rfl⟩
  have gJ := GprsSame.of_post J (by decide)
  have readyF := readyE.stack_log J (by decide) (by simp only [keysG]; decide) (by decide)
    (gJ.get (by decide) (by decide) (by decide) readyE.stack)
    (gJ.get (by decide) (by decide) (by decide) readyE.raReg) (by decide) frame (by simp only [LogInW])
  obtain ⟨g,run4,U⟩ := (interpreter_init_unit f _ readyF.toLeafInput
    (gholds_lookup (n := 10) _ J.regs rfl)).run f ⟨J.pc,rfl⟩
  have gU := GprsSame.of_post U (by decide)
  have readyG := readyF.stack_log U (by decide) (by simp only [keysG]; decide) (by decide)
    (gU.get (by decide) (by decide) (by decide) readyF.stack)
    (gU.get (by decide) (by decide) (by decide) readyF.raReg) (by decide) frame (by simp only [LogInW])
  have memG : g.σ.mem = writeLog d.σ.mem (interpreterInitLog saved) := U.memory.trans (J.memory.trans Q.memory)
  have input : InterpReturnInput (nativeFrameBase parameterStack Layout.interpFrameBytes) saved 1 g := {
    good := readyG.good
    image := readyG.image
    pc := U.pc
    tick := readyG.tick
    frame := interpreter_init_saved saved memG
    stack := readyG.stack
    value := gholds_lookup (n := 21) _ U.regs rfl
    aligned := by rw [link]; decide }
  obtain ⟨n,h,run5,R⟩ := interp_return input
  have RP := interpreter_return_post R
  have readyH := readyG.stack_log_written RP (by decide)
    (interpreter_return_present R)
    (by decide) (gholds_lookup (n := 2) _ RP.regs rfl) (gholds_lookup (n := 1) _ RP.regs rfl)
    (by rw [link]; decide) frame (by simp only [LogInW])
  have pcH : PCAt jal_80004e90_call.pc h := by have pc := R.pc; rw [link] at pc; exact pc
  obtain ⟨i,run6,C⟩ := (call_registers_summary jal_80004e90_call_shape jal_80004e90_call_decode h
    (jal_80004e90_call_pins readyH.image) readyH.good readyH.image readyH.tick readyH.minstret
    [(10,1)] ⟨R.value,trivial⟩ (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa,keysG]; decide) rfl).run h ⟨pcH,rfl⟩
  have gC := GprsSame.of_post C (by decide)
  have CP : WriteRegistersPost [1] [] h jal_80004e90_call.target 1
      [(1,jal_80004e90_call.link),(10,1)] i := C
  have readyI := readyH.stack_log CP (by decide) (by simp only [keysG]; decide) (by decide)
    (gC.get (by decide) (by decide) (by decide) readyH.stack)
    (gholds_lookup (n := 1) _ C.regs rfl) (by decide) frame (by simp only [LogInW])
  obtain ⟨after,run7,D⟩ := (return_stub .debugger i _ 1 readyI.toLeafInput
    (gholds_lookup (n := 10) _ C.regs rfl)).run i ⟨C.pc,rfl⟩
  have gD := GprsSame.of_post D (by decide)
  have readyAfter := readyI.stack_log D (by decide) (by simp only [keysG]; decide) (by decide)
    (gD.get (by decide) (by decide) (by decide) readyI.stack)
    (gD.get (by decide) (by decide) (by decide) readyI.raReg) (by decide) frame (by simp only [LogInW])
  have memory : after.σ.mem = writeLog c.σ.mem (interpreterInitLog saved) := by
    rw [show after.σ.mem = i.σ.mem from D.memory, C.memory, R.memory, memG, show d.σ.mem = c.σ.mem from P.memory]
  have same := gC.trans gD
  have savedAfter : ∀ k ∈ abiSaved, gprGet after.σ k = gprGet c.σ k := by
    intro k hk
    have bounds : ∀ k ∈ abiSaved, 1 ≤ k ∧ k ≤ 31 ∧ k ∉ [1] ∧ k ∈ Layout.interpSavedRegs ∧ k ∉ [11,10] ++ [1] := by decide
    obtain ⟨lo,hi,out,savedReg,outP⟩ := bounds k hk
    have restored : gprGet h.σ k = some (saved k) := R.registers k savedReg
    rw [same.same k lo hi (by simpa using out), restored]
    exact (bank k lo hi).symm.trans (gP.same k lo hi outP)
  have live : LiveFrame H c after := LiveFrame.of_stack memory (interpreterInit_inside saved) frame
    (fun e he => (A.ready.block_bounds he).2)
  exact ⟨after,run1.trans (run2.trans (run3.trans (run4.trans (run5.toSteps.trans (run6.trans run7))))),⟨{
    bank := saved
    bankLink := link
    bankAbi := fun k hk => by
      have bounds : ∀ k ∈ abiSaved, 1 ≤ k ∧ k ≤ 31 ∧ k ∉ [11,10] ++ [1] := by decide
      have b := bounds k hk
      exact (gP.same k b.1 b.2.1 b.2.2).symm.trans (bank k b.1 b.2.1)
    pc := D.pc
    unit := gholds_lookup (n := 10) _ D.regs rfl
    ready := readyAfter
    memory := memory
    saved := savedAfter
    live := live
    caller := ⟨fun x hx => by rw [memory,frameOn_writeLog _ _ _ (interpreterInit_inside saved) x ⟨Or.inr hx,trivial⟩]⟩
    htif := readyAfter.platform.htifIdle.trans A.ready.platform.htifIdle.symm
    output := by unfold Vsa.Machine.output; rw [D.output,C.output,R.frame.out,U.output,J.output,Q.output,P.output] }⟩⟩

end OCaml.Vm.Boot.Startup
