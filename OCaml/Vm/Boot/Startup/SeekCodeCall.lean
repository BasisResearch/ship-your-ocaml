import OCaml.Vm.Boot.Startup.CamlCodeSeekNormalized
import OCaml.Vm.Boot.Startup.CamlCodeSeekCallInterface
import OCaml.Vm.Boot.Startup.CodeSectionName
import OCaml.Vm.Boot.Startup.InterpreterInitReset
import OCaml.Vm.Boot.Startup.BlockCall
import OCaml.Vm.Boot.Startup.CodeSeekTestNormalized
import OCaml.Vm.Boot.Startup.CodeSeekTestImage

namespace OCaml.Vm.Boot.Startup
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The real caml_main arguments to the direct optional-section call. -/
def codeSeekArgs : GRegs :=
  [(12,codeSectionName0),(10,3),(11,WhileMinElfParse.trailSlot),(2,parameterStack),(8,3)]

/-- Execute argument setup and the actual JAL; no separate seek wrapper exists. -/
theorem caml_code_seek_call (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(2,parameterStack),(8,3)]) :
    FnSummary 0x80004e94#64 (fun d => d = c)
      (WriteRegistersPost ([11,10,12] ++ [1]) [] c jal_80004ea4_call.target 3
        ((1,jal_80004ea4_call.link) :: codeSeekArgs)) := by
  apply block_then_call c jal_80004ea4_call_shape jal_80004ea4_call_decode
    (fun _ h => jal_80004ea4_call_pins h) ?_ (by simp only [keysG,codeSeekArgs]; decide)
    (by simp only [KeysAvoidRa,keysG,codeSeekArgs]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_mainX4e94Seg 0x80004e94#64
        [(2,parameterStack),(8,3)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [2,8]; decide
      shape := by change ChainOK _ [2,8] _; decide
      facts := by
        have code := camlCodeSeek_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_main_at_" }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

/-- The checked debugger return supplies this concrete argument-setup input. -/
structure CodeSeekCallInput (H : List (Nat × Nat)) (capacity : Nat) (c : Config) : Prop where
  pc : PCAt 0x80004e94#64 c
  ready : RuntimeReady H capacity parameterStack 0x80004e94#64 c
  caller : LoadCaller c

/-- The native optional-section entry, before its first stack store. -/
structure CodeSeekCallDone (H : List (Nat × Nat)) (capacity : Nat) (before after : Config) : Prop where
  pc : PCAt 0x80004bcc#64 after
  regs : GHolds after.σ ((1,0x80004ea8#64) :: codeSeekArgs)
  ready : RuntimeReady H capacity parameterStack 0x80004ea8#64 after
  memory : after.σ.mem = before.σ.mem
  abi : GprsSame before after abiClobbered

theorem code_seek_call (c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (input : CodeSeekCallInput H capacity c) :
    ∃ after, Steps c after ∧ CodeSeekCallDone H capacity c after := by
  obtain ⟨after,run,P⟩ := (caml_code_seek_call c 0x80004e94 input.ready.toLeafInput
    ⟨input.ready.stack,input.caller.fd,trivial⟩).run c ⟨input.pc,rfl⟩
  have frame : NativeFrame parameterStack 16 := by constructor <;> decide
  have ready := input.ready.stack_log P (by decide) (by simp only [keysG,codeSeekArgs]; decide)
    (by decide) (gholds_lookup (n := 2) _ P.regs rfl) (gholds_lookup (n := 1) _ P.regs rfl)
    (by decide) frame (by simp only [LogInW])
  exact ⟨after,run,{
    pc := P.pc
    regs := P.regs
    ready := ready
    memory := P.memory
    abi := (GprsSame.of_post P (by decide)).mono (by decide) }⟩

/-- Once the actual scan returns the selected length, execute and reject the
missing-section edge at 0x80004eac. This does not supply the pending scan. -/
theorem code_seek_present (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (length : gprGet c.σ 10 = some 764#64) :
    FnSummary 0x80004ea8#64 (fun d => d = c)
      (WriteRegistersPost [15] [] c 0x80004eb0#64 764#64 [(15,-1#64),(10,764#64)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_mainX4ea8FSeg 0x80004ea8#64
        [(10,764#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := ⟨length,trivial⟩
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      facts := by
        have code := codeSeekTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_main_at_"
        decide }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

end OCaml.Vm.Boot.Startup

