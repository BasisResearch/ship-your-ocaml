import OCaml.Vm.Boot.Startup.CamlAttemptOpenNormalized
import OCaml.Vm.Boot.Startup.CamlAttemptOpenCallInterface
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.Write
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- `exe_name = argv[0]` is stored at `sp + 32`, then caml_attempt_open is called with
`&exe_name`, `&trail` (`sp + 40`) and `do_open_script = 0`. -/
def camlAttemptLog (sp name : BitVec 64) : List WEntry := [((sp + 32#64).toNat, 8, name)]
def camlAttemptRegs (sp argv name : BitVec 64) : GRegs :=
  [(12, 0#64), (10, sp + 32#64), (11, sp + 40#64), (15, name), (9, argv), (2, sp)]

theorem camlAttempt_input {sp argv ra c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(9, argv), (2, sp)]) (load : ReadWindow argv 8)
    (slot : WriteWindow (sp + 32#64) 8) :
    BlockInput camlAttemptOpenSave 0x80004de4#64 [(9, argv), (2, sp)] [read8 c.σ.mem argv.toNat] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [9, 2]; decide
  shape := by change ChainOK _ [9, 2] _; decide
  tick := leaf.tick
  facts := by
    have code := camlAttemptOpen_code leaf.image
    chain_facts code with "Vsa.Sim.Code.caml_main_at_"
    · exact load.ld rfl (by change argv + 0#64 = argv; rw [BitVec.add_zero]) (read8_pins _ _)
    · exact slot.sd rfl rfl

/-- The actual caml_main call of caml_attempt_open on `argv[0]`. -/
theorem caml_attempt_open_call (c : Config) (sp ra argv : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(9, argv), (2, sp)]) (load : ReadWindow argv 8)
    (slot : WriteWindow (sp + 32#64) 8)
    (outside : ImageOutside (camlAttemptLog sp (bytesT c.σ.mem argv.toNat 8))) :
    FnSummary 0x80004de4#64 (fun d => d = c)
      (WriteRegistersPost [12, 10, 11, 15, 1] (camlAttemptLog sp (bytesT c.σ.mem argv.toNat 8)) c
        jal_80004df8_call.target (sp + 32#64)
        ((1, jal_80004df8_call.link) :: camlAttemptRegs sp argv (bytesT c.σ.mem argv.toNat 8))) := by
  have front : FnSummary 0x80004de4#64 (fun d => d = c)
      (WriteRegistersPost [12, 10, 11, 15] (camlAttemptLog sp (bytesT c.σ.mem argv.toNat 8)) c
        jal_80004df8_call.pc (sp + 32#64) (camlAttemptRegs sp argv (bytesT c.σ.mem argv.toNat 8))) := by
    apply registers_of_blocks leaf.image outside
      (block_summary _ _ _ _ _ (camlAttempt_input leaf regs load slot))
    · change [((sp + 32#64).toNat, 8, bytesVal .ld (read8 c.σ.mem argv.toNat))] = _
      rw [read8_value]
      rfl
    · rfl
    · change [(12, 0#64 + 0#64), (10, sp + 32#64), (11, sp + 40#64),
        (15, bytesVal .ld (read8 c.σ.mem argv.toNat)), (9, argv), (2, sp)] = _
      rw [BitVec.add_zero, read8_value]
      rfl
    · rfl
    · decide
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  obtain ⟨after, run2, called⟩ := (call_registers_summary jal_80004df8_call_shape jal_80004df8_call_decode request
    (jal_80004df8_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ setup.regs
    (by change KeysOK [12, 10, 11, 15, 9, 2]; decide)
    (by simp only [KeysAvoidRa, camlAttemptRegs, keysG]; decide) (by rfl)).run request ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩
end OCaml.Vm.Boot.Startup
