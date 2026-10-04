import OCaml.Vm.Boot.Startup.EnvironmentSearch
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

/-- The actual reset history supplies every premise of the present-empty parser. -/
theorem ResetParameterEntry.input {initial entry H}
    (w : ResetParameterEntry initial entry)
    (ready : RuntimeReady H (startupAllocatorCredits - 192) parameterStack jal_80004d98_call.link entry) :
    ParameterPresentInput parameterStack parameterEnv parameterEntry jal_80004d98_call.link
      (vsaReg entry 8) (vsaReg entry 9) (vsaReg entry 18) (vsaReg entry 19)
      (vsaReg entry 20) (vsaReg entry 21) (vsaReg entry 22) parameterByte entry := by
  have reg (n : Nat) (lo : 0 < n) (hi : n ≤ 31) : gprGet entry.σ n = some (vsaReg entry n) :=
    library_gpr ready.platform lo hi rfl
  exact {
    toLeafInput := ready.toLeafInput
    frame := by constructor <;> decide
    regs := ⟨ready.stack, ready.raReg, reg 8 (by decide) (by decide), trivial⟩
    saved := ⟨reg 9 (by decide) (by decide), reg 18 (by decide) (by decide),
      reg 19 (by decide) (by decide), reg 20 (by decide) (by decide),
      reg 21 (by decide) (by decide), reg 22 (by decide) (by decide), trivial⟩
    environment := w.environment.global
    envNonzero := by decide
    search := w.environment.search ready.image
    valueWindow := by constructor <;> decide
    valueZero := w.environment.value_zero
    valueBelow := by decide }

/-- Closed reset execution after the complete native parameter parser returns
into caml_main. Later startup functions remain separate execution obligations. -/
structure ResetParameterReturned (initial after : Config) where
  entry : Config
  before : ResetParameterEntry initial entry
  run : Steps (Vsa.Densify.fillZero initial) after
  post : WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
    (parameterPresentLog parameterStack parameterEntry jal_80004d98_call.link
      (vsaReg entry 8) (vsaReg entry 9) (vsaReg entry 18) (vsaReg entry 19)
      (vsaReg entry 20) (vsaReg entry 21) (vsaReg entry 22)) entry jal_80004d98_call.link
    (parameterValuePointer parameterEntry)
    (parameterPresentRegs parameterStack parameterEnv parameterEntry jal_80004d98_call.link
      (vsaReg entry 8) (vsaReg entry 9) (vsaReg entry 18) (vsaReg entry 19)
      (vsaReg entry 20) (vsaReg entry 21) (vsaReg entry 22)) after
  ready : ∃ H, (firstDomainPtr.toNat, 928) ∈ H ∧
    RuntimeReady H (startupAllocatorCredits - 192) parameterStack jal_80004d98_call.link after

theorem ResetParameterReturned.reset {initial after} (w : ResetParameterReturned initial after) :
    ElfResetReady elf initial := w.before.reset

/-- The pinned ELF's own reset run reaches caml_main after parsing OCAMLRUNPARAM=.
Only generated function summaries and the shared loop fold are composed. -/
theorem reset_parameter_returned_exists : ∃ initial after, Nonempty (ResetParameterReturned initial after) := by
  obtain ⟨initial, entry, ⟨w⟩⟩ := reset_parameter_entry_exists
  obtain ⟨H, domain, ready⟩ := w.ready
  have input := w.input ready
  obtain ⟨after, run, post⟩ := (parse_parameters_present_empty entry _ _ _ _ _ _ _ _ _ _ _ _ input).run entry ⟨w.post.pc, rfl⟩
  exact ⟨initial, after, ⟨entry, w, w.run.trans run, post, H, domain, parameter_present_ready ready input post⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
