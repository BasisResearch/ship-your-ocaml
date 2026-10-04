import OCaml.Vm.Boot.Startup.CamlParameterCallInterface
import OCaml.Vm.Boot.Startup.DomainHistory
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

/-- The actual reset run at caml_parse_ocamlrunparam entry, with its full
preceding execution history and retained startup contract. -/
structure ResetParameterEntry (initial entry : Config) where
  before : Config
  domain : DomainHistory initial before
  run : Steps (Vsa.Densify.fillZero initial) entry
  post : RegistersPost [1] before.σ.mem before jal_80004d98_call.target (vsaReg before 10)
    [(1, jal_80004d98_call.link), (2, firstMallocStack + 16#64), (10, vsaReg before 10)] entry
  ready : ∃ H, (firstDomainPtr.toNat, 928) ∈ H ∧
    RuntimeReady H (startupAllocatorCredits - 192) (firstMallocStack + 16#64) jal_80004d98_call.link entry

theorem ResetParameterEntry.reset {initial entry} (h : ResetParameterEntry initial entry) : ElfResetReady elf initial :=
  h.domain.reset

/-- The domain return is followed by caml_main's generated parser call. -/
theorem reset_parameter_entry_exists : ∃ initial entry, Nonempty (ResetParameterEntry initial entry) := by
  obtain ⟨initial, before, ⟨history⟩⟩ := domain_history_exists
  obtain ⟨H, domain, ready⟩ := history.witness.ready
  have regs : GHolds before.σ [(2, firstMallocStack + 16#64), (10, vsaReg before 10)] :=
    ⟨ready.stack, library_gpr ready.platform (by decide) (by decide) (by rfl), trivial⟩
  obtain ⟨entry, run, post⟩ :=
    (call_registers_summary jal_80004d98_call_shape jal_80004d98_call_decode before
      (jal_80004d98_call_pins ready.image) ready.good ready.image ready.tick ready.minstret _ regs
      (by change KeysOK [2, 10]; decide) (by change ∀ n ∈ [2, 10], n ≠ 1; decide) (by rfl)).run before
      ⟨history.witness.post.pc, rfl⟩
  have ready' : RuntimeReady H (startupAllocatorCredits - 192) (firstMallocStack + 16#64) jal_80004d98_call.link entry := by
    apply ready.effect post (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup _ post.regs (by rfl)) (gholds_lookup _ post.regs (by rfl)) (by decide)
    · intro a ha; rfl
    · intro a ha; rfl
    · intro a ha; exact ha
  exact ⟨initial, entry, ⟨before, history, history.witness.run.trans run, post, H, domain, ready'⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
