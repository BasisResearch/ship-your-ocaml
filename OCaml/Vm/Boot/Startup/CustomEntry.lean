import OCaml.Vm.Boot.Startup.StartupAuxReset
import OCaml.Vm.Boot.Startup.CamlLocaleReady
import OCaml.Vm.Boot.Startup.CamlCustomCallInterface
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

/-- Actual reset execution at the custom-operation initializer, after the
successful caller branch, remaining native saves and locale initialization. -/
structure ResetCustomEntry (initial entry : Config) where
  source : Config
  auxiliary : ResetStartupAuxReturned initial source
  returned : Config
  locale : WriteRegistersPost [1]
    (camlLocaleLog camlMainStack (vsaReg source 8) (vsaReg source 18) (vsaReg source 19) (vsaReg source 20))
    source jal_80004dcc_call.link 1#64
    (camlLocaleRegs camlMainStack (vsaReg source 8) (vsaReg source 18) (vsaReg source 19) (vsaReg source 20)) returned
  call : RegistersPost [1] returned.σ.mem returned jal_80004dd0_call.target 1#64
    [(1, jal_80004dd0_call.link), (2, parameterStack), (10, 1#64)] entry
  run : Steps (Vsa.Densify.fillZero initial) entry
  ready : ∃ H, (firstDomainPtr.toNat, 928) ∈ H ∧
    RuntimeReady H (startupAllocatorCredits - 192) parameterStack jal_80004dd0_call.link entry

theorem ResetCustomEntry.reset {initial entry} (w : ResetCustomEntry initial entry) :
    ElfResetReady elf initial := w.auxiliary.reset

theorem reset_custom_entry_exists : ∃ initial entry, Nonempty (ResetCustomEntry initial entry) := by
  obtain ⟨initial, source, ⟨w⟩⟩ := reset_startup_aux_returned_exists
  obtain ⟨H, domain, ready⟩ := w.ready
  have reg (n : Nat) (lo : 0 < n) (hi : n ≤ 31) : gprGet source.σ n = some (vsaReg source n) :=
    library_gpr ready.platform lo hi rfl
  have input : CamlLocaleInput camlMainStack jal_80004da4_call.link
      (vsaReg source 8) (vsaReg source 18) (vsaReg source 19) (vsaReg source 20) source := {
    toLeafInput := ready.toLeafInput
    frame := by constructor <;> decide
    regs := ⟨ready.raReg, w.post.result, ready.stack, reg 8 (by decide) (by decide),
      reg 20 (by decide) (by decide), reg 18 (by decide) (by decide), reg 19 (by decide) (by decide), trivial⟩ }
  obtain ⟨returned, run1, locale⟩ := (caml_locale source _ _ _ _ _ _ input).run source ⟨w.post.pc, rfl⟩
  have ready' := caml_locale_ready (sp := camlMainStack) ready input.frame locale
  have regs : GHolds returned.σ [(2, parameterStack), (10, 1#64)] := ⟨ready'.stack, locale.result, trivial⟩
  obtain ⟨entry, run2, call⟩ := (call_registers_summary jal_80004dd0_call_shape jal_80004dd0_call_decode returned
    (jal_80004dd0_call_pins ready'.image) ready'.good ready'.image ready'.tick ready'.minstret _ regs
    (by change KeysOK [2, 10]; decide) (by change ∀ n ∈ [2, 10], n ≠ 1; decide) (by rfl)).run returned ⟨locale.pc, rfl⟩
  have ready'' : RuntimeReady H (startupAllocatorCredits - 192) parameterStack jal_80004dd0_call.link entry := by
    apply ready'.effect call (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ call.regs (by rfl))
      (gholds_lookup (n := 1) _ call.regs (by rfl)) (by decide)
    · intro a ha; rfl
    · intro a ha; rfl
    · intro a ha; exact ha
  exact ⟨initial, entry, ⟨source, w, returned, locale, call, w.run.trans (run1.trans run2), H, domain, ready''⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
