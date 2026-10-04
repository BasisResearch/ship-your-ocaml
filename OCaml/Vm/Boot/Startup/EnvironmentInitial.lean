import OCaml.Vm.Boot.Startup.EnvironmentHistory
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The environment installed by main, with embedded bytes identified by the
pinned ELF loader certificate. Total reads suffice for the native search. -/
structure EmbeddedEnvironment (c : Config) : Prop where
  global : bytesT c.σ.mem Layout.sym_environ 8 = BitVec.ofNat 64 WhileMinImage.envArray
  byte : ∀ a, Layout.sym_embedded_env ≤ a → a < WhileMinImage.envValue + 1 →
    (c.σ.mem[a]?).getD 0 = (WhileMinImage.initialMem[a]?).getD 0

theorem EmbeddedEnvironment.frame {before after} (h : EmbeddedEnvironment before)
    (frame : EnvironmentFrame before after) : EmbeddedEnvironment after where
  global := (frame.word _ (fun i hi => Or.inl ⟨by omega, by omega⟩)).trans h.global
  byte := fun a lo hi => (frame.byte a (Or.inr ⟨lo, hi⟩)).trans (h.byte a lo hi)
end OCaml.Vm.Boot.Startup
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup OCaml.Vm.Primitives

/-- Loader memory and densification give the same total bytes at reset. -/
theorem reset_total_byte {initial : Config} (reset : ElfResetReady elf initial) (a : Nat) :
    ((Vsa.Densify.fillZero initial).σ.mem[a]?).getD 0 = (WhileMinImage.initialMem[a]?).getD 0 := by
  change ((Vsa.Densify.fillZeroMem initial.σ.mem)[a]?).getD 0 = _
  have same := Vsa.Densify.memEqv_fillZeroMem initial.σ.mem a
  simp only [Std.ExtHashMap.get?_eq_getElem?] at same
  rw [← same, reset.memory, whileMin_elf.memory]

theorem ResetCamlMainWitness.environment {initial atMain : Config}
    (w : ResetCamlMainWitness initial atMain) : EmbeddedEnvironment atMain := by
  constructor
  · rw [w.post.memory]
    have split : mainWrites 0x8000003c#64 (read8 (Vsa.Densify.fillZero initial).σ.mem Layout.sym_embedded_env) =
        [(Layout.sym_stack_top - 8, 8, 0x8000003c#64)] ++
        [(Layout.sym_environ, 8, bytesVal .ld (read8 (Vsa.Densify.fillZero initial).σ.mem Layout.sym_embedded_env))] := rfl
    rw [split, writeLog_append, word_writeLog, read8_value]
    apply Eq.trans (word_observed _ (fun i _ => reset_total_byte w.reset _))
    exact WhileMinImage.env_header
  · intro a lo hi
    rw [w.post.memory, writeLog_out _ _ _ ?_, clearWords_above _ _ _ _ ?_]
    · exact reset_total_byte w.reset a
    · have bound : Layout.sym_bss_start + 8 * bssWords ≤ Layout.sym_embedded_env := by decide
      omega
    · change (a < Layout.sym_stack_top - 8 ∨ Layout.sym_stack_top ≤ a) ∧
        (a < Layout.sym_environ ∨ Layout.sym_environ + 8 ≤ a) ∧ True
      have bound : WhileMinImage.envValue + 1 ≤ Layout.sym_stack_top - 8 ∧
          Layout.sym_environ + 8 ≤ Layout.sym_embedded_env := by decide
      exact ⟨Or.inl (by omega), Or.inr (by omega), trivial⟩

theorem ResetParameterEntry.environment {initial entry} (w : ResetParameterEntry initial entry) :
    EmbeddedEnvironment entry :=
  w.domain.witness.tables.third.first.published.allocation.before.request.tables.allocation.before.alloc.domain.main.environment.frame w.environment_frame
end OCaml.Vm.Boot.WhileMinElfParse
