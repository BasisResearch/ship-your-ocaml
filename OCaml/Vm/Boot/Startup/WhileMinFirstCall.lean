import OCaml.Vm.Boot.Startup.AllocatorBootstrap
import OCaml.Vm.Boot.Startup.CamlMainPrefix
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup OCaml.Vm.Primitives

/-- Native stack value after main's sixteen-byte caller frame. -/
def camlMainStack : BitVec 64 := BitVec.ofNat 64 (Layout.sym_stack_top - 16)

noncomputable def resetArgv (initial : Config) : BitVec 64 :=
  bytesVal .ld (read8 (Vsa.Densify.fillZero initial).σ.mem Layout.sym_embedded_argv)

/-- The source reset supplies x9; crt0/main's full register frame retains it. -/
theorem ResetCamlMainWitness.savedReg {initial after : Config}
    (w : ResetCamlMainWitness initial after) : gprGet after.σ 9 = some 0#64 :=
  (w.post.frame .x9 (by decide) (by decide)).trans (w.reset.gprs 9 (by decide) (by decide))

/-- Discharge the runtime prefix's complete input from the ELF's own execution. -/
theorem ResetCamlMainWitness.prefixInput {initial after : Config}
    (w : ResetCamlMainWitness initial after) :
    CamlMainPrefixInput camlMainStack 0x80001df0#64 0#64 (resetArgv initial) after where
  toLeafInput := w.post.toCrtCamlMainPost.leaf (reset_image_fillZero whileMin_elf w.reset)
  stack := w.post.stack
  savedReg := w.savedReg
  argvReg := w.post.argv
  returnSlot := by constructor <;> decide
  savedSlot := by constructor <;> decide
  imageOutside := by constructor <;> simp only [camlMainLog, OutLRange] <;> decide

/-- Closed actual-reset witness extended through caml_main's first call.
The callee body and remaining startup execution are subsequent obligations. -/
structure ResetDomainWitness (initial atMain atDomain : Config) : Prop where
  main : ResetCamlMainWitness initial atMain
  run : Steps (Vsa.Densify.fillZero initial) atDomain
  post : WriteRegistersPost [2, 9, 1] (camlMainLog camlMainStack 0x80001df0#64 0#64)
    atMain (BitVec.ofNat 64 Layout.sym_caml_init_domain) (resetArgv initial)
    [(1, jal_80004d94_call.link), (2, camlMainStack - 112#64),
     (9, resetArgv initial), (10, resetArgv initial)] atDomain

theorem reset_domain_exists : ∃ initial atMain atDomain, ResetDomainWitness initial atMain atDomain := by
  obtain ⟨initial, atMain, main⟩ := reset_caml_main_exists
  obtain ⟨atDomain, run, post⟩ :=
    (caml_main_domain atMain _ _ _ _ main.prefixInput).run atMain ⟨main.post.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, main, main.post.run.trans run, post⟩
end OCaml.Vm.Boot.WhileMinElfParse
