import OCaml.Vm.Boot.Startup.PageModifyHashNormalized
import OCaml.Vm.Boot.Startup.PageModifyHashImage
import OCaml.Vm.Boot.Startup.PageModifyHashTailNormalized
import OCaml.Vm.Boot.Startup.PageModifyHashTailImage
import OCaml.Vm.Boot.Startup.PageModifySlotNormalized
import OCaml.Vm.Boot.Startup.PageModifySlotImage
import OCaml.Vm.Boot.Startup.LinearChain
import OCaml.Vm.Boot.Startup.PageHash
import OCaml.Vm.Boot.Startup.ReadSectionsSteps
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_page_table_modify's hash: `(page >> 12) * HASH_FACTOR >> shift`.
The native shift-add chain is evaluated over coefficients (`linRun_sound`);
the factor comes out as `0x9E3779B97F4A7C16`. -/

/-- The page number. -/
def pageNumber (page : BitVec 64) : BitVec 64 := page >>> 12

/-- OCaml's `HASH_FACTOR`. -/
abbrev hashFactor : BitVec 64 := 11400714819323198486#64

theorem srli_page (page : BitVec 64) (a : MInstr) (imm : a.imm = 12#12) :
    Sail.shift_bits_right page (Sail.BitVec.extractLsb (shamtOf a) 5 0) = pageNumber page := by
  rw [shamtOf, imm]
  simp only [Sail.shift_bits_right, pageNumber, BitVec.ushiftRight_eq']
  rfl

theorem hash_coefs_a :
    linRun (caml_page_table_modifyXadf0Seg.flatMap (·.body)).tail [(12, 1#64)] =
      some [(14, 2805824235320#64), (15, 70145605883#64), (12, 1#64)] := by decide

theorem hash_coefs_b :
    linRun (caml_page_table_modifyXae38Seg.flatMap (·.body)) [(14, 2805824235320#64), (15, 70145605883#64), (12, 1#64)] =
      some [(15, hashFactor), (14, 22985312135732255#64), (12, 1#64)] := by decide

/-- The shift-add chain: `a5 = HASH_FACTOR * (page >> 12)`. -/
theorem page_hash_chain (c : Config) (ra page : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, page)]) :
    FnSummary 0x8000adf0#64 (fun e => e = c) (BoundaryPost [12, 14, 15] c ra 0x8000ae70#64
      [(15, hashFactor * pageNumber page), (12, pageNumber page)]) := by
  apply boundary_of_blocks leaf
    (block_summary _ _ _ _ _ (show BlockInput (caml_page_table_modifyXadf0Seg ++ caml_page_table_modifyXae38Seg)
        0x8000adf0#64 [(8, page)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8]; decide
      shape := by change ChainOK _ [8] _; decide
      tick := leaf.tick
      facts := by
        have code := pageModifyHash_code leaf.image
        have code2 := pageModifyHashTail_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_page_table_modify_at_" }))
  · rfl
  · rfl
  · intro σ pins
    have start : LinHolds (pageNumber page) [(12, 1#64)]
        (stepGM (mkLine 0x8000adf0#64 0x00c45613#32) [(8, page)] []) := by
      intro n k hn
      simp only [lookupG] at hn
      split at hn
      · rename_i e; subst e
        simp only [Option.some.injEq] at hn; subst hn
        rw [pagemodifyhash_line_8000adf0]
        simp only [stepGM, wvalM, lookupG, srcVal, ite_true, Option.getD_some]
        rw [srli_page _ _ rfl, BitVec.one_mul]
      · simp at hn
    have afterA := linRun_sound (y := pageNumber page) [] start hash_coefs_a
    have afterB := linRun_sound (y := pageNumber page) [] afterA hash_coefs_b
    have run : (evalBlocks (caml_page_table_modifyXadf0Seg ++ caml_page_table_modifyXae38Seg)
        (SegEvalState.init [(8, page)] [])).regs =
        runGM (caml_page_table_modifyXae38Seg.flatMap (·.body))
          (runGM ((caml_page_table_modifyXadf0Seg.flatMap (·.body)).tail)
            (stepGM (mkLine 0x8000adf0#64 0x00c45613#32) [(8, page)] []) []) [] := rfl
    rw [run] at pins
    exact ⟨gholds_lookup _ pins (afterB 15 _ rfl), gholds_lookup _ pins (by
      rw [afterB 12 _ rfl, BitVec.one_mul]), trivial⟩
  · decide
  · decide
end OCaml.Vm.Boot.Startup
