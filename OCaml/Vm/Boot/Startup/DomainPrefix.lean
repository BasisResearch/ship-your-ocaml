import OCaml.Vm.Boot.Startup.DomainNormalized
import OCaml.Vm.Boot.Startup.DomainCallInterface
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.NativeStack
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Fresh-domain test and first allocation prefix from the generated CFG. -/
def domainDirect : List BBlock := caml_init_domainXa8ccTSeg ++ caml_init_domainXa8dcSeg

def domainInput (sp ra : BitVec 64) : GRegs := [(2, sp), (1, ra)]
def domainRegs (sp ra : BitVec 64) : GRegs :=
  [(10, 928#64), (2, sp - 16#64), (15, 0#64), (1, ra)]

structure DomainPrefixInput (sp ra : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  stack : gprGet c.σ 2 = some sp
  fresh : LPins8 c.σ.mem Layout.sym_Caml_state (List.replicate 8 0#8)
  returnSlot : WriteWindow (sp - 8#64) 8
  imageOutside : ImageOutside (savedRaLog sp ra)

theorem domain_prefix_input {c : Config} {sp ra : BitVec 64} (h : DomainPrefixInput sp ra c) :
    BlockInput domainDirect (BitVec.ofNat 64 Layout.sym_caml_init_domain)
      (domainInput sp ra) [List.replicate 8 0#8] c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.stack, h.raReg, True.intro⟩
  keys := by change KeysOK [2, 1]; decide
  shape := by change ChainOK _ [2, 1] domainDirect; decide
  tick := h.tick
  facts := by
    have code := domain_code h.image
    chain_facts code with "Vsa.Sim.Code.caml_init_domain_at_"
    · apply ReadWindow.ld (x := BitVec.ofNat 64 Layout.sym_Caml_state)
        (by constructor <;> decide) rfl rfl
      exact h.fresh
    · change guardB bop.BEQ (bytesVal .ld (List.replicate 8 0#8)) 0#64 = true
      decide
    · apply h.returnSlot.sd rfl
      change sp + 18446744073709551600#64 + 8#64 = sp - 8#64
      simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem domain_prefix_log (sp ra : BitVec 64) :
    (evalBlocks domainDirect (SegEvalState.init (domainInput sp ra) [List.replicate 8 0#8])).log =
      savedRaLog sp ra := by
  simp only [domainDirect, ← domainSave_eq, domainSave, caml_init_domainXa8ccTSeg,
    evalBlocks, evalBlock, SegEvalState.init, List.nil_append, List.cons_append,
    domain_line_8002a8cc, domain_line_8002a8d0, domainInput, wlogM, wentryM, widthOfM, stepGM, stepLdsM, runGM,
    wvalM, eaddrM, srcVal, lookupG, eraseG, Nat.reduceEqDiff, ite_true, ite_false,
    Option.getD_some, Nat.reduceAdd]
  have address : sp + Functions.sign_extend (m := 64) (0xff0#12) +
      Functions.sign_extend (m := 64) (8#12) = sp - 8#64 := by
    change sp + 18446744073709551600#64 + 8#64 = sp - 8#64
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rw [address]
  rfl

/-- The fresh-domain branch prepares the source's 928-byte allocation request. -/
theorem domain_prefix (c : Config) (sp ra : BitVec 64) (h : DomainPrefixInput sp ra c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_init_domain) (fun d => d = c)
      (WriteRegistersPost [15, 2, 10] (savedRaLog sp ra) c jal_8002a8e8_call.pc 928#64
        (domainRegs sp ra)) := by
  apply registers_of_blocks h.image h.imageOutside
    (block_summary _ _ _ _ _ (domain_prefix_input h))
  · exact domain_prefix_log sp ra
  · rfl
  · change [(10, 928#64), (2, sp + 18446744073709551600#64), (15, bytesVal .ld (List.replicate 8 0#8)), (1, ra)] = _
    have zero : bytesVal .ld (List.replicate 8 0#8) = 0#64 := by decide
    rw [zero]
    simp [domainRegs, BitVec.sub_eq_add_neg]
  · rfl
  · decide

theorem domain_allocate (c : Config) (sp ra : BitVec 64) (h : DomainPrefixInput sp ra c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_init_domain) (fun d => d = c)
      (WriteRegistersPost [15, 2, 10, 1] (savedRaLog sp ra) c
        (BitVec.ofNat 64 Layout.sym_caml_stat_alloc_noexc) 928#64
        [(1, jal_8002a8e8_call.link), (2, sp - 16#64), (10, 928#64)]) := by
  apply summary_bind (domain_prefix c sp ra h) (fun _ post => post.pc)
  intro mid post
  have regs : GHolds mid.σ [(2, sp - 16#64), (10, 928#64)] :=
    holds_project post.regs (by simp [domainRegs, lookupG])
  have call := call_registers_summary jal_8002a8e8_call_shape jal_8002a8e8_call_decode mid
    (jal_8002a8e8_call_pins post.image) post.good post.image post.tick post.minstret _ regs
    (by change KeysOK [2, 10]; decide) (by simp [KeysAvoidRa, keysG]) (by rfl)
  apply call.weaken (fun _ eq => eq)
  intro after called
  exact prefix_call_post post called
end OCaml.Vm.Boot.Startup
