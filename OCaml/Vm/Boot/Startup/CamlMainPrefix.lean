import OCaml.Vm.Boot.Startup.CamlMainNormalized
import OCaml.Vm.Boot.Startup.CamlMainCallInterface
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.Write
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def camlMainLog (sp ra saved : BitVec 64) : List WEntry :=
  [((sp - 8#64).toNat, 8, ra), ((sp - 24#64).toNat, 8, saved)]

def camlMainRegs (sp ra argv : BitVec 64) : GRegs :=
  [(9, argv), (2, sp - 112#64), (1, ra), (10, argv)]

structure CamlMainPrefixInput (sp ra saved argv : BitVec 64) (c : Config) : Prop
    extends LeafInput ra c where
  stack : gprGet c.σ 2 = some sp
  savedReg : gprGet c.σ 9 = some saved
  argvReg : gprGet c.σ 10 = some argv
  returnSlot : WriteWindow (sp - 8#64) 8
  savedSlot : WriteWindow (sp - 24#64) 8
  imageOutside : ImageOutside (camlMainLog sp ra saved)

theorem caml_main_prefix_input {c : Config} {sp ra saved argv : BitVec 64}
    (h : CamlMainPrefixInput sp ra saved argv c) :
    BlockInput caml_mainX4d84Seg (BitVec.ofNat 64 Layout.sym_caml_main)
      (caml_mainX4d84L sp ra saved argv) [] c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.stack, h.raReg, h.savedReg, h.argvReg, True.intro⟩
  keys := by change KeysOK [2, 1, 9, 10]; decide
  shape := by change ChainOK _ [2, 1, 9, 10] caml_mainX4d84Seg; decide
  tick := h.tick
  facts := by
    have code := camlMain_code h.image
    chain_facts code with "Vsa.Sim.Code.caml_main_at_"
    · apply h.returnSlot.sd rfl
      change sp + 18446744073709551504#64 + 104#64 = sp - 8#64
      simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    · apply h.savedSlot.sd rfl
      change sp + 18446744073709551504#64 + 88#64 = sp - 24#64
      simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem caml_main_prefix_log (sp ra saved argv : BitVec 64) :
    (evalBlocks caml_mainX4d84Seg (SegEvalState.init (caml_mainX4d84L sp ra saved argv) [])).log = camlMainLog sp ra saved := by
  rw [← camlMainSave_eq]
  simp only [camlMainSave, evalBlocks, evalBlock, SegEvalState.init, List.nil_append,
    caml_mainX4d84L, wlogM, wentryM, widthOfM, stepGM, wvalM,
    eaddrM, srcVal, lookupG, eraseG, Nat.reduceEqDiff, ite_true, ite_false,
    Option.getD_some, Nat.reduceAdd]
  have down : Functions.sign_extend (m := 64) (0xf90#12) = -112#64 := by decide
  have off1 : Functions.sign_extend (m := 64) (0x068#12) = 104#64 := by decide
  have off2 : Functions.sign_extend (m := 64) (0x058#12) = 88#64 := by decide
  have addr1 : sp + Functions.sign_extend (m := 64) (0xf90#12) + Functions.sign_extend (m := 64) (0x068#12) = sp - 8#64 := by
    rw [down, off1]
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have addr2 : sp + Functions.sign_extend (m := 64) (0xf90#12) + Functions.sign_extend (m := 64) (0x058#12) = sp - 24#64 := by
    rw [down, off2]
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rw [addr1, addr2]
  rfl

/-- caml_main saves its two caller words before initializing the domain. -/
theorem caml_main_prefix (c : Config) (sp ra saved argv : BitVec 64)
    (h : CamlMainPrefixInput sp ra saved argv c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_main) (fun d => d = c)
      (WriteRegistersPost [2, 9] (camlMainLog sp ra saved) c jal_80004d94_call.pc argv
        (camlMainRegs sp ra argv)) := by
  apply registers_of_blocks h.image h.imageOutside
    (block_summary _ _ _ _ _ (caml_main_prefix_input h))
  · exact caml_main_prefix_log sp ra saved argv
  · rfl
  · change [(9, argv + 0#64), (2, sp + 18446744073709551504#64), (1, ra), (10, argv)] = _
    simp [camlMainRegs, BitVec.sub_eq_add_neg]
  · rfl
  · decide

/-- The first runtime call, through the real generated JAL and its full ABI interface. -/
theorem caml_main_domain (c : Config) (sp ra saved argv : BitVec 64)
    (h : CamlMainPrefixInput sp ra saved argv c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_main) (fun d => d = c)
      (WriteRegistersPost [2, 9, 1] (camlMainLog sp ra saved) c
        (BitVec.ofNat 64 Layout.sym_caml_init_domain) argv
        [(1, jal_80004d94_call.link), (2, sp - 112#64), (9, argv), (10, argv)]) := by
  apply summary_bind (caml_main_prefix c sp ra saved argv h) (fun _ post => post.pc)
  intro mid post
  have regs : GHolds mid.σ [(2, sp - 112#64), (9, argv), (10, argv)] :=
    holds_project post.regs (by simp [camlMainRegs, lookupG])
  have call := call_registers_summary jal_80004d94_call_shape jal_80004d94_call_decode mid
    (jal_80004d94_call_pins post.image) post.good post.image post.tick post.minstret _ regs
    (by change KeysOK [2, 9, 10]; decide) (by simp [KeysAvoidRa, keysG]) (by rfl)
  apply call.weaken (fun _ eq => eq)
  intro after called
  exact prefix_call_post post called
end OCaml.Vm.Boot.Startup
