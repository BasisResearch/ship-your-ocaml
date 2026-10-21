import OCaml.Vm.Boot.Startup.InitStack
import OCaml.Vm.Boot.Startup.InitGcReset
import OCaml.Vm.Boot.Startup.CamlInitStackNormalized
import OCaml.Vm.Boot.Startup.CamlInitStackImage
import OCaml.Vm.Boot.Startup.CamlInitStackCallInterface
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_main's `caml_init_stack(caml_init_max_stack_wsz)` after caml_init_gc. -/

local macro "cis" : tactic => `(tactic| simp only [camlinitstack_line_80004e70, camlinitstack_line_80004e74, eaddrM,
  srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd,
  imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- Load `caml_init_max_stack_wsz` (parameter word 5) and call caml_init_stack. -/
theorem caml_init_stack_arg (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (data : ∀ a, GcDataByte a → (c.σ.mem[a]?).getD 0 = (WhileMinImage.initialMem[a]?).getD 0) :
    FnSummary 0x80004e70#64 (fun e => e = c) (WriteRegistersPost [10] [] c jal_80004e78_call.pc (gcParamWord 5)
      [(10, gcParamWord 5)]) := by
  have word := gcParam_of_data data 5 (by decide)
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_mainX4e70Seg 0x80004e70#64 [] [gcLoad c.σ.mem 5] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := trivial
      keys := by change KeysOK []; decide
      shape := by change ChainOK _ [] _; decide
      tick := leaf.tick
      facts := by
        have code := camlInitStack_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_main_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 (gcParamAddr + 8 * 5)) 8 by
            constructor <;> simp only [BitVec.toNat_ofNat, gcParamAddr, Layout.sym_tohost] <;> omega).ld rfl
              (by cis; decide) (read8_pins _ _) }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_mainX4e70Seg, evalBlocks, evalBlock, SegEvalState.init, camlinitstack_line_80004e70,
      camlinitstack_line_80004e74, runGM, stepGM, eraseG, wvalM, ite_true, ite_false, Nat.reduceEqDiff, imm20Of,
      ldsRunM, stepLdsM, List.headD_cons, List.tail_cons] at pins
    exact ⟨gholds_lookup_eq pins rfl word, trivial⟩
  · rfl
  · decide

theorem caml_init_stack_call (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (data : ∀ a, GcDataByte a → (c.σ.mem[a]?).getD 0 = (WhileMinImage.initialMem[a]?).getD 0) :
    FnSummary 0x80004e70#64 (fun e => e = c) (WriteRegistersPost ([10] ++ [1]) [] c jal_80004e78_call.target
      (gcParamWord 5) ((1, jal_80004e78_call.link) :: [(10, gcParamWord 5)])) :=
  block_then_call c jal_80004e78_call_shape jal_80004e78_call_decode (fun _ h => jal_80004e78_call_pins h)
    (caml_init_stack_arg c ra leaf data) (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives Startup

/-- caml_init_stack returned in the reset run, with the page table caml_init_gc left. -/
structure InitStackReset (H : List (Nat × Nat)) (capacity : Nat) (ra s0 s1 s2 mx p : BitVec 64) (before after : Config) :
    Prop where
  done : InitStackDone H capacity ra s0 s1 s2 mx p before after
  table : ∃ ent, GcTableAt ((p.toNat, 32768) :: H) after.σ.mem ent

/-- The reset run through caml_init_gc and caml_init_stack: back in caml_main
with the interpreter stack allocated and recorded in the domain record. -/
theorem reset_init_stack_reset_exists :
    ∃ initial after, Steps (Vsa.Densify.fillZero initial) after ∧
      ∃ H s0 s1 s2 mx p before, InitStackReset H
        (startupAllocatorCredits - 656 - initGcCredits - 32768)
        jal_80004e78_call.link s0 s1 s2 mx p before after := by
  obtain ⟨initial, sections, ⟨w⟩⟩ := reset_read_sections_exists
  obtain ⟨t1, t2, t3, dom⟩ := reset_domain_kept initial sections w
  obtain ⟨a, run1, A, gcA⟩ := reset_init_gc_call w dom
  obtain ⟨Hfinal, d, run2, D⟩ := caml_init_gc a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A
  have data : ∀ x, GcDataByte x → (d.σ.mem[x]?).getD 0 = (WhileMinImage.initialMem[x]?).getD 0 :=
    fun x hx => (D.low x (GcLowKeep.of_range (Or.inl hx))).trans (gcA.data x hx)
  have link : jal_80004e6c_call.link = 0x80004e70#64 := by decide
  have pcD : PCAt 0x80004e70#64 d := by have := D.pc; rwa [link] at this
  obtain ⟨e, run3, P⟩ := (caml_init_stack_call d jal_80004e6c_call.link D.ready.toLeafInput data).run d ⟨pcD, rfl⟩
  have gP := GprsSame.of_post P (by decide)
  have credits : startupAllocatorCredits - 656 - initGcCredits = (startupAllocatorCredits - 656 - initGcCredits - 32768) + 32768 := by
    decide
  have readyD := D.ready
  rw [credits] at readyD
  have readyE := readyD.stack_log P (by decide) (by simp only [keysG]; decide) (by decide)
    (gP.get (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ D.regs rfl))
    (gholds_lookup (n := 1) _ P.regs rfl) (by decide) initStack_frame (by simp only [LogInW])
  obtain ⟨pre, hpre⟩ := D.extends_
  have IS : InitStackCall Hfinal (startupAllocatorCredits - 656 - initGcCredits - 32768) 32768 jal_80004e78_call.link
      3#64 argvPtr (vsaReg w.attempt.opened.call.atRetry 18) (gcParamWord 5) e := {
    pc := by have := P.pc; rwa [jal_80004e78_call_target] at this
    regs := ⟨gP.get (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ D.regs rfl),
      gP.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ D.regs rfl),
      gP.get (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ D.regs rfl),
      gholds_lookup (n := 1) _ P.regs rfl,
      gP.get (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ D.regs rfl),
      gholds_lookup (n := 10) _ P.regs rfl, trivial⟩
    ready := readyE
    charged := ⟨by decide, by decide⟩
    domainOwned := by rw [hpre]; exact List.mem_append_right _ A.domainOwned
    domain := readyE.domainWord
    quiet := lpins8_observed A.quiet fun i hi => by
      rw [show e.σ.mem = d.σ.mem from P.memory]
      exact D.low _ (GcLowKeep.of_range (Or.inr (Or.inl ⟨by unfold Layout.sym_caml_verb_gc; omega,
        by unfold Layout.sym_caml_verb_gc; omega⟩))) }
  obtain ⟨p, f, run4, S⟩ := caml_init_stack e _ _ _ _ _ _ _ _ IS
  obtain ⟨ent, T⟩ := D.table
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  have table : GcTableAt ((p.toNat, 32768) :: Hfinal) f.σ.mem ent := (T.agree fun x inT => by
    obtain ⟨below, foot⟩ := T.table.out inT
    have ta := T.table.apartDomain
    have th := T.table.high
    have hP : pageTable = 0x800684b8 := rfl
    have hS : heapStart = 0x8007d140 := rfl
    rw [dom] at ta
    rw [hS] at th
    rw [S.kept x below foot (by
        simp only [initStackFieldsLog, initStackCells, List.map, OutL, domainField, dom, camlMaxStackSizeAddr, and_true]
        rcases inT with ⟨lo, hi⟩ | ⟨lo, hi⟩
        · rw [hP] at lo hi; omega
        · omega), show e.σ.mem = d.σ.mem from P.memory]).cons _
  exact ⟨initial, f, run1.trans (run2.trans (run3.trans run4)), _, _, _, _, _, _, _, ⟨S, ent, table⟩⟩

theorem reset_init_stack_returned_exists :
    ∃ initial after, Steps (Vsa.Densify.fillZero initial) after ∧
      ∃ H cap ra s0 s1 s2 mx p before, InitStackDone H cap ra s0 s1 s2 mx p before after := by
  obtain ⟨initial, after, run, H, s0, s1, s2, mx, p, before, R⟩ := reset_init_stack_reset_exists
  exact ⟨initial, after, run, H, _, _, s0, s1, s2, mx, p, before, R.done⟩
end OCaml.Vm.Boot.WhileMinElfParse
