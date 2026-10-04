import OCaml.Vm.Boot.Startup.NativeReturnPair
import OCaml.Vm.Boot.Startup.StatCheckedTestRows
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def statCheckedReturnInput (sp p : BitVec 64) : GRegs := [(2, nativeStack sp 32), (10, p)]
def statCheckedReturnRegs (sp ra s0 p : BitVec 64) : GRegs := [(2, sp), (8, s0), (1, ra), (10, p)]

structure StatCheckedReturnInput (sp ra s0 p oldra : BitVec 64) (c : Config) : Prop extends LeafInput oldra c where
  frame : NativeFrame sp 32
  regs : GHolds c.σ (statCheckedReturnInput sp p)
  nonzero : p ≠ 0#64
  savedRa : bytesT c.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra
  savedS0 : bytesT c.σ.mem (nativeFrameBase sp 32 + 16) 8 = s0
  returnAligned : ra.toNat % 4 = 0

def statCheckedTestInput (sp oldra p : BitVec 64) : GRegs :=
  [(2, nativeStack sp 32), (10, p), (1, oldra)]

theorem statCheckedTest_input {sp ra s0 p oldra c} (h : StatCheckedReturnInput sp ra s0 p oldra c) :
    BlockInput caml_stat_allocXbb8cTSeg 0x8000bb8c#64 (statCheckedTestInput sp oldra p) [] c where
  good := h.good
  minstret := h.minstret
  regs := ⟨gholds_lookup (n := 2) _ h.regs (by rfl), gholds_lookup (n := 10) _ h.regs (by rfl), h.raReg, trivial⟩
  keys := by change KeysOK [2, 10, 1]; decide
  shape := by change ChainOK _ [2, 10, 1] _; decide
  tick := h.tick
  facts := by
    have code := statCheckedReturn_code h.image
    chain_facts code with "Vsa.Sim.Code.caml_stat_alloc_at_"
    change (p != 0#64) = true
    exact bne_iff_ne.mpr h.nonzero

/-- Successful checked allocation branches into the shared caller-restoration
protocol and returns the fresh pointer. -/
theorem stat_checked_return (c : Config) (sp ra s0 p oldra : BitVec 64)
    (h : StatCheckedReturnInput sp ra s0 p oldra c) :
    FnSummary 0x8000bb8c#64 (fun d => d = c)
      (WriteRegistersPost [1, 8, 2] [] c ra p (statCheckedReturnRegs sp ra s0 p)) := by
  have test : FnSummary 0x8000bb8c#64 (fun d => d = c)
      (WriteRegistersPost [] [] c NativePairKind.checked.entry p (statCheckedTestInput sp oldra p)) := by
    apply registers_of_blocks h.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (statCheckedTest_input h))
    · rfl
    · rfl
    · rfl
    · rfl
    · decide
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨checked, run1, tested⟩ := test.run c ⟨pc, rfl⟩
  have input : NativePairInput .checked sp ra s0 p oldra checked := {
    toLeafInput := tested.leaf (by rfl) h.aligned
    frame := h.frame
    regs := ⟨gholds_lookup (n := 2) _ tested.regs (by rfl),
      gholds_lookup (n := 10) _ tested.regs (by rfl), trivial⟩
    savedRa := by rw [tested.memory]; exact h.savedRa
    savedS0 := by rw [tested.memory]; exact h.savedS0
    returnAligned := h.returnAligned }
  obtain ⟨after, run2, returned⟩ := (native_return_pair checked .checked sp ra s0 p oldra input).run checked ⟨tested.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_readonly_post tested returned⟩
end OCaml.Vm.Boot.Startup
