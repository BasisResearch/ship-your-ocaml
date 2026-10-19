import OCaml.Vm.Boot.Startup.PolicyTestNormalized
import OCaml.Vm.Boot.Startup.PolicyTestImage
import OCaml.Vm.Boot.Startup.PolicyBestNormalized
import OCaml.Vm.Boot.Startup.PolicyBestImage
import OCaml.Vm.Boot.Startup.PolicyStoreNormalized
import OCaml.Vm.Boot.Startup.PolicyStoreImage
import OCaml.Vm.Boot.Startup.PageAddSteps
import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.AllocatorRun
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_set_allocation_policy(2): the best-fit free-list functions. A leaf
whose every value is a link-time constant. -/

/-- Policy 2 is neither next-fit (0) nor first-fit (1). -/
theorem policy_test (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, 2#64)]) :
    FnSummary 0x8000759c#64 (fun e => e = c) (WriteRegistersPost [15] [] c 0x80007624#64 2#64
      [(15, 1#64), (10, 2#64)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (caml_set_allocation_policyX759cFSeg ++ caml_set_allocation_policyX75a0TSeg)
        0x8000759c#64 [(10, 2#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := policyTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_set_allocation_policy_at_"
        all_goals decide }))
  · rfl
  · decide
  · decide
  · rfl
  · decide

/-- The best-fit functions. -/
def bestFitRegs : GRegs :=
  [(15, 0x80006fac#64), (14, 0x8000629c#64), (13, 0x80006d6c#64), (12, 0x80006258#64), (11, 0x800070b4#64),
    (16, 0x800061a0#64), (17, 0x800073ac#64), (10, 2#64)]

theorem policy_best (c : Config) (ra v : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, v)]) :
    FnSummary 0x80007624#64 (fun e => e = c) (WriteRegistersPost [10, 17, 16, 11, 12, 13, 14, 15] [] c
      0x800075e0#64 2#64 bestFitRegs) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_set_allocation_policyX7624Seg 0x80007624#64 [(10, v)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := policyBest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_set_allocation_policy_at_" }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_set_allocation_policyX7624Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal,
      lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, policybest_line_80007624, policybest_line_80007628, policybest_line_8000762c, policybest_line_80007630, policybest_line_80007634, policybest_line_80007638, policybest_line_8000763c, policybest_line_80007640, policybest_line_80007644, policybest_line_80007648, policybest_line_8000764c, policybest_line_80007650, policybest_line_80007654, policybest_line_80007658, policybest_line_8000765c] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      trivial⟩
  · rfl
  · decide

local macro "psk" : tactic => `(tactic| simp only [policystore_line_800075e0, policystore_line_800075e4, policystore_line_800075e8, policystore_line_800075ec, policystore_line_800075f0, policystore_line_800075f4, policystore_line_800075f8, policystore_line_800075fc, policystore_line_80007600, policystore_line_80007604, policystore_line_80007608, policystore_line_8000760c, policystore_line_80007610, policystore_line_80007614, policystore_line_80007618, policystore_line_8000761c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of])

/-- The policy and the free-list functions it selects. -/
def policyLog : List WEntry :=
  [(0x80064848, 8, 2#64), (0x800649d0, 8, 0x800070b4#64), (0x800649e8, 8, 0x800073ac#64), (0x800649d8, 8, 0x80006258#64),
    (0x800649e0, 8, 0x800061a0#64), (0x800649c8, 8, 0x80006d6c#64), (0x800649c0, 8, 0x8000629c#64),
    (0x800649b8, 8, 0x80006fac#64)]

theorem policy_store (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ ((1, ra) :: bestFitRegs)) :
    FnSummary 0x800075e0#64 (fun e => e = c) (WriteRegistersPost [6, 10, 11, 12, 13, 14] policyLog c ra 0x80064600#64
      [(1, ra), (6, 0x800645e0#64), (10, 0x80064600#64), (11, 0x800645f8#64), (12, 0x80064608#64),
        (13, 0x80064610#64), (14, 0x80064618#64)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> simp only [policyLog, OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_set_allocation_policyX75e0Seg 0x800075e0#64
        ((1, ra) :: bestFitRegs) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [1, 15, 14, 13, 12, 11, 16, 17, 10]; decide
      shape := by change ChainOK _ [1, 15, 14, 13, 12, 11, 16, 17, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := policyStore_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_set_allocation_policy_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 0x80064848) 8 by constructor <;> decide).sd rfl (by psk; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 0x800649d0) 8 by constructor <;> decide).sd rfl (by psk; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 0x800649e8) 8 by constructor <;> decide).sd rfl (by psk; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 0x800649d8) 8 by constructor <;> decide).sd rfl (by psk; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 0x800649e0) 8 by constructor <;> decide).sd rfl (by psk; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 0x800649c8) 8 by constructor <;> decide).sd rfl (by psk; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 0x800649c0) 8 by constructor <;> decide).sd rfl (by psk; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 0x800649b8) 8 by constructor <;> decide).sd rfl (by psk; decide)
        · change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [ret_tgt ra leaf.aligned]
          exact leaf.aligned }))
  · simp only [caml_set_allocation_policyX75e0Seg, bestFitRegs, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
      wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, imm20Of, policystore_line_800075e0, policystore_line_800075e4, policystore_line_800075e8, policystore_line_800075ec, policystore_line_800075f0, policystore_line_800075f4, policystore_line_800075f8, policystore_line_800075fc, policystore_line_80007600, policystore_line_80007604, policystore_line_80007608, policystore_line_8000760c, policystore_line_80007610, policystore_line_80007614, policystore_line_80007618, policystore_line_8000761c]
    decide
  · change Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [ret_tgt ra leaf.aligned]
  · intro σ pins
    simp only [caml_set_allocation_policyX75e0Seg, bestFitRegs, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, policystore_line_800075e0, policystore_line_800075e4, policystore_line_800075e8, policystore_line_800075ec, policystore_line_800075f0, policystore_line_800075f4, policystore_line_800075f8, policystore_line_800075fc, policystore_line_80007600, policystore_line_80007604, policystore_line_80007608, policystore_line_8000760c, policystore_line_80007610, policystore_line_80007614, policystore_line_80007618, policystore_line_8000761c] at pins
    exact ⟨gholds_lookup (n := 1) _ pins rfl, gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), trivial⟩
  · rfl
  · decide

/-- The policy global and the free-list function pointers. -/
def policyWindows : List W := [⟨0x80064848, 0x80064850⟩, ⟨0x800649b8, 0x800649f0⟩]

theorem policyWindows_pins (pin : Nat × BitVec 8) (member : pin ∈ VsaIris.Sym.allocText) : OutW policyWindows pin.1 := by
  have source := allocator_sources pin member
  unfold AllocatorByteSource at source
  simp only [OutW, policyWindows, and_true]
  split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr] at * <;> omega

theorem policyWindows_foot {H : List (Nat × Nat)} {a : Nat} (foot : vsaFoot H a) : OutW policyWindows a := by
  simp only [OutW, policyWindows, and_true]
  rcases foot with global | ⟨above, _, _⟩
  · unfold allocGlobal InRange at global; omega
  · unfold heapStart at above; omega

/-- caml_set_allocation_policy(2) returned. -/
structure PolicySet (H : List (Nat × Nat)) (capacity : Nat) (sp ra : BitVec 64) (before after : Config) : Prop where
  pc : PCAt ra after
  ready : RuntimeReady H capacity sp ra after
  memory : after.σ.mem = writeLog before.σ.mem policyLog
  saved : ∀ k ∈ abiSaved, gprGet after.σ k = gprGet before.σ k

theorem set_allocation_policy (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (sp ra : BitVec 64)
    (pc : PCAt 0x8000759c#64 c) (ready : RuntimeReady H capacity sp ra c) (policy : gprGet c.σ 10 = some 2#64) :
    ∃ d, Steps c d ∧ PolicySet H capacity sp ra c d := by
  obtain ⟨d1, run1, p1⟩ := (policy_test c ra ready.toLeafInput ⟨policy, trivial⟩).run c ⟨pc, rfl⟩
  have k1 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [15]) : gprGet d1.σ r = gprGet c.σ r :=
    p1.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready1 := ready.window_log (windows := []) p1 (by decide) (by simp only [keysG]; decide) (by decide)
    ((k1 2 (by decide) (by decide) (by decide)).trans ready.stack) ((k1 1 (by decide) (by decide) (by decide)).trans
      ready.raReg) ready.aligned trivial (fun _ _ => trivial) trivial trivial (fun _ _ => trivial)
  obtain ⟨d2, run2, p2⟩ := (policy_best d1 ra 2#64 ready1.toLeafInput ⟨gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩).run
    d1 ⟨p1.pc, rfl⟩
  have k2 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [10, 17, 16, 11, 12, 13, 14, 15]) :
      gprGet d2.σ r = gprGet d1.σ r :=
    p2.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready2 := ready1.window_log (windows := []) p2 (by decide) (by simp only [keysG, bestFitRegs]; decide)
    (by decide) ((k2 2 (by decide) (by decide) (by decide)).trans ready1.stack)
    ((k2 1 (by decide) (by decide) (by decide)).trans ready1.raReg) ready1.aligned trivial (fun _ _ => trivial) trivial
    trivial (fun _ _ => trivial)
  obtain ⟨d3, run3, p3⟩ := (policy_store d2 ra ready2.toLeafInput
    ⟨ready2.raReg, gholds_lookup (n := 15) _ p2.regs rfl, gholds_lookup (n := 14) _ p2.regs rfl,
      gholds_lookup (n := 13) _ p2.regs rfl, gholds_lookup (n := 12) _ p2.regs rfl,
      gholds_lookup (n := 11) _ p2.regs rfl, gholds_lookup (n := 16) _ p2.regs rfl,
      gholds_lookup (n := 17) _ p2.regs rfl, gholds_lookup (n := 10) _ p2.regs rfl, trivial⟩).run d2 ⟨p2.pc, rfl⟩
  have k3 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [6, 10, 11, 12, 13, 14]) : gprGet d3.σ r = gprGet d2.σ r :=
    p3.toEffectPost.gpr_frame (by decide) r lo hi out
  refine ⟨d3, run1.trans (run2.trans run3), {
    pc := p3.pc
    ready := ready2.window_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
      ((k3 2 (by decide) (by decide) (by decide)).trans ready2.stack) (gholds_lookup (n := 1) _ p3.regs rfl)
      ready.aligned (by simp only [policyLog, policyWindows, LogInW, InsideW]; decide) policyWindows_pins
      (by simp only [OutWRange, policyWindows]; decide) (by simp only [OutWRange, policyWindows]; decide)
      (fun _ foot => policyWindows_foot foot)
    memory := by rw [p3.memory, p2.memory, p1.memory]; rfl
    saved := fun k member => by
      have range : 1 ≤ k ∧ k ≤ 31 := by simp [abiSaved] at member; omega
      have out (L : List Nat) (low : ∀ m ∈ L, m ∉ abiSaved) : k ∉ L := fun mem => low k mem member
      rw [k3 k range.1 range.2 (out _ (by decide)), k2 k range.1 range.2 (out _ (by decide)),
        k1 k range.1 range.2 (out _ (by decide))] }⟩
end OCaml.Vm.Boot.Startup
