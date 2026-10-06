import OCaml.Vm.Boot.Startup.StatFreeNormalized
import OCaml.Vm.Boot.Startup.StatFreeImage
import OCaml.Vm.Boot.Startup.FreeWrapRows
import OCaml.Vm.Boot.Startup.FreeWrapImage
import OCaml.Vm.Boot.Startup.FreeNullRows
import OCaml.Vm.Boot.Startup.FreeNullImage
import OCaml.Vm.Boot.Startup.FreeNullReturnRows
import OCaml.Vm.Boot.Startup.FreeNullReturnImage
import OCaml.Vm.Boot.Startup.GetenvPrefix
import OCaml.Vm.Boot.Startup.StrncmpReturn
import OCaml.Vm.Primitives.Boundary
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Nonpooling `caml_stat_free` is a tail jump to `free`. -/
def statFreeDirect : List BBlock := caml_stat_freeXbb98TSeg ++ caml_stat_freeXbbc4Seg

theorem statFree_input {c : Config} {ra p : BitVec 64} (h : LeafInput ra c) (regs : GHolds c.σ [(10, p)])
    (pool : LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8)) :
    BlockInput statFreeDirect 0x8000bb98#64 [(10, p)] [List.replicate 8 0#8] c where
  good := h.good
  minstret := h.minstret
  regs := regs
  keys := by change KeysOK [10]; decide
  shape := by change ChainOK _ [10] _; decide
  tick := h.tick
  facts := by
    have code := statFree_code h.image
    chain_facts code with "Vsa.Sim.Code.caml_stat_free_at_"
    · apply ReadWindow.ld (x := BitVec.ofNat 64 Layout.sym_pool) (by constructor <;> decide) rfl
      · simp only [statfree_line_8000bb98, statfree_line_8000bb9c, eaddrM, srcVal, lookupG, runGM, stepGM,
          eraseG, wvalM, Option.getD_some, ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
        decide
      exact pool
    · rfl

theorem stat_free_dispatch (c : Config) (ra p : BitVec 64) (h : LeafInput ra c) (regs : GHolds c.σ [(10, p)])
    (pool : LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8)) :
    FnSummary 0x8000bb98#64 (fun d => d = c)
      (BoundaryPost [15, 14] c ra (BitVec.ofNat 64 Vsa.Alloc.freeEntry) [(15, p + 0#64), (14, 0#64), (10, p)]) := by
  apply boundary_of_blocks h (block_summary _ _ _ _ _ (statFree_input h regs pool))
  · rfl
  · rfl
  · intro σ pins
    have a4 := gholds_lookup (n := 14) _ pins (by rfl)
    change gprGet σ 14 = some (bytesVal .ld (List.replicate 8 0#8)) at a4
    rw [show bytesVal .ld (List.replicate 8 0#8) = 0#64 from by decide] at a4
    have a5 := gholds_lookup (n := 15) _ pins (by rfl)
    change gprGet σ 15 = some (p + 0#64) at a5
    exact ⟨a5, a4, gholds_lookup (n := 10) _ pins (by rfl), trivial⟩
  · decide
  · decide

/-- The `free` wrapper passes its pointer and the reentrancy structure to `_free_r`. -/
theorem free_wrap (c : Config) (ra p : BitVec 64) (h : LeafInput ra c) (regs : GHolds c.σ [(10, p)]) :
    FnSummary (BitVec.ofNat 64 Vsa.Alloc.freeEntry) (fun d => d = c)
      (BoundaryPost [11, 10] c ra 0x80044868#64 [(10, getenvReent c), (11, p)]) := by
  apply boundary_of_blocks h (block_summary _ _ _ _ _ (show
      BlockInput freeX75a8Seg (BitVec.ofNat 64 Vsa.Alloc.freeEntry) [(10, p)] [read8 c.σ.mem allocatorImpureAddr] c from {
    good := h.good
    minstret := h.minstret
    regs := regs
    keys := by change KeysOK [10]; decide
    shape := by change ChainOK _ [10] _; decide
    tick := h.tick
    facts := by
      have code := freeWrap_code h.image
      chain_facts code with "Vsa.Sim.Code.free_at_"
      exact (show ReadWindow (BitVec.ofNat 64 allocatorImpureAddr) 8 from by constructor <;> decide).ld
        rfl rfl (read8_pins _ _) }))
  · rfl
  · rfl
  · intro σ pins
    have a0 := gholds_lookup (n := 10) _ pins (by rfl)
    change gprGet σ 10 = some (bytesVal .ld (read8 c.σ.mem allocatorImpureAddr)) at a0
    rw [read8_value] at a0
    have a1 := gholds_lookup (n := 11) _ pins (by rfl)
    change gprGet σ 11 = some (p + 0#64) at a1
    rw [BitVec.add_zero] at a1
    exact ⟨a0, a1, trivial⟩
  · decide
  · decide

/-- `_free_r` returns at once for a null pointer. -/
theorem free_r_null (c : Config) (ra reent : BitVec 64) (h : LeafInput ra c)
    (regs : GHolds c.σ [(10, reent), (11, 0#64)]) :
    FnSummary 0x80044868#64 (fun d => d = c)
      (WriteRegistersPost [] [] c ra reent [(10, reent), (11, 0#64), (1, ra)]) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (free_rX4868TSeg ++ free_rX4998Seg) 0x80044868#64
        [(10, reent), (11, 0#64), (1, ra)] [] c from {
      good := h.good
      minstret := h.minstret
      regs := ⟨regs.1, regs.2.1, h.raReg, trivial⟩
      keys := by change KeysOK [10, 11, 1]; decide
      shape := by change ChainOK _ [10, 11, 1] _; decide
      tick := h.tick
      facts := by
        have code := freeNull_code h.image
        chain_facts code with "Vsa.Sim.Code._free_r_at_"
        · rfl
        · change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [ret_tgt ra h.aligned]
          exact h.aligned }))
  · rfl
  · exact ret_tgt ra h.aligned
  · rfl
  · rfl
  · decide

/-- `caml_stat_free(NULL)` without pooling returns at once, touching no memory. -/
theorem stat_free_null (c : Config) (ra : BitVec 64) (h : LeafInput ra c) (regs : GHolds c.σ [(10, 0#64)])
    (pool : LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8)) :
    FnSummary 0x8000bb98#64 (fun d => d = c)
      (RegistersPost [15, 14, 11, 10] c.σ.mem c ra (getenvReent c)
        [(1, ra), (10, getenvReent c), (11, 0#64), (15, 0#64), (14, 0#64)]) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, run1, dispatched⟩ := (stat_free_dispatch c ra 0#64 h regs pool).run c ⟨pc, rfl⟩
  have leafA : LeafInput ra a := dispatched.toLeafInput
  have sameA : a.σ.mem = c.σ.mem := dispatched.memory
  obtain ⟨b, run2, wrapped⟩ := (free_wrap a ra 0#64 leafA ⟨gholds_lookup (n := 10) _ dispatched.regs (by rfl), trivial⟩).run
    a ⟨dispatched.pc, rfl⟩
  have reent : getenvReent a = getenvReent c := by unfold getenvReent; rw [sameA]
  obtain ⟨after, run3, post⟩ := (free_r_null b ra (getenvReent a) wrapped.toLeafInput
    wrapped.regs).run b ⟨wrapped.pc, rfl⟩
  rw [reent] at post
  have effects := dispatched.then_write (wrapped.then_write post.toEffectPost)
  have p15 : gprGet a.σ 15 = some (0#64 + 0#64) := gholds_lookup (n := 15) _ dispatched.regs (by rfl)
  rw [BitVec.add_zero] at p15
  exact ⟨after, run1.trans (run2.trans run3), ⟨effects, gholds_lookup (n := 1) _ post.regs (by rfl),
    gholds_lookup (n := 10) _ post.regs (by rfl), gholds_lookup (n := 11) _ post.regs (by rfl),
    (post.frame .x15 (by decide) (by decide)).trans ((wrapped.frame .x15 (by decide) (by decide)).trans p15),
    (post.frame .x14 (by decide) (by decide)).trans ((wrapped.frame .x14 (by decide) (by decide)).trans
      (gholds_lookup (n := 14) _ dispatched.regs (by rfl))),
    trivial⟩⟩
end OCaml.Vm.Boot.Startup
