import OCaml.Vm.Sim.PendingRootFacts

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- Complete no-pending-action return through the generated function CFG. -/
theorem pending_root_summary {sp ra value : BitVec 64} {c : Config} (h : PendingRootInput sp ra value c) :
    FnSummary 0x8000d6ec#64 (fun start => start = c) (PendingRootPost sp ra value c) := by
  obtain ⟨mem, memEq⟩ : ∃ mem : Std.ExtHashMap Nat (BitVec 8),
      mem = writeLog c.σ.mem (pendingRootLog sp ra value) := ⟨_, rfl⟩
  have saved : bytesT mem (pendingRootRa sp).toNat 8 = ra := by rw [memEq]; exact pending_root_return_word h
  have summary := block_summary _ _ _ _ _ (pending_root_input h memEq)
  apply summary.weaken (fun _ eq => eq)
  intro after post
  have memory : after.σ.mem = writeLog c.σ.mem (pendingRootLog sp ra value) := by
    simpa only [pendingRootLoads, pending_root_log] using post.memory
  have regs := post.regs
  simp only [pendingRootLoads, pending_root_regs] at regs
  have target : evalBlocksPC 0x8000d6ec#64 (SegEvalState.init (pendingRootInitial sp ra value)
      (pendingRootLoads c sp mem)) pendingRootBlocks = ra := by
    change Sail.BitVec.update (bytesVal .ld (read8 mem (pendingRootRa sp).toNat) + sign_extend (m := 64) (0#12)) 0 0#1 = ra
    rw [read8_value, saved]
    exact ret_tgt ra h.aligned
  refine ⟨post.good, image_of_writeLog h.image h.imageOutside memory, post.tick,
    post.pc.trans (congrArg some target), gholds_lookup _ regs (by rfl),
    gholds_lookup _ regs (by rfl), memory, post.output, ?_⟩
  intro r outside
  apply post.frame r
  · intro q member
    exact outside q (List.mem_append_right _ member)
  · intro n member
    have written : ∀ n ∈ wrChain pendingRootBlocks, gprReg n ∈ [Register.x1, Register.x2, Register.x15] ++ noiseRegs := by decide
    exact outside _ (written n member)

end OCaml.Vm.Sim
