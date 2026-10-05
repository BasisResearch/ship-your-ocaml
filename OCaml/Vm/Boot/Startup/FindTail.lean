import OCaml.Vm.Boot.Startup.FindRestore
import OCaml.Vm.Boot.Startup.FindUnlock
import OCaml.Vm.Boot.Startup.FindReturn
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

theorem FindReturnSaved.transport {sp ra s1 s2 s3 s5 s6 before after}
    (h : FindReturnSaved sp ra s1 s2 s3 s5 s6 before) (same : after.σ.mem = before.σ.mem) :
    FindReturnSaved sp ra s1 s2 s3 s5 s6 after := by
  constructor <;> rw [same]
  · exact h.caller
  · exact h.saved1
  · exact h.saved2
  · exact h.saved3
  · exact h.saved5
  · exact h.saved6

/-- Release the environment lock, restore the saved registers and return null:
the common end of every unsuccessful search (from 0x800374f4). -/
theorem find_release (c : Config) (sp reent ra s1 s2 s3 s5 s6 oldra : BitVec 64)
    (leaf : LeafInput oldra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findUnlockInput (nativeStack sp 80) reent))
    (saved : FindReturnSaved sp ra s1 s2 s3 s5 s6 c) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x800374f4#64 (fun d => d = c)
      (RegistersPost [10, 1, 9, 18, 19, 21, 22, 2] c.σ.mem c ra 0#64 (findReturnRegs sp ra s1 s2 s3 s5 s6)) := by
  constructor
  intro before input
  obtain ⟨pc, eq⟩ := input
  subst before
  obtain ⟨b, run2, unlocked⟩ := (find_unlock c (nativeStack sp 80) reent oldra leaf regs).run c ⟨pc, rfl⟩
  have same : b.σ.mem = c.σ.mem := unlocked.memory
  have regsB : GHolds b.σ (findReturnInput sp) := ⟨gholds_lookup (n := 2) _ unlocked.regs (by rfl), trivial⟩
  obtain ⟨after, run3, post⟩ := (find_return b sp ra s1 s2 s3 s5 s6 _
    (unlocked.leaf (by rfl) (by decide)) frame regsB (saved.transport same) aligned).run b ⟨unlocked.pc, rfl⟩
  have effect := unlocked.toEffectPost.trans post.toEffectPost
  refine ⟨after, run2.trans run3, ⟨?_, post.regs⟩⟩
  exact { effect.widen (writes' := [10, 1, 9, 18, 19, 21, 22, 2]) (by decide) with
    memory := post.memory.trans same }

/-- The full not-found tail restores s4, releases the lock, restores the
remaining saved registers and returns null to the original caller. -/
theorem find_tail (c : Config) (sp reent ra s1 s2 s3 s4 s5 s6 oldra : BitVec 64)
    (leaf : LeafInput oldra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findRestoreInput sp reent))
    (saved4 : bytesT c.σ.mem (nativeFrameBase sp 80 + 32) 8 = s4)
    (saved : FindReturnSaved sp ra s1 s2 s3 s5 s6 c) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8003756c#64 (fun d => d = c)
      (RegistersPost [20, 10, 1, 9, 18, 19, 21, 22, 2] c.σ.mem c ra 0#64
        (findReturnRegs sp ra s1 s2 s3 s5 s6 ++ [(20, s4)])) := by
  constructor
  intro before input
  obtain ⟨pc, eq⟩ := input
  subst before
  obtain ⟨a, run1, restored⟩ := (find_restore c sp reent s4 oldra leaf frame regs saved4).run c ⟨pc, rfl⟩
  have leafA : LeafInput oldra a :=
    ⟨restored.good, restored.image, restored.minstret,
      (restored.frame .x1 (by decide) (by decide)).trans leaf.raReg, leaf.aligned, restored.tick⟩
  have regsA : GHolds a.σ (findUnlockInput (nativeStack sp 80) reent) :=
    ⟨gholds_lookup (n := 21) _ restored.regs (by rfl),
      gholds_lookup (n := 2) _ restored.regs (by rfl), trivial⟩
  have same : a.σ.mem = c.σ.mem := restored.memory
  obtain ⟨after, run2, post⟩ := (find_release a sp reent ra s1 s2 s3 s5 s6 oldra leafA frame regsA
    (saved.transport same) aligned).run a ⟨restored.pc, rfl⟩
  have effect := restored.toEffectPost.trans post.toEffectPost
  refine ⟨after, run1.trans run2, ⟨?_, ?_⟩⟩
  · exact { effect.widen (writes' := [20, 10, 1, 9, 18, 19, 21, 22, 2]) (by decide) with
      memory := post.memory.trans same }
  · apply (gholds_append _ _).mpr
    refine ⟨post.regs, ?_, trivial⟩
    exact (post.frame .x20 (by decide) (by decide)).trans (gholds_lookup (n := 20) _ restored.regs (by rfl))
end OCaml.Vm.Boot.Startup
