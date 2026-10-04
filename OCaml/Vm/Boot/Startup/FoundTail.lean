import OCaml.Vm.Boot.Startup.FoundMemory
import OCaml.Vm.Boot.Startup.FindFoundReturn
import OCaml.Vm.Boot.Startup.EnvLock
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Complete the successful first-entry lookup tail: record the caller offset,
unlock, restore every saved register and return the value pointer. -/
theorem find_found_tail (c : Config) (sp env reent pointer offset ra oldra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (leaf : LeafInput oldra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findFoundInput sp env reent pointer offset))
    (environment : bytesT c.σ.mem Layout.sym_environ 8 = env) (slot : WriteWindow offset 4)
    (high : sp.toNat ≤ offset.toNat) (outside : ImageOutside (findFoundLog sp pointer offset))
    (saved : FindReturnSaved sp ra s1 s2 s3 s5 s6 c)
    (saved0 : bytesT c.σ.mem (nativeFrameBase sp 80 + 64) 8 = s0)
    (saved4 : bytesT c.σ.mem (nativeFrameBase sp 80 + 32) 8 = s4) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80037520#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10, 14, 15, 18, 19, 20, 21, 22] (findFoundLog sp pointer offset) c ra (pointer + 1#64)
        (findFoundReturnRegs sp ra s0 s1 s2 s3 s4 s5 s6 pointer ++ [(14, env)])) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, run1, prepared⟩ := (find_found c sp env reent pointer offset oldra leaf frame regs environment slot outside).run c ⟨pc, rfl⟩
  have leafA : LeafInput oldra a := ⟨prepared.good, prepared.image, prepared.minstret,
    (prepared.frame .x1 (by decide) (by decide)).trans leaf.raReg, leaf.aligned, prepared.tick⟩
  have parked : GHolds a.σ ((10, reent) :: [(2, nativeStack sp 80), (14, env)]) :=
    ⟨prepared.result, gholds_lookup (n := 2) _ prepared.regs (by rfl),
      gholds_lookup (n := 14) _ prepared.regs (by rfl), trivial⟩
  obtain ⟨b, run2, unlocked⟩ := (scalar_leaf_call jal_80037538_call jal_80037538_call_shape jal_80037538_call_decode
    (envLockValue true) a oldra reent leafA (jal_80037538_call_pins prepared.image)
    [(2, nativeStack sp 80), (14, env)] parked (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide)
    (by simp only [keysG]; decide) (by simp only [keysG]; decide) (by decide)
    (fun state h => env_lock true state _ h)).run a ⟨prepared.pc, rfl⟩
  have savedA := saved.found frame high prepared.memory
  have savedB := savedA.transport unlocked.memory
  have saved0B : bytesT b.σ.mem (nativeFrameBase sp 80 + 64) 8 = s0 := by
    rw [unlocked.memory]
    exact (findFound_word frame high prepared.memory (by decide) (by decide)).trans saved0
  have saved4B : bytesT b.σ.mem (nativeFrameBase sp 80 + 32) 8 = s4 := by
    rw [unlocked.memory]
    exact (findFound_word frame high prepared.memory (by decide) (by decide)).trans saved4
  have savedPointer : bytesT b.σ.mem (nativeFrameBase sp 80 + 8) 8 = pointer := by
    rw [unlocked.memory]
    exact findFound_pointer frame high prepared.memory
  have regsB : GHolds b.σ (findReturnInput sp) :=
    ⟨gholds_lookup (n := 2) _ unlocked.regs (by rfl), trivial⟩
  obtain ⟨after, run3, returned⟩ := (find_found_return b sp ra s0 s1 s2 s3 s4 s5 s6 pointer _
    (unlocked.leaf (by rfl) (by decide)) frame regsB savedB saved0B saved4B savedPointer aligned).run b ⟨unlocked.pc, rfl⟩
  have effects := (prefix_readonly_post prepared (prefix_readonly_post (log := []) unlocked returned)).toEffectPost.widen
    (writes' := [1, 2, 8, 9, 10, 14, 15, 18, 19, 20, 21, 22]) (by decide)
  exact ⟨after, run1.trans (run2.trans run3), ⟨effects, (gholds_append _ _).mpr ⟨returned.regs,
    (returned.frame .x14 (by decide) (by decide)).trans (gholds_lookup (n := 14) _ unlocked.regs (by rfl)), trivial⟩⟩⟩
end OCaml.Vm.Boot.Startup
