import OCaml.Vm.Primitives.Effects
import OCaml.Vm.Primitives.LibraryFrame

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable

/-- A generated write certificate retains the library invariant when its
symbolic output covers every written register. Memory writes preserve byte
presence, and the complete frame preserves the idle HTIF counter. -/
theorem RegistersPost.vsaOk {live writes log before after pc value regs}
    (post : WriteRegistersPost writes log before pc value regs after)
    (pre : VsaOk live before) (keys : KeysOK writes)
    (cover : ∀ n ∈ writes, n ∈ keysG regs) : VsaOk live after := by
  refine ⟨post.good, post.tick, ?_, ?_, ?_⟩
  · intro n lower upper
    by_cases written : n ∈ writes
    · obtain ⟨v, hv⟩ := lookupG_of_mem (cover n written)
      rw [gholds_lookup _ post.regs hv]
      rfl
    · have frame : gprGet after.σ n = gprGet before.σ n := by
        apply gprGet_of_frame n lower upper (gpr_avoids_noise n (by omega) lower)
        · intro m hm
          have bounds := keys m hm
          exact gprReg_beq_false m (by omega) n (by omega) bounds.1 lower
            (fun e => written (e ▸ hm))
        · intro r noise outside
          exact post.frame r (fun m hm => by
            have ne := outside m hm
            exact fun eq => by rw [eq, beq_self_eq_true] at ne; contradiction) noise
      rw [frame]
      exact pre.gpr n lower upper
  · intro a ha
    rw [post.memory]
    exact writeLog_present _ _ _ (pre.live a ha)
  · rw [post.frame _ (fun n _ => by
      have h := gprReg_htif_payload n
      exact fun eq => by rw [eq, beq_self_eq_true] at h; contradiction) (by decide)]
    exact pre.htifIdle

end OCaml.Vm.Primitives
