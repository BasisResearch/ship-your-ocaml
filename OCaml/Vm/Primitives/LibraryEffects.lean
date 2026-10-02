import OCaml.Vm.Primitives.Effects
import OCaml.Vm.Primitives.LibraryFrame

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable

/-- The complete generated frame preserves every nonwritten ABI register. -/
theorem EffectPost.gpr_frame {writes mem before after pc value}
    (post : EffectPost writes mem before pc value after) (keys : KeysOK writes)
    (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ writes) :
    gpr after n = gpr before n := by
  apply gprGet_of_frame n lower upper (gpr_avoids_noise n (by omega) lower)
  · intro m hm
    have bounds := keys m hm
    exact gprReg_beq_false m (by omega) n (by omega) bounds.1 lower
      (fun e => unwritten (e ▸ hm))
  · intro r noise outside
    exact post.frame r (fun m hm => by
      have ne := outside m hm
      exact fun eq => by rw [eq, beq_self_eq_true] at ne; contradiction) noise

/-- Convert a generated register frame into the library's total observation. -/
theorem EffectPost.observed_gpr {live writes mem before after pc value}
    (post : EffectPost writes mem before pc value after) (keys : KeysOK writes)
    (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ writes) :
    (vsaModel live).reg after n = (vsaModel live).reg before n := by
  have agree := post.gpr_frame keys n lower upper unwritten
  change gprGet after.σ n = gprGet before.σ n at agree
  change vsaReg after n = vsaReg before n
  rw [vsaReg_gpr (by change n ≠ 32; omega), vsaReg_gpr (by change n ≠ 32; omega), agree]

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
    · have frame := post.toEffectPost.gpr_frame keys n lower upper written
      change gprGet after.σ n = gprGet before.σ n at frame
      rw [frame]
      exact pre.gpr n lower upper
  · intro a ha
    rw [post.memory]
    exact writeLog_present _ _ _ (pre.live a ha)
  · rw [post.frame _ (fun n _ => by
      have h := gprReg_htif_payload n
      exact fun eq => by rw [eq, beq_self_eq_true] at h; contradiction) (by decide)]
    exact pre.htifIdle

/-- Read-only library cells depend only on their register and byte observations. -/
theorem readonly_transport {live before after ro text}
    (h : VsaIris.ROHolds (vsaModel live) before ro text)
    (registers : ∀ p ∈ ro, (vsaModel live).reg after p.1 = (vsaModel live).reg before p.1)
    (memory : Vsa.Densify.MemEqv after.σ.mem before.σ.mem) :
    VsaIris.ROHolds (vsaModel live) after ro text :=
  ⟨fun p hp => (registers p hp).trans (h.1 p hp),
   fun p hp => (memory p.1).trans (h.2 p hp)⟩

/-- Stack or nursery stores outside a library's pinned bytes preserve its
read-only precondition; the scalar ABI check protects the global pointer. -/
theorem EffectPost.readOnly_log {live writes log text before after pc value}
    (post : WritePost writes log before pc value after) (keys : KeysOK writes)
    (gp : 3 ∉ writes)
    (readOnly : VsaIris.ROHolds (vsaModel live) before VsaIris.MallocFast.roR text)
    (outside : ∀ p ∈ text, OutL log p.1) :
    VsaIris.ROHolds (vsaModel live) after VsaIris.MallocFast.roR text := by
  constructor
  · intro p hp
    have eq : p = (3, VsaIris.MallocFast.gpV) := List.mem_singleton.mp hp
    subst p
    exact (post.observed_gpr keys 3 (by decide) (by decide) gp).trans
      (readOnly.1 _ hp)
  · intro p hp
    have prior := readOnly.2 p hp
    change (after.σ.mem[p.1]?).getD 0 = p.2
    rw [post.memory, writeLog_out _ _ _ (outside p hp)]
    exact prior

end OCaml.Vm.Primitives
