import OCaml.Vm.Gc.SlotBridge
import OCaml.Vm.Primitives.IndirectCall

/-! # A `jalr` into `caml_oldify_one` with a slot-level result

The global-root scan calls its `scanning_action` argument (`caml_oldify_one`
during a minor collection) through a register (`jalr s1`).
`IndirectSlotSite Loaded` names such a site for a caller whose code image is
`Loaded`; `IndirectSlotSite.slot` is `SlotSite.slot` for it, given that the
source register holds `caml_oldify_one`'s entry. -/
namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- A decoded `jalr` through one of the carried registers, in a caller whose
code image is `Loaded`. -/
structure IndirectSlotSite (Loaded : Std.ExtHashMap Nat (BitVec 8) → Prop) where
  call : IndirectCallInstr
  shape : IndirectShape call
  decode : IndirectDecode call
  /-- the source register is carried into `caml_oldify_one` -/
  carriedSource : call.source ∈ [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25]
  imm : call.imm = 0#12
  aligned : call.link.toNat % 4 = 0
  pins : ∀ {c : Config}, Loaded c.σ.mem → IndirectPins call c

namespace IndirectSlotSite
variable {Loaded : Std.ExtHashMap Nat (BitVec 8) → Prop} (site : IndirectSlotSite Loaded)

/-- The callee's register view: the caller's, with `ra` the site's link. -/
def linked (R : Nat → BitVec 64) (n : Nat) : BitVec 64 := if n = 1 then site.call.link else R n

theorem linked_regs {R : Nat → BitVec 64} {before after : Config} {target : BitVec 64}
    (post : SegCallFacts [] (OldifyBridge.carried R) [] target site.call.link before after) :
    GHolds after.σ (OldifyEntry.regs (site.linked R)) := by
  have holds : GHolds after.σ ((1, site.call.link) :: OldifyBridge.carried R) := ⟨post.ra, post.registers⟩
  apply gholds_select holds
  intro n v member
  simp only [OldifyEntry.regs, OldifyEntry.entryKeys, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

theorem source_lookup (R : Nat → BitVec 64) :
    lookupG site.call.source (OldifyBridge.carried R) = some (R site.call.source) := by
  have h := site.carriedSource
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl

/-- The jump and the callee's slot-level result, from the caller's state. -/
structure Returned (R : Nat → BitVec 64) (copies : List PendingCopy) (pl : Place)
    (before after : Config) : Prop where
  entered : ∃ e copies', SegCallFacts [] (OldifyBridge.carried R) [] OldifyEntry.pc site.call.link before e ∧
    SlotDone (site.linked R) copies copies' pl e after

/-- **The site's call**, when the source register holds `caml_oldify_one`'s
entry, for a `SlotCall` supplied at every jumped-to state. -/
theorem slot {R : Nat → BitVec 64} {copies : List PendingCopy} {pl : Place} {c : Config}
    (code : Loaded c.σ.mem) (good : GoodState c.σ) (tick : c.tick < 2)
    (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (registers : GHolds c.σ (OldifyBridge.carried R))
    (target : R site.call.source = OldifyEntry.pc)
    (supply : ∀ e, SegCallFacts [] (OldifyBridge.carried R) [] OldifyEntry.pc site.call.link c e →
      SlotCall (site.linked R) copies pl e) :
    FnSummary site.call.pc (fun d => d = c) (Returned site R copies pl c) := by
  have entry : site.call.target OldifyEntry.pc = OldifyEntry.pc := by
    rw [IndirectCallInstr.target, site.imm]
    exact ret_tgt _ (by decide)
  have jump := indirect_summary site.shape site.decode c (site.pins code) good tick minstret
    (OldifyBridge.carried R) registers
    (by change KeysOK [2,8,9,10,11,18,19,20,21,22,23,24,25]; decide)
    (by change ∀ n ∈ [2,8,9,10,11,18,19,20,21,22,23,24,25], n ≠ 1; decide)
    (R site.call.source) (site.source_lookup R) (by rw [target, entry]; decide)
  rw [target, entry] at jump
  constructor
  apply Vsa.Logic.Triple.seq jump.run
  intro entered called
  obtain ⟨copies', summary⟩ := supply entered called
  obtain ⟨after, run, done⟩ := summary.run entered ⟨called.pc, rfl⟩
  exact ⟨after, run, ⟨⟨entered, copies', called, done⟩⟩⟩

end IndirectSlotSite
end OCaml.Vm.Gc
