import OCaml.Vm.Gc.OldifySlot
import OCaml.Vm.Primitives.Call
import OCaml.Vm.Gc.OldifyBridge

/-! # A `jal caml_oldify_one` site with a slot-level result

Any caller of `caml_oldify_one` (the VM-stack and `ref_table` root loops,
mopup) reaches it through a decoded `jal`. `SlotSite Loaded` names such a
site for a caller whose code image is `Loaded`. `SlotSite.slot` composes the
jump with a `SlotCall` supplied at the jumped-to state, for any route. -/
namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- A decoded `jal caml_oldify_one` in a caller whose code image is `Loaded`. -/
structure SlotSite (Loaded : Std.ExtHashMap Nat (BitVec 8) → Prop) where
  call : CallInstr
  shape : CallShape call
  decode : CallDecode call
  target : call.target = OldifyEntry.pc
  aligned : call.link.toNat % 4 = 0
  pins : ∀ {c : Config}, Loaded c.σ.mem → CallPins call c

namespace SlotSite
variable {Loaded : Std.ExtHashMap Nat (BitVec 8) → Prop} (site : SlotSite Loaded)

/-- The callee's register view: the caller's, with `ra` the site's link. -/
def linked (R : Nat → BitVec 64) (n : Nat) : BitVec 64 := if n = 1 then site.call.link else R n

theorem linked_regs {R : Nat → BitVec 64} {before after : Config}
    (post : SegCallFacts [] (OldifyBridge.carried R) [] site.call.target site.call.link before after) :
    GHolds after.σ (OldifyEntry.regs (site.linked R)) := by
  have holds : GHolds after.σ ((1, site.call.link) :: OldifyBridge.carried R) := ⟨post.ra, post.registers⟩
  apply gholds_select holds
  intro n v member
  simp only [OldifyEntry.regs, OldifyEntry.entryKeys, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

/-- The jump and the callee's slot-level result, from the caller's state. -/
structure Returned (R : Nat → BitVec 64) (copies : List PendingCopy) (pl : Place)
    (before after : Config) : Prop where
  entered : ∃ e copies', SegCallFacts [] (OldifyBridge.carried R) [] site.call.target site.call.link before e ∧
    SlotDone (site.linked R) copies copies' pl e after

/-- **The site's call**, for a `SlotCall` supplied at every jumped-to state. -/
theorem slot {R : Nat → BitVec 64} {copies : List PendingCopy} {pl : Place} {c : Config}
    (code : Loaded c.σ.mem) (good : GoodState c.σ) (tick : c.tick < 2)
    (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (registers : GHolds c.σ (OldifyBridge.carried R))
    (supply : ∀ e, SegCallFacts [] (OldifyBridge.carried R) [] site.call.target site.call.link c e →
      SlotCall (site.linked R) copies pl e) :
    FnSummary site.call.pc (fun d => d = c) (Returned site R copies pl c) := by
  have jump := call_summary site.shape site.decode c (site.pins code) good tick minstret
    (OldifyBridge.carried R) registers
    (by change KeysOK [2,8,9,10,11,18,19,20,21,22,23,24,25]; decide)
    (by change ∀ n ∈ ([2,8,9,10,11,18,19,20,21,22,23,24,25] : List Nat), n ≠ 1; decide)
  constructor
  apply Vsa.Logic.Triple.seq jump.run
  intro entered called
  obtain ⟨copies', summary⟩ := supply entered called
  have pc : PCAt OldifyEntry.pc entered := by simpa only [PCAt, site.target] using called.pc
  obtain ⟨after, run, done⟩ := summary.run entered ⟨pc, rfl⟩
  exact ⟨after, run, ⟨⟨entered, copies', called, done⟩⟩⟩

end SlotSite
end OCaml.Vm.Gc
