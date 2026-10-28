import OCaml.Vm.Primitives.Channel.OpenRepr
import OCaml.Vm.Gc.ChannelRefs

/-! Counted channel representation, separate from `ChanAt`'s data layout.
The physical accounting predicate is supplied by the named custom-call
obligation. These records are the boundary witness to carry through the VM
invariant; the existing `WorldRepr` alone does not supply them. -/

namespace OCaml.Vm
open OCaml.Bytecode Vsa.Machine Vsa.Sim
set_option autoImplicit false

/-- Enumerating valid indices and reading them recovers the original list. -/
theorem map_range_getD {α : Type} (xs : List α) (fallback : α) :
    (List.range xs.length).map (fun id => xs[id]?.getD fallback) = xs := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range,
    List.getElem?_eq_getElem h₂, Option.getD_some]

/-- Physical reference counts at the represented channel places. Unlike
`ChanAt`, this observes the four-byte `refcount` field, without modular wrap. -/
structure ChannelRefsRepr (c : Config) (cp : ChanPlace) (w : World) : Prop where
  refs : ∀ id ch, w.chans[id]? = some ch →
    ∃ a, cp id = some a ∧ Gc.chanRefs c.σ.mem a = ch.refs

/-- Total refcounts of a fully placed list of ids. -/
theorem refcountSum_filterMap {m : Std.ExtHashMap Nat (BitVec 8)} {cp : ChanPlace}
    (ids : List Nat) (refs : Nat → Nat)
    (placed : ∀ id ∈ ids, ∃ a, cp id = some a ∧ Gc.chanRefs m a = refs id) :
    Gc.refcountSum m (ids.filterMap cp) = (ids.map refs).sum := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    obtain ⟨a, at_, count⟩ := placed id List.mem_cons_self
    have tail := ih (fun j hj => placed j (List.mem_cons_of_mem _ hj))
    simp only [List.filterMap_cons, at_, Gc.refcountSum, List.map_cons, List.sum_cons] at *
    rw [count, tail]

/-- The physical total agrees with the model's represented refcount total. -/
theorem ChannelRefsRepr.sum {c : Config} {cp : ChanPlace} {w : World}
    (h : ChannelRefsRepr c cp w) :
    Gc.refcountSum c.σ.mem (Gc.placedChannels cp w.chans.length) = w.customs := by
  let atId : Nat → Chan := fun id => w.chans[id]?.getD ⟨0, false, [], [], 0, 0, 0⟩
  have all : (List.range w.chans.length).map atId = w.chans := map_range_getD _ _
  have placed : ∀ id ∈ (List.range w.chans.length).reverse,
      ∃ a, cp id = some a ∧ Gc.chanRefs c.σ.mem a = (atId id).refs := by
    intro id hid
    have lt : id < w.chans.length := by simpa using hid
    have at_ := List.getElem?_eq_getElem lt
    obtain ⟨a, hp, hr⟩ := h.refs id _ at_
    exact ⟨a, hp, by simpa only [atId, at_, Option.getD_some] using hr⟩
  rw [Gc.placedChannels, refcountSum_filterMap _ (fun id => (atId id).refs) placed]
  rw [List.map_reverse, List.sum_reverse]
  change ((List.range w.chans.length).map (Chan.refs ∘ atId)).sum = _
  rw [← List.map_map, all]
  rfl

/-- A VM-boundary witness: physical custom accounting equals the model's
refcount total, and the real opened list has that same total. -/
structure ChannelCustomsRepr (Customs : Config → Nat → Prop) (c : Config)
    (cp : ChanPlace) (w : World) : Prop where
  references : ChannelRefsRepr c cp w
  opened : Gc.OpenChannelList c.σ.mem (Gc.placedChannels cp w.chans.length)
  physical : Customs c w.customs

/-- Console effects may change channel data while retaining every reference
count and the number of records. These are model observations, not a physical
accounting assumption. -/
structure ChannelRefsSame (w w' : World) : Prop where
  length : w'.chans.length = w.chans.length
  refs : ∀ (id : Nat) (ch ch' : Chan), w.chans[id]? = some ch → w'.chans[id]? = some ch' → ch'.refs = ch.refs

theorem ChannelRefsSame.of_chans {w w' : World} (same : w'.chans = w.chans) :
    ChannelRefsSame w w' := by
  refine ⟨by rw [same], ?_⟩
  intro id ch ch' at_ at'
  rw [same, at_] at at'
  cases at'; rfl

theorem ChannelRefsSame.trans {w w' w'' : World} (first : ChannelRefsSame w w')
    (second : ChannelRefsSame w' w'') : ChannelRefsSame w w'' := by
  refine ⟨second.length.trans first.length, ?_⟩
  intro id ch ch'' at_ at''
  have bound : id < w'.chans.length := by
    rw [first.length]; exact (List.getElem?_eq_some_iff.mp at_).1
  have at' := List.getElem?_eq_getElem bound
  exact (second.refs id _ _ at' at'').trans (first.refs id _ _ at_ at')

theorem ChannelRefsSame.set {w : World} {id : Nat} {ch ch' : Chan}
    (at_ : w.chans[id]? = some ch) (refs : ch'.refs = ch.refs) :
    ChannelRefsSame w (w.setChan id ch') := by
  refine ⟨List.length_set, ?_⟩
  intro j old new oldAt newAt
  by_cases eq : j = id
  · subst j
    rw [at_] at oldAt; cases oldAt
    have bound := (List.getElem?_eq_some_iff.mp at_).1
    change (w.chans.set id ch')[id]? = some new at newAt
    rw [List.getElem?_set_self bound] at newAt
    cases newAt; exact refs
  · change (w.chans.set id ch')[j]? = some new at newAt
    rw [List.getElem?_set_ne (Ne.symm eq), oldAt] at newAt
    cases newAt; rfl

theorem ChannelRefsSame.customs {w w' : World} (same : ChannelRefsSame w w') :
    w'.customs = w.customs := by
  have maps : w'.chans.map Chan.refs = w.chans.map Chan.refs := by
    apply List.ext_getElem (by simp [same.length])
    intro i hi hi'
    simp only [List.getElem_map]
    exact same.refs i _ _ (List.getElem?_eq_getElem (by simpa using hi'))
      (List.getElem?_eq_getElem (by simpa using hi))
  exact congrArg List.sum maps

/-- Update after an OS effect, retaining the original channel's refs. -/
theorem ChannelRefsSame.set_after {w mid : World} {id : Nat} {ch : Chan}
    (same : ChannelRefsSame w mid) (at_ : w.chans[id]? = some ch)
    (new : Chan) (refs : new.refs = ch.refs) : ChannelRefsSame w (mid.setChan id new) := by
  have bound : id < mid.chans.length := by
    rw [same.length]; exact (List.getElem?_eq_some_iff.mp at_).1
  have midAt := List.getElem?_eq_getElem bound
  exact same.trans (.set (ch' := new) midAt (refs.trans (same.refs id _ _ at_ midAt).symm))

/-- Retarget the complete count witness from length and per-id refs alone. -/
theorem ChannelCustomsRepr.of_refs_same {Customs : Config → Nat → Prop} {c : Config}
    {cp : ChanPlace} {w w' : World} (counts : ChannelCustomsRepr Customs c cp w)
    (same : ChannelRefsSame w w') : ChannelCustomsRepr Customs c cp w' := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · intro id ch' at'
    have bound : id < w.chans.length := by
      rw [← same.length]; exact (List.getElem?_eq_some_iff.mp at').1
    have at_ := List.getElem?_eq_getElem bound
    obtain ⟨a, placed, count⟩ := counts.references.refs id _ at_
    exact ⟨a, placed, count.trans (same.refs id _ _ at_ at').symm⟩
  · simpa only [same.length] using counts.opened
  · rw [same.customs]; exact counts.physical

theorem ChannelCustomsRepr.boundary {Customs : Config → Nat → Prop} {c : Config}
    {cp : ChanPlace} {w : World} (h : ChannelCustomsRepr Customs c cp w) :
    Gc.ChannelCustomsAt Customs c (Gc.placedChannels cp w.chans.length) w.customs 0 :=
  ⟨h.physical, ⟨h.opened, by simpa using h.references.sum⟩⟩

/-- The intended counted loop invariant. Projection preserves the existing
VM relation while producers are migrated; `VmReprAt` alone cannot supply the
additional physical evidence. -/
structure CountedVmReprAt (Customs : Config → Nat → Prop) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) : Prop extends VmReprAt P s c pl cp sp high where
  counts : ChannelCustomsRepr Customs c cp s.world

/-- The initial empty world, conditional only on the runtime's physical zero
witness and the actual opened-list head. -/
theorem ChannelCustomsRepr.empty {Customs : Config → Nat → Prop} {c : Config}
    {cp : ChanPlace} {w : World} (empty : w.chans = []) (physical : Customs c 0)
    (head : bytesT c.σ.mem Layout.sym_caml_all_opened_channels 8 = 0#64) :
    ChannelCustomsRepr Customs c cp w := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · intro id ch at_
    rw [empty] at at_
    simp at at_
  · simpa [Gc.placedChannels, empty] using (Gc.ChannelCustomsAt.of_null physical head).refs.opened
  · simpa [World.customs, empty] using physical

/-- Reference counts at the new channel placement. The observations of old
records are shared with the ordinary payload frame. -/
theorem ChannelRefsRepr.open {c d : Config} {cp : ChanPlace} {w : World} {rec : Nat} {ch : Chan}
    (before : ChannelRefsRepr c cp w)
    (kept : ∀ id old a, w.chans[id]? = some old → cp id = some a →
      Gc.chanRefs d.σ.mem a = Gc.chanRefs c.σ.mem a)
    (new : Gc.chanRefs d.σ.mem rec = ch.refs) :
    ChannelRefsRepr d (cp.put w.chans.length rec) {w with chans := w.chans ++ [ch]} := by
  constructor
  intro id old at_
  rcases Primitives.chans_append_cases at_ with ⟨at_, lt⟩ | ⟨rfl, rfl⟩
  · obtain ⟨a, placed, count⟩ := before.refs id old at_
    exact ⟨a, by rw [ChanPlace.put_other cp (Nat.ne_of_lt lt)]; exact placed,
      (kept id old a at_ placed).trans count⟩
  · exact ⟨rec, ChanPlace.put_self cp _ _, new⟩

/-- The opening's physical transition and represented references meet at the
VM boundary. The pre-allocation reference increment is never used as physical
custom readiness. -/
theorem ChannelCustomsRepr.open {Customs : Config → Nat → Prop} {c d : Config}
    {cp : ChanPlace} {w : World} {rec : Nat} {ch : Chan}
    (before : ChannelCustomsRepr Customs c cp w)
    (step : Gc.CustomCountStep Customs c d 1) (one : ch.refs = 1)
    (kept : ∀ id old a, w.chans[id]? = some old → cp id = some a →
      Gc.chanRefs d.σ.mem a = Gc.chanRefs c.σ.mem a)
    (new : Gc.chanRefs d.σ.mem rec = ch.refs)
    (opened : Gc.OpenChannelList d.σ.mem
      (Gc.placedChannels (cp.put w.chans.length rec) (w.chans ++ [ch]).length)) :
    ChannelCustomsRepr Customs d (cp.put w.chans.length rec) {w with chans := w.chans ++ [ch]} := by
  refine ⟨before.references.open kept new, opened, ?_⟩
  simpa [World.customs, List.map_append, List.sum_append, one] using step.count before.physical

end OCaml.Vm
