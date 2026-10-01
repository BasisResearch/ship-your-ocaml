import OCaml.Vm.Repr

/-! Finite heap witnesses, including reachability closure, for startup images. -/
namespace OCaml.Vm.Boot
open OCaml.Bytecode Vsa.Machine

/-- Every root pointer and every block-field pointer names a defined object. -/
structure HeapClosed (h : Heap) (rs : List Val) : Prop where
  roots : ∀ v ∈ rs, ∀ l, v.loc? = some l → ∃ o, h.get? l = some o
  fields : ∀ l tag fs, h.get? l = some (.block tag fs) →
    ∀ v ∈ fs, ∀ target, v.loc? = some target → ∃ o, h.get? target = some o

/-- Closure converts a finite object table into coverage of all live objects. -/
theorem HeapClosed.live_defined {h : Heap} {rs : List Val} (closed : HeapClosed h rs)
    {l : Nat} (live : Live h rs l) : ∃ o, h.get? l = some o := by
  induction live with
  | root hv hp => exact closed.roots _ hv _ hp
  | field _ hg hv hp _ => exact closed.fields _ _ _ hg _ hv _ hp

/-- A finite placement table can establish more than the live-only relation needs. -/
structure HeapImage (c : Config) (pl : Place) (cp : ChanPlace) (h : Heap) : Prop where
  objects : ∀ l o, h.get? l = some o → ∃ a, pl.φ l = some a ∧ ObjAt c pl cp a o
  separated : ∀ l l' a a' o o', l ≠ l' →
    pl.φ l = some a → pl.φ l' = some a' → h.get? l = some o → h.get? l' = some o' →
    a + 8 * o.wosize ≤ a' - 8 ∨ a' + 8 * o'.wosize ≤ a - 8

/-- All-object coverage and closure give the production live-heap predicate. -/
theorem HeapImage.repr {c : Config} {pl : Place} {cp : ChanPlace} {P : Prog} {s : St}
    (image : HeapImage c pl cp s.heap) (closed : HeapClosed s.heap (roots P s)) :
    HeapRepr c pl cp P s := by
  constructor
  · intro l live
    obtain ⟨o, ho⟩ := closed.live_defined live
    obtain ⟨a, ha, obj⟩ := image.objects l o ho
    exact ⟨a, o, ha, ho, obj⟩
  · intro l l' a a' o o' _ _ ne ha ha' ho ho'
    exact image.separated l l' a a' o o' ne ha ha' ho ho'

end OCaml.Vm.Boot
