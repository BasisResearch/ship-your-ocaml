import OCaml.Vm.Sim.ArmInput

/-!
# Placing a fresh location

An allocating arm needs a representation witness whose placement maps the
fresh location `(s.heap.alloc o).2` to the reserved nursery block. The loop
head's witness may place that (absent) location anywhere, but no represented
value can point at it: every root and every field of a live block refers to a
live location, and `HeapRepr` puts every live location in the heap. So
re-placing an absent location (`Place.put`) keeps the whole representation
(`VmReprAt.put`) and the loop geometry (`LoopGeometry.put`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Place location `l` at `a`. -/
def _root_.OCaml.Vm.Place.put (pl : Place) (l a : Nat) : Place :=
  { pl with φ := fun l' => if l' = l then some a else pl.φ l' }

theorem put_ne {pl : Place} {l l' a : Nat} (ne : l' ≠ l) : (pl.put l a).φ l' = pl.φ l' := by
  simp [Place.put, ne]

theorem put_self {pl : Place} {l a : Nat} : (pl.put l a).φ l = some a := by
  simp [Place.put]

/-- A placed, present location is not the absent one. -/
theorem put_present {pl : Place} {h : Heap} {l l0 a b : Nat} {o : Obj}
    (absent : h.get? l0 = none) (object : h.get? l = some o) (placed : (pl.put l0 a).φ l = some b) :
    pl.φ l = some b := by
  have ne : l ≠ l0 := fun eq => by rw [eq, absent] at object; cases object
  rwa [put_ne ne] at placed

/-- A value pointing only at present locations is represented alike. -/
theorem valWord_put {pl : Place} {h : Heap} {l0 a : Nat} {v : Val} (absent : h.get? l0 = none)
    (present : ∀ l, v.loc? = some l → ∃ o, h.get? l = some o) : valWord (pl.put l0 a) v = valWord pl v := by
  cases v with
  | ptr l k =>
    obtain ⟨o, object⟩ := present l rfl
    have ne : l ≠ l0 := fun eq => by rw [eq, absent] at object; cases object
    simp only [valWord, put_ne ne]
  | _ => rfl

/-- Every live location is present. -/
theorem _root_.OCaml.Vm.HeapRepr.live_present {c : Config} {pl : Place} {cp : ChanPlace} {P : Prog} {s : St}
    (h : HeapRepr c pl cp P s) {l : Nat} (live : Live s.heap (roots P s) l) : ∃ o, s.heap.get? l = some o := by
  obtain ⟨a, o, -, object, -⟩ := h.1 l live
  exact ⟨o, object⟩

/-- **The heap representation survives re-placing an absent location.** -/
theorem _root_.OCaml.Vm.HeapRepr.put {c : Config} {pl : Place} {cp : ChanPlace} {P : Prog} {s : St} {l0 a : Nat}
    (h : HeapRepr c pl cp P s) (absent : s.heap.get? l0 = none) : HeapRepr c (pl.put l0 a) cp P s := by
  refine ⟨fun l live => ?_, fun l l' b b' o o' live live' ne placed placed' object object' =>
    h.2 l l' b b' o o' live live' ne (put_present absent object placed) (put_present absent object' placed')
      object object'⟩
  obtain ⟨b, o, placed, object, at_⟩ := h.1 l live
  have ne : l ≠ l0 := fun eq => by rw [eq, absent] at object; cases object
  refine ⟨b, o, by rw [put_ne ne]; exact placed, object, at_.1, ?_⟩
  have fields := at_.2
  cases o with
  | block t fs =>
    intro i v hv
    rw [valWord_put absent fun l' loc => HeapRepr.live_present h (Live.field live object
      (List.mem_of_getElem? hv) loc)]
    exact fields i v hv
  | _ => exact fields

/-- **The representation survives re-placing an absent location.** -/
theorem _root_.OCaml.Vm.VmReprAt.put {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {sp high l0 a : Nat}
    (h : VmReprAt P s c pl cp sp high) (absent : s.heap.get? l0 = none) :
    VmReprAt P s c (pl.put l0 a) cp sp high := by
  have root : ∀ v ∈ roots P s, valWord (pl.put l0 a) v = valWord pl v := fun v member =>
    valWord_put absent fun l loc => HeapRepr.live_present h.heap (Live.root member loc)
  refine { h with
    pc := h.pc
    accu := by rw [root _ (by simp [roots])]; exact h.accu
    env := by rw [root _ (by simp [roots])]; exact h.env
    globals := by rw [root _ (by simp [roots])]; exact h.globals
    stack := ⟨h.stack.1, fun i v hv => by
      rw [root _ (by simp [roots, List.mem_of_getElem? hv])]; exact h.stack.2 i v hv⟩
    heap := HeapRepr.put h.heap absent }

/-- Word alignment survives placing at an aligned address. -/
theorem WordPlace.put {pl : Place} {l0 a : Nat} (w : WordPlace pl) (aligned : a % 8 = 0) :
    WordPlace (pl.put l0 a) :=
  ⟨w.code, fun l b placed => by
    by_cases eq : l = l0
    · subst eq; rw [put_self] at placed; cases placed; exact aligned
    · rw [put_ne eq] at placed; exact w.heap l b placed, w.atoms⟩

/-- **The stack geometry survives re-placing an absent location.** -/
theorem StackGeometry.put {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {high l0 a : Nat}
    (g : StackGeometry P s c pl cp high) (absent : s.heap.get? l0 = none) (aligned : a % 8 = 0) :
    StackGeometry P s c (pl.put l0 a) cp high :=
  { g with
    heap := fun l b o placed object => g.heap l b o (put_present absent object placed) object
    heapArena := fun l b o placed object => g.heapArena l b o (put_present absent object placed) object
    even := (g.words.put aligned).even
    words := g.words.put aligned
    heapLow := fun l b o placed object => g.heapLow l b o (put_present absent object placed) object
    heapCode := fun l b o placed object => g.heapCode l b o (put_present absent object placed) object
    heapAtoms := fun l b o placed object => g.heapAtoms l b o (put_present absent object placed) object
    heapChannels := fun l b o placed object => g.heapChannels l b o (put_present absent object placed) object
    heapPrims := fun l b o placed object => g.heapPrims l b o (put_present absent object placed) object
    domainHeap := fun l b o placed object => g.domainHeap l b o (put_present absent object placed) object }

/-- The nursery geometry survives re-placing an absent location. -/
theorem _root_.OCaml.Vm.Gc.NurseryGeometry.put {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high l0 a : Nat} (g : Gc.NurseryGeometry P s c pl cp high) (absent : s.heap.get? l0 = none) :
    Gc.NurseryGeometry P s c (pl.put l0 a) cp high :=
  { g with
    heap := fun l b o placed object => g.heap l b o (put_present absent object placed) object
    heapDomain := fun l b o placed object => g.heapDomain l b o (put_present absent object placed) object
    heapPrivate := fun l b o placed object => g.heapPrivate l b o (put_present absent object placed) object
    heapChunks := fun l b o placed object => g.heapChunks l b o (put_present absent object placed) object }

/-- **The loop geometry survives re-placing an absent location.** -/
theorem _root_.OCaml.LoopGeometry.put {L : OCaml.Layout} {P : Prog} {s : St} {c : Config} {pl : Place}
    {cp : ChanPlace} {high l0 a : Nat} (g : OCaml.LoopGeometry L P s c pl cp high)
    (absent : s.heap.get? l0 = none) (aligned : a % 8 = 0) :
    OCaml.LoopGeometry L P s c (pl.put l0 a) cp high :=
  ⟨⟨g.toStackGeometry.put absent aligned, g.nursery.put absent⟩, g.room⟩

/-- **An arm input with the fresh location placed.** -/
theorem ArmInput.put {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config} {pl : Place}
    {cp : ChanPlace} {sp high l0 a : Nat} (h : ArmInput L P s op c pl cp sp high)
    (absent : s.heap.get? l0 = none) (aligned : a % 8 = 0) : ArmInput L P s op c (pl.put l0 a) cp sp high :=
  { toVmReprAt := h.toVmReprAt.put absent
    dispatch := h.dispatch
    runtime := h.runtime
    geometry := h.geometry.put absent aligned
    native := h.native }

/-- The fresh location of an allocation is absent. -/
theorem alloc_absent (h : Heap) (o : Obj) : h.get? (h.alloc o).2 = none := by
  simp [Heap.alloc, Heap.get?]

end OCaml.Vm.Sim
