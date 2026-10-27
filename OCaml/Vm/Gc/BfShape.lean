import OCaml.Vm.Gc.BestFitSmall
import OCaml.Vm.Gc.BestFitExact
import Vsa.Sim.DlHeap

/-! # The best-fit allocator's free structures

Toward the major heap's allocation readiness (the fresh-copy routes of
`caml_oldify_one` allocate through `caml_alloc_shr_for_minor_gc`): the
best-fit policy's small free lists. Size `s ≤ 16` has a list headed at
`bf_small_fl[s].free`, linked through each free block's first word
(`SmallList`); `SmallShape` gives every list with its windows. A nonempty
list supplies the exact-size path's core conditions (`core_of_nonempty`). -/
namespace OCaml.Vm.Gc.BfShape
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- A small free list from `p`, linked through each block's first word. -/
def SmallList (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 → List (BitVec 64) → Prop
  | p, [] => p = 0#64
  | p, b :: bs => p = b ∧ b ≠ 0#64 ∧ SmallList m (bytesT m b.toNat 8) bs

/-- The list slot of size `s`. -/
def slot (s : Nat) : BitVec 64 := BestFitSmall.slot (BitVec.ofNat 64 s)

/-- **The small free lists** in memory `m`, list `lists s` for size `s`. -/
structure SmallShape (m : Std.ExtHashMap Nat (BitVec 8)) (lists : Nat → List (BitVec 64)) : Prop where
  linked : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → SmallList m (bytesT m (slot s).toNat 8) (lists s)
  /-- every listed block's link word is readable -/
  blocks : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ∀ b ∈ lists s, ReadWindow b 8
  /-- free blocks lie in the heap, above every static -/
  heap : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ∀ b ∈ lists s, Vsa.Sim.DlHeap.heapStart ≤ b.toNat

theorem slot_toNat (s : Nat) (hi : s ≤ Layout.bf_small_count) :
    (slot s).toNat = Layout.sym_bf_small_fl + 16 * s := by
  have log : Nat.log2 Layout.bf_small_size = 4 := by decide
  simp only [slot, BestFitSmall.slot, log, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Layout.sym_bf_small_fl]
  simp only [Layout.bf_small_count] at hi
  omega

theorem slot_write (s : Nat) (hi : s ≤ Layout.bf_small_count) : WriteWindow (slot s) 8 := by
  have h := slot_toNat s hi
  simp only [Layout.bf_small_count] at hi
  constructor <;> rw [h] <;> simp only [Layout.sym_bf_small_fl, Layout.sym_tohost] <;> omega

theorem merge_read (s : Nat) (hi : s ≤ Layout.bf_small_count) :
    ReadWindow (slot s + BitVec.ofNat 64 Layout.off_bf_small_merge) 8 := by
  have h := slot_toNat s hi
  simp only [Layout.bf_small_count] at hi
  have addr : (slot s + BitVec.ofNat 64 Layout.off_bf_small_merge).toNat = Layout.sym_bf_small_fl + 16 * s + 8 := by
    rw [BitVec.toNat_add, h]; simp only [BitVec.toNat_ofNat, Layout.off_bf_small_merge, Layout.sym_bf_small_fl]; omega
  constructor <;> rw [addr] <;> simp only [Layout.sym_bf_small_fl, Layout.sym_tohost] <;> omega

/-- **A nonempty small list** supplies the exact-size path's core conditions. -/
theorem core_of_nonempty {m : Std.ExtHashMap Nat (BitVec 8)} {lists : Nat → List (BitVec 64)} {c : Config}
    (shape : SmallShape m lists) (memory : c.σ.mem = m) {s : Nat} (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count)
    (nonempty : lists s ≠ []) : BestFitSmall.CoreConditions (BitVec.ofNat 64 s) c := by
  have linked := shape.linked s lo hi
  obtain ⟨b, bs, hb⟩ : ∃ b bs, lists s = b :: bs := by
    cases h : lists s with
    | nil => exact absurd h nonempty
    | cons b bs => exact ⟨b, bs, rfl⟩
  rw [hb] at linked
  obtain ⟨head, nonzero, -⟩ := linked
  have firstEq : BestFitSmall.first (BitVec.ofNat 64 s) c = b := by
    unfold BestFitSmall.first word
    rw [memory]; exact head
  have small : s < 2 ^ 64 := by simp only [Layout.bf_small_count] at hi; omega
  refine ⟨?_, ?_, ?_, slot_write s hi, merge_read s hi, ?_, ?_⟩
  · simp only [BitVec.toNat_ofNat]; omega
  · simp only [BitVec.toNat_ofNat]; omega
  · rw [firstEq]; exact nonzero
  · rw [firstEq]; exact shape.blocks s lo hi b (by rw [hb]; exact List.mem_cons_self ..)
  · apply outLRange_of_forall
    intro e member
    simp only [List.mem_singleton] at member
    subst member
    have h := slot_toNat s hi
    simp only [Layout.bf_small_count] at hi
    show _ ∨ (BestFitSmall.slot (BitVec.ofNat 64 s)).toNat + 8 ≤ _
    rw [show BestFitSmall.slot (BitVec.ofNat 64 s) = slot s from rfl, h]
    simp only [Layout.sym_bf_small_fl, Layout.sym_caml_fl_cur_wsz]
    omega

theorem merge_toNat (s : Nat) (hi : s ≤ Layout.bf_small_count) :
    (slot s + BitVec.ofNat 64 Layout.off_bf_small_merge).toNat = Layout.sym_bf_small_fl + 16 * s + 8 := by
  have h := slot_toNat s hi
  simp only [Layout.bf_small_count] at hi
  rw [BitVec.toNat_add, h]; simp only [BitVec.toNat_ofNat, Layout.off_bf_small_merge, Layout.sym_bf_small_fl]; omega

theorem merge_write (s : Nat) (hi : s ≤ Layout.bf_small_count) :
    WriteWindow (slot s + BitVec.ofNat 64 Layout.off_bf_small_merge) 8 := by
  have addr := merge_toNat s hi
  simp only [Layout.bf_small_count] at hi
  constructor <;> rw [addr] <;> simp only [Layout.sym_bf_small_fl, Layout.sym_tohost] <;> omega

/-- **A nonempty small list** supplies the exact-size path's conditions. -/
theorem exact_of_nonempty {m : Std.ExtHashMap Nat (BitVec 8)} {lists : Nat → List (BitVec 64)} {c : Config}
    (shape : SmallShape m lists) (memory : c.σ.mem = m) {s : Nat} (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count)
    (nonempty : lists s ≠ []) : BestFitExact.Conditions (BitVec.ofNat 64 s) c := by
  have core := core_of_nonempty shape memory lo hi nonempty
  obtain ⟨b, bs, hb⟩ : ∃ b bs, lists s = b :: bs := by
    cases h : lists s with
    | nil => exact absurd h nonempty
    | cons b bs => exact ⟨b, bs, rfl⟩
  have head : BestFitSmall.first (BitVec.ofNat 64 s) c = b := by
    have linked := shape.linked s lo hi
    rw [hb] at linked
    unfold BestFitSmall.first word; rw [memory]; exact linked.1
  have inHeap := shape.heap s lo hi b (by rw [hb]; exact List.mem_cons_self ..)
  have mergeAddr := merge_toNat s hi
  have slotAddr := slot_toNat s hi
  have small : s ≤ 16 := by simpa only [Layout.bf_small_count] using hi
  have slotEq : BestFitSmall.slot (BitVec.ofNat 64 s) = slot s := rfl
  refine ⟨core, fun _ => ⟨merge_write s hi, ?_, ?_⟩, fun _ => ?_⟩
  · rw [head]
    apply outLRange_of_forall
    intro e member
    simp only [BestFitSmall.repairLog, List.mem_singleton] at member
    subst member
    simp only [slotEq, mergeAddr, Vsa.Sim.DlHeap.heapStart, Layout.sym_bf_small_fl] at inHeap ⊢
    omega
  · apply outLRange_of_forall
    intro e member
    simp only [BestFitSmall.repairLog, List.mem_singleton] at member
    subst member
    simp only [slotEq, mergeAddr, Layout.sym_bf_small_fl, Layout.sym_caml_fl_cur_wsz]
    omega
  · apply outLRange_of_forall
    intro e member
    have mapApart : ∀ a, a = (slot s + BitVec.ofNat 64 Layout.off_bf_small_merge).toNat ∨ a = (slot s).toNat →
        Layout.sym_bf_small_map + 4 ≤ a := by
      intro a h
      rcases h with rfl | rfl
      · rw [mergeAddr]; simp only [Layout.sym_bf_small_fl, Layout.sym_bf_small_map]; omega
      · rw [slotAddr]; simp only [Layout.sym_bf_small_fl, Layout.sym_bf_small_map]; omega
    have which : e.1 = (slot s + BitVec.ofNat 64 Layout.off_bf_small_merge).toNat ∨ e.1 = (slot s).toNat := by
      unfold BestFitEmpty.effect at member
      split at member
      · simp only [BestFitSmall.repairLog, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
        subst member
        exact Or.inr rfl
    exact Or.inl (mapApart _ which)

/-- A small list survives memory that keeps its blocks' link words. -/
theorem SmallList.congr {m m' : Std.ExtHashMap Nat (BitVec 8)} :
    ∀ (p : BitVec 64) (bs : List (BitVec 64)), (∀ x ∈ bs, bytesT m' x.toNat 8 = bytesT m x.toNat 8) →
      SmallList m p bs → SmallList m' p bs
  | _, [], _, h => h
  | p, x :: xs, same, ⟨hp, hx, rest⟩ => by
    refine ⟨hp, hx, ?_⟩
    rw [same x (List.mem_cons_self ..)]
    exact SmallList.congr _ xs (fun y hy => same y (List.mem_cons_of_mem _ hy)) rest

/-- The lists after popping the head of size `s`. -/
def popped (lists : Nat → List (BitVec 64)) (s : Nat) (bs : List (BitVec 64)) (t : Nat) : List (BitVec 64) :=
  if t = s then bs else lists t

/-- **Popping a small list's head** keeps the shape, given that the head
slot now holds the block's link and every other slot and link word is kept. -/
theorem SmallShape.pop {m m' : Std.ExtHashMap Nat (BitVec 8)} {lists : Nat → List (BitVec 64)} {s : Nat}
    {b : BitVec 64} {bs : List (BitVec 64)} (shape : SmallShape m lists) (hb : lists s = b :: bs)
    (headStore : bytesT m' (slot s).toNat 8 = bytesT m b.toNat 8)
    (otherSlots : ∀ t, 1 ≤ t → t ≤ Layout.bf_small_count → t ≠ s → bytesT m' (slot t).toNat 8 = bytesT m (slot t).toNat 8)
    (links : ∀ t, 1 ≤ t → t ≤ Layout.bf_small_count → ∀ x ∈ popped lists s bs t, bytesT m' x.toNat 8 = bytesT m x.toNat 8) :
    SmallShape m' (popped lists s bs) := by
  refine ⟨fun t lo hi => ?_, fun t lo hi x hx => ?_, fun t lo hi x hx => ?_⟩
  · by_cases same : t = s
    · subst same
      have linked := shape.linked t lo hi
      rw [hb] at linked
      obtain ⟨-, -, rest⟩ := linked
      have l := links t lo hi
      simp only [popped, if_pos] at l ⊢
      rw [headStore]
      exact SmallList.congr _ _ l rest
    · have l := links t lo hi
      simp only [popped, if_neg same] at l ⊢
      rw [otherSlots t lo hi same]
      exact SmallList.congr _ _ l (shape.linked t lo hi)
  · by_cases same : t = s
    · subst same
      simp only [popped, if_pos] at hx
      exact shape.blocks t lo hi x (by rw [hb]; exact List.mem_cons_of_mem _ hx)
    · simp only [popped, if_neg same] at hx
      exact shape.blocks t lo hi x hx
  · by_cases same : t = s
    · subst same
      simp only [popped, if_pos] at hx
      exact shape.heap t lo hi x (by rw [hb]; exact List.mem_cons_of_mem _ hx)
    · simp only [popped, if_neg same] at hx
      exact shape.heap t lo hi x hx

/-! ## The small-list bitmap -/

/-- `bf_small_map`: bit `s - 1` for size `s`. -/
def mapBits (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 32 := bytesT m Layout.sym_bf_small_map 4

/-- The bitmap agrees with the lists. -/
def MapConsistent (m : Std.ExtHashMap Nat (BitVec 8)) (lists : Nat → List (BitVec 64)) : Prop :=
  ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ((mapBits m).getLsbD (s - 1) = true ↔ lists s ≠ [])

/-- Clearing bit `s - 1` when list `s` empties keeps the bitmap consistent. -/
theorem MapConsistent.clear {m m' : Std.ExtHashMap Nat (BitVec 8)} {lists : Nat → List (BitVec 64)} {s : Nat}
    {bs : List (BitVec 64)} (map : MapConsistent m lists) (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count)
    (emptied : bs = []) (bits : mapBits m' = mapBits m &&& ~~~(1#32 <<< (s - 1))) :
    MapConsistent m' (popped lists s bs) := by
  intro t lt ht
  have small : s - 1 < 32 := by simp only [Layout.bf_small_count] at hi; omega
  have smallT : t - 1 < 32 := by simp only [Layout.bf_small_count] at ht; omega
  rw [bits, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  by_cases same : t = s
  · subst same
    simp [popped, emptied, smallT]
  · have ne : t - 1 ≠ s - 1 := by omega
    have old := map t lt ht
    simp only [popped, if_neg same]
    have cond : t - 1 < s - 1 ∨ ¬t - 1 - (s - 1) = 0 := by omega
    simp only [smallT, decide_true, Bool.true_and, Bool.not_eq_true', Bool.and_eq_true, cond]
    simp [smallT, ne, ← old, BitVec.getLsbD_eq_getElem]
    omega

/-- Header representation of the small lists, alongside their link shape.
Every listed block carries the size of its list in its physical header. -/
structure SmallHeaders (m : Std.ExtHashMap Nat (BitVec 8))
    (lists : Nat → List (BitVec 64)) : Prop where
  sizes : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ∀ b ∈ lists s,
    bytesT m (b - 8#64).toNat 8 >>> (10 : Nat) = BitVec.ofNat 64 s

/-- Transport a list representation through stores which keep its slots and links. -/
theorem SmallShape.congr {m m' lists} (shape : SmallShape m lists)
    (slots : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count →
      bytesT m' (slot s).toNat 8 = bytesT m (slot s).toNat 8)
    (links : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ∀ b ∈ lists s,
      bytesT m' b.toNat 8 = bytesT m b.toNat 8) : SmallShape m' lists := by
  refine ⟨?_,shape.blocks,shape.heap⟩
  intro s lo hi
  rw [slots s lo hi]
  exact SmallList.congr _ _ (links s lo hi) (shape.linked s lo hi)


/-- Prepend a block at its decoded size. -/
def inserted (lists : Nat → List (BitVec 64)) (s : Nat) (b : BitVec 64)
    (t : Nat) : List (BitVec 64) := if t = s then b :: lists t else lists t

theorem SmallShape.push {m m' lists s b} (shape : SmallShape m lists)
    (nonzero : b ≠ 0#64) (window : ReadWindow b 8)
    (heap : Vsa.Sim.DlHeap.heapStart ≤ b.toNat)
    (head : bytesT m' (slot s).toNat 8 = b)
    (link : bytesT m' b.toNat 8 = bytesT m (slot s).toNat 8)
    (slots : ∀ t, 1 ≤ t → t ≤ Layout.bf_small_count → t ≠ s →
      bytesT m' (slot t).toNat 8 = bytesT m (slot t).toNat 8)
    (links : ∀ t, 1 ≤ t → t ≤ Layout.bf_small_count → ∀ x ∈ lists t,
      bytesT m' x.toNat 8 = bytesT m x.toNat 8) :
    SmallShape m' (inserted lists s b) := by
  refine ⟨?_,?_,?_⟩
  · intro t lo hi
    by_cases eq : t = s
    · subst t
      simp only [inserted,ite_true]
      rw [head]
      refine ⟨rfl,nonzero,?_⟩
      rw [link]
      exact SmallList.congr _ _ (links s lo hi) (shape.linked s lo hi)
    · simp only [inserted,if_neg eq]
      rw [slots t lo hi eq]
      exact SmallList.congr _ _ (links t lo hi) (shape.linked t lo hi)
  · intro t lo hi x hx
    by_cases eq : t = s
    · simp only [inserted,if_pos eq,List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact window
      · exact shape.blocks t lo hi x hx
    · exact shape.blocks t lo hi x (by simpa only [inserted,if_neg eq] using hx)
  · intro t lo hi x hx
    by_cases eq : t = s
    · simp only [inserted,if_pos eq,List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact heap
      · exact shape.heap t lo hi x hx
    · exact shape.heap t lo hi x (by simpa only [inserted,if_neg eq] using hx)

theorem SmallHeaders.congr {m m' lists} (headers : SmallHeaders m lists)
    (same : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ∀ b ∈ lists s,
      bytesT m' (b-8#64).toNat 8 = bytesT m (b-8#64).toNat 8) :
    SmallHeaders m' lists := by
  constructor
  intro s lo hi b hb
  rw [same s lo hi b hb]
  exact headers.sizes s lo hi b hb

theorem SmallHeaders.pop {m lists s b bs} (headers : SmallHeaders m lists)
    (selected : lists s = b :: bs) : SmallHeaders m (popped lists s bs) := by
  constructor
  intro t lo hi x hx
  apply headers.sizes t lo hi x
  by_cases eq : t = s
  · subst t
    rw [selected]
    exact List.mem_cons_of_mem _ (by simpa only [popped,ite_true] using hx)
  · simpa only [popped,if_neg eq] using hx

theorem SmallHeaders.push {m lists s b} (headers : SmallHeaders m lists)
    (size : bytesT m (b-8#64).toNat 8 >>> (10 : Nat) = BitVec.ofNat 64 s) :
    SmallHeaders m (inserted lists s b) := by
  constructor
  intro t lo hi x hx
  by_cases eq : t = s
  · subst t
    simp only [inserted,ite_true,List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact size
    · exact headers.sizes s lo hi x hx
  · exact headers.sizes t lo hi x (by simpa only [inserted,if_neg eq] using hx)

/-- Original physical extents. Distinct occurrences, including two occurrences
in one list, occupy disjoint header-plus-payload intervals. Production of
this stronger component by the allocator's callers remains an obligation. -/
structure SmallPhysical (lists : Nat → List (BitVec 64)) : Prop where
  bounds : ∀ s, 1 ≤ s → s ≤ Layout.bf_small_count → ∀ b ∈ lists s,
    Vsa.Sim.DlHeap.heapStart + 8 ≤ b.toNat ∧ b.toNat + 8*s < 2^64
  separate : ∀ (s t i j : Nat) (b x : BitVec 64), 1 ≤ s → s ≤ Layout.bf_small_count →
    1 ≤ t → t ≤ Layout.bf_small_count →
    (lists s)[i]? = some b → (lists t)[j]? = some x →
    (s ≠ t ∨ i ≠ j) → b.toNat + 8*s ≤ x.toNat-8 ∨ x.toNat + 8*t ≤ b.toNat-8

/-- Derive selected-block separation from original occurrence separation. -/
theorem SmallPhysical.selected_apart {lists s b bs} (physical : SmallPhysical lists)
    (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count) (selected : lists s = b :: bs)
    {t x} (lt : 1 ≤ t) (ht : t ≤ Layout.bf_small_count)
    (hx : x ∈ popped lists s bs t) :
    b.toNat + 8*s ≤ x.toNat-8 ∨ x.toNat + 8*t ≤ b.toNat-8 := by
  by_cases eq : t = s
  · subst t
    simp only [popped,ite_true] at hx
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hx
    apply physical.separate s s 0 (j+1) b x lo hi lo hi
    · simp [selected]
    · simpa [selected] using hj
    · exact Or.inr (by omega)
  · have hx' : x ∈ lists t := by simpa only [popped,if_neg eq] using hx
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hx'
    exact physical.separate s t 0 j b x lo hi lt ht (by simp [selected]) hj
      (Or.inl (Ne.symm eq))


/-- Setting the inserted size's bit preserves bitmap/list agreement. -/
theorem MapConsistent.set {m m' lists s b} (map : MapConsistent m lists)
    (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count)
    (bits : mapBits m' = mapBits m ||| (1#32 <<< (s-1))) :
    MapConsistent m' (inserted lists s b) := by
  have cert : ∀ s < 17, 1 ≤ s → ∀ t < 17, 1 ≤ t →
      (1#32 <<< (s-1)).getLsbD (t-1) = decide (t=s) := by decide
  intro t lt ht
  rw [bits,BitVec.getLsbD_or,cert s (by simpa only [Layout.bf_small_count] using Nat.lt_succ_of_le hi)
    lo t (by simpa only [Layout.bf_small_count] using Nat.lt_succ_of_le ht) lt]
  by_cases eq : t = s
  · simp [inserted,eq]
  · simpa only [inserted,if_neg eq,eq,decide_false,Bool.or_false,ite_false] using map t lt ht

end OCaml.Vm.Gc.BfShape
