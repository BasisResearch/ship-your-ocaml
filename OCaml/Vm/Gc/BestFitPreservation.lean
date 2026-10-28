import OCaml.Vm.Gc.BestFitSearchRoute

/-! Representation after native next-size allocation. Original physical extents
are explicit: their production by allocator callers is still open. All memory
transport below consumes checked stage posts or their exact bounded store logs. -/
namespace OCaml.Vm.Gc.BfShape
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

theorem popped_mem {lists s b bs t x} (selected : lists s = b :: bs)
    (member : x ∈ popped lists s bs t) : x ∈ lists t := by
  by_cases eq : t = s
  · subst t
    rw [selected]
    exact List.mem_cons_of_mem _ (by simpa only [popped,ite_true] using member)
  · simpa only [popped,if_neg eq] using member

theorem SmallPhysical.header_nat {lists t x} (physical : SmallPhysical lists)
    (lo : 1 ≤ t) (hi : t ≤ Layout.bf_small_count) (member : x ∈ lists t) :
    (x-8#64).toNat = x.toNat-8 := by
  have low := (physical.bounds t lo hi x member).1
  have bound := x.isLt
  simp only [BitVec.toNat_sub,BitVec.toNat_ofNat,DlHeap.heapStart] at *
  omega

/-- Original native-frame separation, only for the observed header and link.
The search caller already supplies this for every original listed block. -/
def StackApart (sp : BitVec 64) (lists : Nat → List (BitVec 64)) : Prop :=
  ∀ t, 1 ≤ t → t ≤ Layout.bf_small_count → ∀ x ∈ lists t,
    sp.toNat+32 ≤ x.toNat-8 ∨ x.toNat+8 ≤ sp.toNat

theorem SmallPhysical.insertApart {lists s b bs} (physical : SmallPhysical lists)
    (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count) (selected : lists s = b :: bs) :
    BestFitRemnant.InsertApart b (popped lists s bs) := by
  constructor
  · intro t lt ht x hx
    have sep := physical.selected_apart lo hi selected lt ht hx
    omega
  · intro t lt ht x hx
    have member := popped_mem selected hx
    have xb := physical.bounds t lt ht x member
    have xn := physical.header_nat lt ht member
    have sep := physical.selected_apart lo hi selected lt ht hx
    rw [xn]
    exact ⟨by omega,by omega⟩
end OCaml.Vm.Gc.BfShape

namespace OCaml.Vm.Gc.BestFitExact
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Read the selected head from the original represented list. -/
theorem selected_first {lists s b bs c} (shape : BfShape.SmallShape c.σ.mem lists)
    (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count) (selected : lists s = b :: bs) :
    BestFitSmall.first (BitVec.ofNat 64 s) c = b := by
  have linked := shape.linked s lo hi
  rw [selected] at linked
  exact linked.1

/-- Actual exact-size log readback, including both clear and unchanged branches. -/
theorem Post.bitmap {ra s before after}
    (post : Post ra (BitVec.ofNat 64 s) before after)
    (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count) :
    BfShape.mapBits after.σ.mem =
      if BestFitSmall.next (BitVec.ofNat 64 s) before = 0 then
        BfShape.mapBits before.σ.mem &&& ~~~(1#32 <<< (s-1)) else BfShape.mapBits before.σ.mem := by
  have size : (BitVec.ofNat 64 s).toNat = s := by
    have : s < 2^64 := by change s ≤ 16 at hi; omega
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt this]
  rw [BfShape.mapBits,post.memory,effect_bitmap (by omega) (by omega) (BfShape.exact_prefix_bitmap hi),size]
  rfl

theorem Post.boundedBitmap {ra s before after}
    (post : Post ra (BitVec.ofNat 64 s) before after)
    (bounded : BfShape.BoundedBitmap before.σ.mem)
    (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count) : BfShape.BoundedBitmap after.σ.mem := by
  have bits := post.bitmap lo hi
  split at bits
  · exact bounded.clear bits
  · exact bounded.congr bits

/-- Every exact-size native branch returns the actual popped representation. -/
theorem Post.smallRepresentation {ra lists s b bs before after}
    (post : Post ra (BitVec.ofNat 64 s) before after)
    (repr : BfShape.SmallRepresentation before.σ.mem lists)
    (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count) (selected : lists s = b :: bs) :
    BfShape.SmallRepresentation after.σ.mem (BfShape.popped lists s bs) := by
  have first := selected_first repr.shape lo hi selected
  have linked := repr.shape.linked s lo hi
  rw [selected] at linked
  have tail : BfShape.SmallList before.σ.mem (BestFitSmall.next (BitVec.ofNat 64 s) before) bs := by
    simpa only [BestFitSmall.next,first,word] using linked.2.2
  have size : (BitVec.ofNat 64 s).toNat = s := by
    have : s < 2^64 := by simp only [Layout.bf_small_count] at hi; omega
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt this]
  have headStore : bytesT after.σ.mem (BfShape.slot s).toNat 8 = bytesT before.σ.mem b.toNat 8 := by
    have observed : bytesT after.σ.mem (BfShape.slot s).toNat 8 =
        BestFitSmall.next (BitVec.ofNat 64 s) before := by
      rw [post.memory]
      exact BfShape.exact_effect_head hi
    rw [observed]
    change bytesT before.σ.mem (BestFitSmall.first (BitVec.ofNat 64 s) before).toNat 8 = _
    rw [first]
  have heapRead : ∀ a n, Vsa.Sim.DlHeap.heapStart ≤ a → bytesT after.σ.mem a n = bytesT before.σ.mem a n := by
    intro a n heap
    rw [post.memory]
    exact bytesT_writeLog_out _ (effect_outside (BfShape.exact_heap_outside hi heap))
  refine ⟨repr.shape.pop selected headStore ?_ ?_,(repr.headers.pop selected).congr ?_,?_,repr.physical.pop selected⟩
  · intro t lt ht different
    rw [post.memory]
    exact bytesT_writeLog_out _ (effect_outside (BfShape.exact_slot_outside hi ht different))
  · intro t lt ht x hx
    exact heapRead _ _ (repr.shape.heap t lt ht x (BfShape.popped_mem selected hx))
  · intro t lt ht x hx
    have member := BfShape.popped_mem selected hx
    have bound := repr.physical.bounds t lt ht x member
    rw [repr.physical.header_nat lt ht member]
    exact heapRead _ _ (by omega)
  · have bits : BfShape.mapBits after.σ.mem =
        if BestFitSmall.next (BitVec.ofNat 64 s) before = 0 then
          BfShape.mapBits before.σ.mem &&& ~~~(1#32 <<< (s-1)) else BfShape.mapBits before.σ.mem := by
      rw [BfShape.mapBits,post.memory,effect_bitmap (by omega) (by omega) (BfShape.exact_prefix_bitmap hi),size]
      rfl
    by_cases empty : BestFitSmall.next (BitVec.ofNat 64 s) before = 0
    · apply repr.map.clear lo hi (tail.zero_iff.mp empty)
      simpa only [empty,ite_true] using bits
    · apply repr.map.pop_nonempty selected (fun h => empty (tail.zero_iff.mpr h))
      simpa only [empty,ite_false] using bits

theorem Post.boundedSmallRepresentation {ra lists s b bs before after}
    (post : Post ra (BitVec.ofNat 64 s) before after)
    (repr : BfShape.BoundedSmallRepresentation before.σ.mem lists)
    (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count) (selected : lists s = b :: bs) :
    BfShape.BoundedSmallRepresentation after.σ.mem (BfShape.popped lists s bs) :=
  ⟨post.smallRepresentation repr.toSmallRepresentation lo hi selected,
    post.boundedBitmap repr.bounded lo hi⟩

/-- The selected physical header is unchanged by the static branch stores. -/
theorem Post.selected_header {ra lists s b bs before after}
    (post : Post ra (BitVec.ofNat 64 s) before after)
    (physical : BfShape.SmallPhysical lists)
    (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count) (selected : lists s = b :: bs) :
    bytesT after.σ.mem (b-8#64).toNat 8 = bytesT before.σ.mem (b-8#64).toNat 8 := by
  have member : b ∈ lists s := by rw [selected]; exact List.mem_cons_self ..
  have bound := physical.bounds s lo hi b member
  rw [post.memory]
  apply bytesT_writeLog_out
  apply effect_outside
  apply BfShape.exact_heap_outside hi
  rw [physical.header_nat lo hi member]
  omega

end OCaml.Vm.Gc.BestFitExact

namespace OCaml.Vm.Gc.BestFitNext
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Bounded frame certificate for the split's three actual stores. -/
structure SplitOutside (sp b : BitVec 64) (a n : Nat) : Prop where
  counter : a+n ≤ Layout.sym_caml_fl_cur_wsz ∨ Layout.sym_caml_fl_cur_wsz+8 ≤ a
  header : a+n ≤ (b-8#64).toNat ∨ (b-8#64).toNat+8 ≤ a
  stack : a+n ≤ sp.toNat ∨ sp.toNat+8 ≤ a

theorem splitMemory_read {sp b request m a n} (outside : SplitOutside sp b a n) :
    bytesT (splitMemory sp b request m) a n = bytesT m a n := by
  unfold splitMemory
  apply bytesT_writeLog_out
  exact ⟨outside.counter,outside.header,outside.stack,True.intro⟩

theorem splitMemory_header {sp b request m} (geo : SplitGeometry sp b) :
    sourceHeader b (splitMemory sp b request m) = smallHeader request (sourceHeader b m) := by
  unfold sourceHeader splitMemory
  apply word_writeLog_at _ _ 1 _ _ rfl
  have sep := geo.separate
  rw [geo.header_nat] at *
  exact ⟨by dsimp only [splitLog]; omega,True.intro⟩

theorem splitOutside_static {sp b} (geo : SplitGeometry sp b) {a n}
    (high : a+n ≤ DlHeap.heapStart) (counter : a+n ≤ Layout.sym_caml_fl_cur_wsz ∨
      Layout.sym_caml_fl_cur_wsz+8 ≤ a) : SplitOutside sp b a n := by
  have sh := geo.stackHeap
  have bh := geo.blockHeap
  refine ⟨counter,Or.inl ?_,Or.inl (by omega)⟩
  rw [geo.header_nat]
  omega

/-- The final family is precisely selected-head pop followed by conditional
remnant insertion, at the size decoded in the actual split snapshot. -/
def routeLists (sp s b request : BitVec 64) (lists : Nat → List (BitVec 64))
    (bs : List (BitVec 64)) (m : Std.ExtHashMap Nat (BitVec 8)) :=
  BestFitRemnant.finalLists b (splitMemory sp b request (poppedMemory sp s b m))
    (BfShape.popped lists s.toNat bs)

/-- The split prefix preserves the remaining representation. Every nonaliasing
fact follows from original physical extents and original stack separation. -/
theorem RouteInput.split_representation {sp s b request lists bs c picked popped}
    (input : RouteInput sp s b request lists bs c)
    (physical : BfShape.SmallPhysical lists) (stack : BfShape.StackApart sp lists)
    (first : PickPost sp s c picked)
    (second : PopPost sp s b (bytesT c.σ.mem sp.toNat 8) request picked popped) :
    let m := splitMemory sp b request popped.σ.mem
    BfShape.SmallShape m (BfShape.popped lists s.toNat bs) ∧
    BfShape.SmallHeaders m (BfShape.popped lists s.toNat bs) ∧
    BfShape.MapConsistent m (BfShape.popped lists s.toNat bs) := by
  have represented := input.popped_shape first second
  have headers : BfShape.SmallHeaders popped.σ.mem (BfShape.popped lists s.toNat bs) := by
    apply (input.headers.pop input.selected).congr
    intro t lo hi x hx
    have member := BfShape.popped_mem input.selected hx
    have bound := physical.bounds t lo hi x member
    apply input.prefix_read first second
    apply prefix_out_heap input.small
    rw [physical.header_nat lo hi member]
    omega
  have frame : ∀ t, 1 ≤ t → t ≤ Layout.bf_small_count →
      ∀ x ∈ BfShape.popped lists s.toNat bs t,
      SplitOutside sp b x.toNat 8 ∧ SplitOutside sp b (x-8#64).toNat 8 := by
    intro t lo hi x hx
    have member := BfShape.popped_mem input.selected hx
    have bounds := physical.bounds t lo hi x member
    have sep := physical.selected_apart input.positive input.small input.selected lo hi hx
    have st := stack t lo hi x member
    have xn := physical.header_nat lo hi member
    have bn := input.geometry.header_nat
    have bh := input.geometry.blockHeap
    simp only [DlHeap.heapStart,Layout.sym_caml_fl_cur_wsz] at bounds bh
    constructor
    · exact ⟨Or.inr (by simp only [Layout.sym_caml_fl_cur_wsz]; omega),by rw [bn]; omega,by omega⟩
    · rw [xn]
      exact ⟨Or.inr (by simp only [Layout.sym_caml_fl_cur_wsz]; omega),by rw [bn]; omega,by omega⟩
  have slots : ∀ t, 1 ≤ t → t ≤ Layout.bf_small_count →
      bytesT (splitMemory sp b request popped.σ.mem) (BfShape.slot t).toNat 8 =
        bytesT popped.σ.mem (BfShape.slot t).toNat 8 := by
    intro t lo hi
    apply splitMemory_read
    apply splitOutside_static input.geometry
    · rw [BfShape.slot_toNat t hi]
      simp only [Layout.bf_small_count] at hi
      simp only [Layout.sym_bf_small_fl,DlHeap.heapStart]; omega
    · rw [BfShape.slot_toNat t hi]
      simp only [Layout.sym_bf_small_fl,Layout.sym_caml_fl_cur_wsz]; omega
  have bits : BfShape.mapBits (splitMemory sp b request popped.σ.mem) =
      BfShape.mapBits popped.σ.mem :=
    splitMemory_read (splitOutside_static input.geometry (by decide) (by decide))
  refine ⟨represented.1.congr slots (fun t lo hi x hx => splitMemory_read (frame t lo hi x hx).1),
    headers.congr (fun t lo hi x hx => splitMemory_read (frame t lo hi x hx).2),?_⟩
  intro t lo hi
  change (BfShape.mapBits _).getLsbD _ = true ↔ _
  rw [bits]
  exact represented.2 t lo hi

/-- Checked native-return preservation, for every existing remnant branch.
The word counter equation remains available as `post.counter`. -/
theorem RoutePost.representation {sp s b request lists bs before after}
    (post : RoutePost sp s b request lists bs before after)
    (input : RouteInput sp s b request lists bs before)
    (physical : BfShape.SmallPhysical lists) (stack : BfShape.StackApart sp lists) :
    BfShape.SmallShape after.σ.mem (routeLists sp s b request lists bs before.σ.mem) ∧
    BfShape.SmallHeaders after.σ.mem (routeLists sp s b request lists bs before.σ.mem) ∧
    BfShape.MapConsistent after.σ.mem (routeLists sp s b request lists bs before.σ.mem) := by
  obtain ⟨picked,popped,path⟩ := post.path_spec
  have represented := input.split_representation physical stack path.pick path.pop
  have splitInput := input.split_input path.pick path.pop
  have small : (BestFitRemnant.size b (splitMemory sp b request popped.σ.mem)).toNat ≤ 16 := by
    change (sourceSize (sourceHeader b (splitMemory sp b request popped.σ.mem))).toNat ≤ 16
    rw [splitMemory_header input.geometry,
      smallHeader_size input.requestPositive splitInput.larger splitInput.small]
    have := splitInput.small
    omega
  have result := BestFitRemnant.effect_representation small input.geometry.blockHeap input.remnant.read
    represented.1 represented.2.1 represented.2.2
    (physical.insertApart input.positive input.small input.selected) input.geometry.header_nat
  have memory : after.σ.mem = writeLog (splitMemory sp b request popped.σ.mem)
      (BestFitRemnant.effect b (splitMemory sp b request popped.σ.mem)) := by
    rw [path.complete.memory,completeLog,writeLog_append]
    rfl
  have snapshot : poppedMemory sp s b before.σ.mem = popped.σ.mem := by
    rw [poppedMemory,show pickedMemory s before.σ.mem = picked.σ.mem from path.pick.memory.symm]
    exact path.pop.memory.symm
  rw [memory]
  simpa only [routeLists,snapshot] using result

end OCaml.Vm.Gc.BestFitNext

namespace OCaml.Vm.Gc.BestFitNext
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The allocated header starts immediately after the remnant's physical
extent. The original whole-block bound prevents every address wrap. -/
theorem resultHeader_nat {b request hd : BitVec 64}
    (positive : 1 ≤ request.toNat) (larger : request.toNat < (sourceSize hd).toNat)
    (small : (sourceSize hd).toNat ≤ 16)
    (lower : 8 ≤ b.toNat) (upper : b.toNat+8*(sourceSize hd).toNat < 2^64) :
    (resultHeader b request hd).toNat = b.toNat+8*((sourceSize hd).toNat-request.toNat-1) := by
  have cert : ∀ s < 17, ∀ r < 17, 1 ≤ r → r < s →
      ((((BitVec.ofNat 64 s + 1#64 - BitVec.ofNat 64 r) <<< (3 : Nat)) - 8#64)).toNat =
        8*(s-r) := by decide
  have req : request = BitVec.ofNat 64 request.toNat := by simp
  have sz : sourceSize hd = BitVec.ofNat 64 (sourceSize hd).toNat := by simp
  have offset : ((cutWords request hd <<< (3 : Nat))-8#64).toNat =
      8*((sourceSize hd).toNat-request.toNat) := by
    unfold cutWords
    rw [req,sz]
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt request.isLt,
      Nat.mod_eq_of_lt (sourceSize hd).isLt] using cert _ (by omega) _ (by omega) positive larger
  have hn : (b-8#64).toNat = b.toNat-8 := by
    have := b.isLt
    simp only [BitVec.toNat_sub,BitVec.toNat_ofNat]
    omega
  rw [resultHeader,BitVec.toNat_add,offset,hn,Nat.mod_eq_of_lt (by omega)]
  omega

/-- The actual split snapshot decodes the smaller remnant size from the
original selected header. Shared by free and allocated extent preservation. -/
theorem RoutePost.remnant_size_nat {sp s b request lists bs before after}
    (post : RoutePost sp s b request lists bs before after)
    (input : RouteInput sp s b request lists bs before) :
    (BestFitRemnant.size b
      (splitMemory sp b request (poppedMemory sp s b before.σ.mem))).toNat =
      s.toNat-request.toNat-1 := by
  obtain ⟨picked,popped,path⟩ := post.path_spec
  have snapshot : poppedMemory sp s b before.σ.mem = popped.σ.mem := by
    rw [poppedMemory,show pickedMemory s before.σ.mem = picked.σ.mem from path.pick.memory.symm]
    exact path.pop.memory.symm
  rw [snapshot]
  have splitInput := input.split_input path.pick path.pop
  change (sourceSize (sourceHeader b (splitMemory sp b request popped.σ.mem))).toNat = _
  rw [splitMemory_header input.geometry,
    smallHeader_size input.requestPositive splitInput.larger splitInput.small]
  have old : sourceHeader b popped.σ.mem = sourceHeader b before.σ.mem :=
    input.prefix_read path.pick path.pop (prefix_out_heap input.small (by
      rw [input.geometry.header_nat]; have := input.geometry.blockHeap; omega))
  rw [old,input.size]

/-- Every final free occurrence has bounded, disjoint physical extents at the
same native return. Zero-word and sweep-deferred remnants leave only the pop. -/
theorem RoutePost.physical {sp s b request lists bs before after}
    (post : RoutePost sp s b request lists bs before after)
    (input : RouteInput sp s b request lists bs before)
    (physical : BfShape.SmallPhysical lists) :
    BfShape.SmallPhysical (routeLists sp s b request lists bs before.σ.mem) := by
  unfold routeLists BestFitRemnant.finalLists
  split
  · apply physical.remnant input.positive input.small input.selected
    rw [post.remnant_size_nat input]
    omega
  · exact physical.pop input.selected

/-- A compact reusable representation at the checked route's native return. -/
theorem RoutePost.smallRepresentation {sp s b request lists bs before after}
    (post : RoutePost sp s b request lists bs before after)
    (input : RouteInput sp s b request lists bs before)
    (physical : BfShape.SmallPhysical lists) (stack : BfShape.StackApart sp lists) :
    BfShape.SmallRepresentation after.σ.mem (routeLists sp s b request lists bs before.σ.mem) := by
  have represented := post.representation input physical stack
  exact ⟨represented.1,represented.2.1,represented.2.2,post.physical input physical⟩

/-- Physical separation of the allocated header and all its payload words
from the represented free header-plus-payload extents. -/
structure AllocatedApart (a : Nat) (request : BitVec 64)
    (lists : Nat → List (BitVec 64)) : Prop where
  bound : a+8*(request.toNat+1) < 2^64
  separate : ∀ t, 1 ≤ t → t ≤ Layout.bf_small_count → ∀ x ∈ lists t,
    a+8*(request.toNat+1) ≤ x.toNat-8 ∨ x.toNat+8*t ≤ a

/-- Exact-size removal separates the whole actual returned allocation. -/
theorem _root_.OCaml.Vm.Gc.BestFitExact.Post.allocated_apart {ra lists s b bs before after}
    (_post : BestFitExact.Post ra (BitVec.ofNat 64 s) before after)
    (physical : BfShape.SmallPhysical lists)
    (lo : 1 ≤ s) (hi : s ≤ Layout.bf_small_count) (selected : lists s = b :: bs) :
    AllocatedApart (b-8#64).toNat (BitVec.ofNat 64 s) (BfShape.popped lists s bs) := by
  have member : b ∈ lists s := by rw [selected]; exact List.mem_cons_self ..
  have bound := physical.bounds s lo hi b member
  have hn := physical.header_nat lo hi member
  have size : (BitVec.ofNat 64 s).toNat = s := by
    have : s < 2^64 := by simp only [Layout.bf_small_count] at hi; omega
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt this]
  constructor
  · rw [hn,size]
    omega
  · intro t lt ht x hx
    rw [hn,size]
    have sep := physical.selected_apart lo hi selected lt ht hx
    omega

/-- Preservation includes a disjoint allocated result, rather than only
well-formed links in the remaining lists. -/
theorem RoutePost.allocated_apart {sp s b request lists bs before after}
    (post : RoutePost sp s b request lists bs before after)
    (input : RouteInput sp s b request lists bs before)
    (physical : BfShape.SmallPhysical lists) :
    AllocatedApart (resultHeader b request (sourceHeader b before.σ.mem)).toNat request
      (routeLists sp s b request lists bs before.σ.mem) := by
  have member : b ∈ lists s.toNat := by rw [input.selected]; simp
  have bounds := physical.bounds s.toNat input.positive input.small b member
  have a := resultHeader_nat (b := b) (hd := sourceHeader b before.σ.mem) input.requestPositive (by simpa only [input.size] using input.larger)
    (by simpa only [input.size] using input.small) (by have := input.geometry.blockHeap; omega)
    (by simpa only [input.size] using bounds.2)
  rw [input.size] at a
  have remnant := post.remnant_size_nat input
  constructor
  · rw [a]
    have := input.larger
    omega
  · intro t lo hi x hx
    rw [a]
    have old : x ∈ BfShape.popped lists s.toNat bs t →
        b.toNat+8*(s.toNat-request.toNat-1)+8*(request.toNat+1) ≤ x.toNat-8 ∨
          x.toNat+8*t ≤ b.toNat+8*(s.toNat-request.toNat-1) := by
      intro hx
      have sep := physical.selected_apart input.positive input.small input.selected lo hi hx
      have := input.larger
      omega
    unfold routeLists BestFitRemnant.finalLists at hx
    split at hx
    · by_cases eq : t = (BestFitRemnant.size b
          (splitMemory sp b request (poppedMemory sp s b before.σ.mem))).toNat
      · simp only [BfShape.inserted,if_pos eq,List.mem_cons] at hx
        rcases hx with rfl | hx
        · right
          rw [eq,remnant]
          exact Nat.le_refl _
        · exact old hx
      · exact old (by simpa only [BfShape.inserted,if_neg eq] using hx)
    · exact old hx

end OCaml.Vm.Gc.BestFitNext

namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable BestFitNext

/-- The final family uses the exact native search snapshot, the selected-head
pop and the remnant wrapper's actual insertion/defer test. -/
def searchLists (R : Nat → BitVec 64) (s : Nat) (b : BitVec 64)
    (lists : Nat → List (BitVec 64)) (bs : List (BitVec 64)) (before : Config) :=
  routeLists (frameSp R) (BitVec.ofNat 64 s) b (R 10) lists bs (searchMemory R before)

/-- Small representation in actual native returned memory, from original
search data plus explicit original physical extents. The existing counter,
returned-result and ABI equations remain in `SearchReturned`. -/
theorem SearchReturned.representation {R lists s b bs before after}
    (post : SearchReturned R lists s b bs before after)
    (input : SearchInput R lists before) (physical : BfShape.SmallPhysical lists) :
    BfShape.SmallShape after.σ.mem (searchLists R s b lists bs before) ∧
    BfShape.SmallHeaders after.σ.mem (searchLists R s b lists bs before) ∧
    BfShape.MapConsistent after.σ.mem (searchLists R s b lists bs before) := by
  obtain ⟨searched,path⟩ := post.path_spec
  have routeInput := input.route_input path.choice path.search
  have result := path.allocation.representation routeInput physical (by
    intro t lo hi x hx
    exact (input.sources t lo hi x hx).geometry.separate)
  have snapshot : searchMemory R before = searched.σ.mem := path.search.memory.symm
  simpa only [searchLists,snapshot] using result

/-- Physical extents survive the actual native bitmap search and allocation
return, using its existing stage witnesses and original input only. -/
theorem SearchReturned.physical {R lists s b bs before after}
    (post : SearchReturned R lists s b bs before after)
    (input : SearchInput R lists before) (physical : BfShape.SmallPhysical lists) :
    BfShape.SmallPhysical (searchLists R s b lists bs before) := by
  obtain ⟨searched,path⟩ := post.path_spec
  have result := path.allocation.physical (input.route_input path.choice path.search) physical
  have snapshot : searchMemory R before = searched.σ.mem := path.search.memory.symm
  simpa only [searchLists,snapshot] using result

/-- All four components together at the same native search return, ready for
later allocations once their request/dispatch/stack obligations are supplied. -/
theorem SearchReturned.smallRepresentation {R lists s b bs before after}
    (post : SearchReturned R lists s b bs before after)
    (input : SearchInput R lists before) (physical : BfShape.SmallPhysical lists) :
    BfShape.SmallRepresentation after.σ.mem (searchLists R s b lists bs before) := by
  have represented := post.representation input physical
  exact ⟨represented.1,represented.2.1,represented.2.2,post.physical input physical⟩

/-- The native search result's allocated block is disjoint from every final
represented free block, including the reinserted remnant when present. -/
theorem SearchReturned.allocated_apart {R lists s b bs before after}
    (post : SearchReturned R lists s b bs before after)
    (input : SearchInput R lists before) (physical : BfShape.SmallPhysical lists) :
    AllocatedApart (resultHeader b (R 10) (sourceHeader b before.σ.mem)).toNat (R 10)
      (searchLists R s b lists bs before) := by
  obtain ⟨searched,path⟩ := post.path_spec
  have routeInput := input.route_input path.choice path.search
  have result := path.allocation.allocated_apart routeInput physical
  have positive : 1 ≤ s := by have := path.choice.larger; omega
  have header : sourceHeader b searched.σ.mem = sourceHeader b before.σ.mem :=
    path.search.read input.toStackConditions
      (input.sources s positive path.choice.small b (by rw [path.choice.selected]; simp)).header_out
  have snapshot : searchMemory R before = searched.σ.mem := path.search.memory.symm
  simpa only [searchLists,snapshot,header] using result

end OCaml.Vm.Gc.BestFitFallback

namespace OCaml.Vm.Gc.BestFitRemnant
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The actual insertion log sets only the decoded remnant's small-class bit. -/
theorem insert_boundedBitmap {v w m} (bounded : BfShape.BoundedBitmap m)
    (lo : 1 ≤ w.toNat) (hi : w.toNat ≤ 16) (heap : DlHeap.heapStart ≤ v.toNat) :
    BfShape.BoundedBitmap (writeLog m (insertLog v w m)) :=
  bounded.set (by omega) (insert_readbacks lo hi heap).bits

/-- Zero-size and sweep-deferral branches have no stores; insertion uses its
native four-byte OR readback. -/
theorem effect_boundedBitmap {v m} (bounded : BfShape.BoundedBitmap m)
    (small : (size v m).toNat ≤ 16) (heap : DlHeap.heapStart ≤ v.toNat) :
    BfShape.BoundedBitmap (writeLog m (effect v m)) := by
  unfold effect
  split
  next ins =>
    have lo : 1 ≤ (size v m).toNat := by
      have nz : (size v m).toNat ≠ 0 := by
        intro h
        exact ins.1 (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    exact insert_boundedBitmap bounded lo small heap
  next => exact bounded
end OCaml.Vm.Gc.BestFitRemnant

namespace OCaml.Vm.Gc.BestFitNext
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The next-size pop consumes the actual saved bitmap, truncates to 32 bits,
and either clears the selected bit or leaves the bitmap unchanged. -/
theorem PopPost.boundedBitmap {sp s b bits request before after}
    (post : PopPost sp s b bits request before after)
    (bounded : BfShape.BoundedBitmap before.σ.mem) (lo : 1 ≤ s.toNat) (hi : s.toNat ≤ 16)
    (bitsRead : bits.setWidth 32 = BfShape.mapBits before.σ.mem) :
    BfShape.BoundedBitmap after.σ.mem := by
  by_cases empty : nextOf b before.σ.mem = 0#64
  · exact bounded.clear (post.bitmap_empty lo hi empty bitsRead)
  · apply bounded.congr
    rw [BfShape.mapBits,post.memory,popLog,if_neg empty]
    apply bytesT_writeLog_out
    have hs := BestFitRemnant.slot_nat hi
    exact ⟨Or.inl (by
      change Layout.sym_bf_small_map+4 ≤ (BestFitRemnant.slot s).toNat
      rw [hs]; simp only [Layout.sym_bf_small_map,Layout.sym_bf_small_fl]; omega),True.intro⟩

/-- Boundedness follows the real pick/pop/split/remnant snapshots. -/
theorem RoutePost.boundedBitmap {sp s b request lists bs before after}
    (post : RoutePost sp s b request lists bs before after)
    (input : RouteInput sp s b request lists bs before)
    (bounded : BfShape.BoundedBitmap before.σ.mem) : BfShape.BoundedBitmap after.σ.mem := by
  obtain ⟨picked,popped,path⟩ := post.path_spec
  have bits : BfShape.mapBits picked.σ.mem = BfShape.mapBits before.σ.mem := by
    apply path.pick.read
    have hm := BestFitRemnant.merge_nat input.small
    change (BestFitRemnant.slot s+8#64).toNat = _ at hm
    change _ ≤ (BestFitRemnant.slot s+8#64).toNat ∨ _
    rw [hm]
    exact Or.inl (by simp only [Layout.sym_bf_small_fl,Layout.sym_bf_small_map]; omega)
  have popBound := path.pop.boundedBitmap (bounded.congr bits) input.positive input.small
    (input.savedBitmap.trans bits.symm)
  have splitBound : BfShape.BoundedBitmap (splitMemory sp b request popped.σ.mem) :=
    popBound.congr (splitMemory_read (splitOutside_static input.geometry (by decide) (by decide)))
  have splitInput := input.split_input path.pick path.pop
  have small : (BestFitRemnant.size b (splitMemory sp b request popped.σ.mem)).toNat ≤ 16 := by
    change (sourceSize (sourceHeader b (splitMemory sp b request popped.σ.mem))).toNat ≤ 16
    rw [splitMemory_header input.geometry,
      smallHeader_size input.requestPositive splitInput.larger splitInput.small]
    have := splitInput.small
    omega
  rw [path.complete.memory,completeLog,writeLog_append]
  exact BestFitRemnant.effect_boundedBitmap splitBound small (by have := input.geometry.blockHeap; omega)

theorem RoutePost.boundedSmallRepresentation {sp s b request lists bs before after}
    (post : RoutePost sp s b request lists bs before after)
    (input : RouteInput sp s b request lists bs before)
    (repr : BfShape.BoundedSmallRepresentation before.σ.mem lists)
    (stack : BfShape.StackApart sp lists) :
    BfShape.BoundedSmallRepresentation after.σ.mem (routeLists sp s b request lists bs before.σ.mem) :=
  ⟨post.smallRepresentation input repr.physical stack,post.boundedBitmap input repr.bounded⟩
end OCaml.Vm.Gc.BestFitNext

namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

theorem SearchReturned.boundedBitmap {R lists s b bs before after}
    (post : SearchReturned R lists s b bs before after)
    (input : SearchInput R lists before) (bounded : BfShape.BoundedBitmap before.σ.mem) :
    BfShape.BoundedBitmap after.σ.mem := by
  obtain ⟨searched,path⟩ := post.path_spec
  have bits : BfShape.mapBits searched.σ.mem = BfShape.mapBits before.σ.mem :=
    path.search.read input.toStackConditions (input.static_out (by decide))
  exact path.allocation.boundedBitmap (input.route_input path.choice path.search) (bounded.congr bits)

theorem SearchReturned.boundedSmallRepresentation {R lists s b bs before after}
    (post : SearchReturned R lists s b bs before after)
    (input : SearchInput R lists before)
    (repr : BfShape.BoundedSmallRepresentation before.σ.mem lists) :
    BfShape.BoundedSmallRepresentation after.σ.mem (searchLists R s b lists bs before) :=
  ⟨post.smallRepresentation input repr.physical,post.boundedBitmap input repr.bounded⟩
end OCaml.Vm.Gc.BestFitFallback
