import OCaml.Vm.Primitives.OutChannelsList
import OCaml.Vm.Sim.HeapAllocAll
import OCaml.Vm.Sim.OutListWalk
import OCaml.Vm.Primitives.Channel.LseekCall

/-!
# `caml_ml_out_channels_list`'s model as a chain of allocations

`outChannelsList` folds over the listed ids (`outChannelIds`), allocating
each id's channel object and then a cons cell. Its heap is `allocAll` of
`listObjs` (channel, cell, channel, cell, …) and its value `listVal`; the
objects are `AllPlaced` at `outListPlaces`' addresses.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm.Primitives

/-- The objects `outChannelsList` allocates from heap size `size`, with `acc`
the list so far. -/
def listObjs (size : Nat) (acc : Val) : List Nat → List Obj
  | [] => []
  | id :: ids => .channel id :: .block 0 [.ptr size 0, acc] :: listObjs (size + 2) (.ptr (size + 1) 0) ids

/-- The list `outChannelsList` returns. -/
def listVal (size : Nat) (acc : Val) : List Nat → Val
  | [] => acc
  | _ :: ids => listVal (size + 2) (.ptr (size + 1) 0) ids

/-- **The model's fold is a chain of allocations.** -/
theorem outList_fold (ids : List Nat) : ∀ (h : Heap) (acc : Val),
    ids.foldl outListStep (h, acc) = (allocAll h (listObjs h.size acc ids), listVal h.size acc ids) := by
  induction ids with
  | nil => intro h acc; rfl
  | cons id ids ih =>
    intro h acc
    simp only [List.foldl_cons, listObjs, listVal, allocAll]
    have e : outListStep (h, acc) id =
        (((h.alloc (.channel id)).1.alloc (.block 0 [.ptr h.size 0, acc])).1, .ptr (h.size + 1) 0) := by
      simp only [outListStep, Heap.loc_alloc, Heap.size_alloc]
    rw [e, ih]
    simp only [Heap.size_alloc]

theorem outChannelsList_alloc (h : Heap) (w : World) :
    outChannelsList h w = (allocAll h (listObjs h.size (.int 0) (outChannelIds w)),
      listVal h.size (.int 0) (outChannelIds w)) := by
  rw [outChannelsList_eq, outList_fold]

theorem blockWords_listObjs (size : Nat) (acc : Val) (ids : List Nat) :
    blockWords (listObjs size acc ids) = 6 * ids.length := by
  induction ids generalizing size acc with
  | nil => rfl
  | cons id ids ih => simp only [listObjs, blockWords, ih, Obj.wosize, List.length_cons, List.length_nil]; omega

/-- **The objects are placed at `outListPlaces`' addresses**: object `i` at
location `size + i`, 24 bytes per object below `y − 16`. -/
theorem listObjs_placed (pl : Place) (ids : List Nat) : ∀ (h : Heap) (acc : Val) (y : Nat),
    (∀ i, i < 2 * ids.length → pl.φ (h.size + i) = some (y - 24 * i - 16)) →
    AllPlaced pl h y (listObjs h.size acc ids) := by
  induction ids with
  | nil => intro _ _ _ _; trivial
  | cons id ids ih =>
    intro h acc y placed
    simp only [listObjs, AllPlaced, Obj.wosize, List.length_cons, List.length_nil]
    refine ⟨?_, ?_, ?_⟩
    · rw [Heap.loc_alloc]; have := placed 0 (by simp); simpa using this
    · rw [Heap.loc_alloc, Heap.size_alloc]; have := placed 1 (by simp; omega)
      rw [this]
    · have := ih ((h.alloc (.channel id)).1.alloc (.block 0 [.ptr h.size 0, acc])).1 (.ptr (h.size + 1) 0)
        (y - 8 * (2 + 1) - 8 * (2 + 1)) fun i hi => by
          rw [Heap.size_alloc, Heap.size_alloc]
          have := placed (i + 2) (by simp at hi ⊢; omega)
          rw [show h.size + 1 + 1 + i = h.size + (i + 2) by omega, this]
          congr 1; omega
      rw [Heap.size_alloc, Heap.size_alloc, show h.size + 1 + 1 = h.size + 2 by omega] at this
      rw [show y - 8 * (2 + 1) - 8 * (0 + 1 + 1 + 1) = y - 8 * (2 + 1) - 8 * (2 + 1) by omega]
      exact this

open Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Primitives.Channel.OutList in
/-- The managed flag reads as set through a sign-extended `lw`. -/
theorem managed_lw {x : BitVec 32} (h : x &&& 4#32 = 4#32) :
    LeanRV64DExecutable.Functions.sign_extend (m := 64) x &&& 4#64 ≠ 0#64 := by
  intro z
  have b : (x &&& 4#32).getLsbD 2 = true := by rw [h]; decide
  have b2 : (LeanRV64DExecutable.Functions.sign_extend (m := 64) x &&& 4#64).getLsbD 2 = false := by rw [z]; decide
  simp only [BitVec.getLsbD_and] at b b2
  simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend] at b2
  simp_all

open Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Primitives.Channel.OutList in
/-- **A channel record is listed exactly when the channel is an open output
channel** (`max == NULL`; every record is managed by the GC). -/
theorem listed_of_chanAt {c : Config} {a : Nat} {ch : Chan} (h : ChanAt c a ch) (pos : 0 < a)
    (fit : a + 80 < 2 ^ 64) :
    Listed c.σ.mem (BitVec.ofNat 64 a) ↔ (ch.isOut && ch.fd != -1) = true := by
  obtain ⟨_, _, _, hmax, _, _, _, _, managed⟩ := h
  have a32 : (BitVec.ofNat 64 a + 32#64).toNat = a + chanOffMax := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp only [chanOffMax]; omega
  have a68 : (BitVec.ofNat 64 a + 68#64).toNat = a + chanOffFlags := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp only [chanOffFlags]; omega
  have flags : bytesVal .lw (read8 c.σ.mem (BitVec.ofNat 64 a + 68#64).toNat) &&& 4#64 ≠ 0#64 := by
    rw [a68, OCaml.Vm.Primitives.Channel.lw_read8]; exact managed_lw managed
  unfold Listed
  rw [a32]
  constructor
  · intro ⟨z, _⟩
    have zt : (word c (a + chanOffMax)).toNat = 0 := by
      change (bytesT c.σ.mem (a + chanOffMax) 8).toNat = 0; rw [z]; rfl
    rw [hmax] at zt
    by_cases f : ch.fd = -1
    · simp only [f, ↓reduceIte] at zt; omega
    · by_cases o : ch.isOut
      · simp [o, f]
      · simp only [f, o, ↓reduceIte, Bool.false_eq_true] at zt; omega
  · intro hb
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
    refine ⟨?_, flags⟩
    have zt : (word c (a + chanOffMax)).toNat = 0 := by rw [hmax]; simp [hb.1, hb.2]
    exact BitVec.eq_of_toNat_eq zt

theorem filterMap_of_some {α β : Type} {g : α → Option β} {f : α → β} :
    ∀ {L : List α}, (∀ x ∈ L, g x = some (f x)) → L.filterMap g = L.map f
  | [], _ => rfl
  | x :: L, h => by
    rw [List.filterMap_cons, h x List.mem_cons_self, List.map_cons,
      filterMap_of_some fun y hy => h y (List.mem_cons_of_mem _ hy)]

open Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Primitives.Channel.OutList OutListWalk in
/-- **The walk's listed records are the model's listed ids' records**, in the
same (newest-first) order. -/
theorem listedRecs_placed {c : Config} {w : World} {cp : ChanPlace}
    (chans : ∀ id, id < w.chans.length → ∃ a ch, w.chans[id]? = some ch ∧ cp id = some a ∧ ChanAt c a ch ∧
      0 < a ∧ a + 80 < 2 ^ 64) :
    listedRecs c.σ.mem (Gc.placedChannels cp w.chans.length) = (outChannelIds w).map fun id => (cp id).getD 0 := by
  have some_ : ∀ id ∈ (List.range w.chans.length).reverse, cp id = some ((cp id).getD 0) := fun id hid => by
    obtain ⟨a, ch, _, hp, _⟩ := chans id (by simpa using hid)
    rw [hp]; rfl
  unfold Gc.placedChannels listedRecs outChannelIds
  rw [filterMap_of_some some_, List.filter_map, ← List.filter_reverse]
  congr 1
  apply List.filter_congr
  intro id hid
  obtain ⟨a, ch, hc, hp, at_, pos, fit⟩ := chans id (by simpa using hid)
  show decide (Listed c.σ.mem (BitVec.ofNat 64 ((cp id).getD 0))) =
    (Option.map (fun c => c.isOut && c.fd != -1) w.chans[id]?).getD false
  rw [hp, hc]
  simp only [Option.getD_some, Option.map_some]
  by_cases b : (ch.isOut && ch.fd != -1) = true
  · rw [b]; exact decide_eq_true ((listed_of_chanAt at_ pos fit).mpr b)
  · have nb : ¬ Listed c.σ.mem (BitVec.ofNat 64 a) := fun l => b ((listed_of_chanAt at_ pos fit).mp l)
    simp only [Bool.not_eq_true] at b
    rw [b]; exact decide_eq_false nb

open Vsa.Machine Vsa.Sim OCaml.Vm OutListWalk in
/-- The records' words from list index `k` on (`NurseryList` from `k`). -/
def ListWords (m : Std.ExtHashMap Nat (BitVec 8)) (Y k : Nat) (ids : List Nat) (R : Nat → Nat) : Prop :=
  ∀ t id, ids[t]? = some id → ∀ x ∈ objWords Y (k + t) (R id), bytesT m x.1 8 = x.2

open Vsa.Machine Vsa.Sim OCaml.Vm OutListWalk in
theorem ListWords.of_nursery {m : Std.ExtHashMap Nat (BitVec 8)} {Y : Nat} {ids : List Nat} {R : Nat → Nat}
    (h : NurseryList m Y (ids.map R)) : ListWords m Y 0 ids R := fun t id hid x hx => by
  exact h t (R id) (by rw [List.getElem?_map, hid]; rfl) x (by simpa using hx)

open Vsa.Machine Vsa.Sim OCaml.Vm OutListWalk in
/-- **The model's new objects are represented** at their nursery addresses:
the `j`-th listed id's channel object (header, `channel_operations`, the
record) and its cons cell (header, the channel object, the previous list). -/
theorem listObjs_objAt {c : Config} {pl : Place} {cp : ChanPlace} {R : Nat → Nat} {Y : Nat}
    (yFit : Y < 2 ^ 64) :
    ∀ (ids : List Nat) (k size : Nat) (acc : Val), (∀ id ∈ ids, cp id = some (R id) ∧ R id < 2 ^ 64) →
      ListWords c.σ.mem Y k ids R →
      valWord pl acc = some (resWord Y k) →
      (∀ i, i < 2 * ids.length → pl.φ (size + i) = some (Y - 24 * (2 * k + i) - 16)) →
      48 * (k + ids.length) ≤ Y →
      ∀ i o, (listObjs size acc ids)[i]? = some o → ObjAt c pl cp (Y - 24 * (2 * k + i) - 16) o := by
  intro ids
  induction ids with
  | nil => intro k size acc _ _ _ _ _ i o h; simp [listObjs] at h
  | cons id ids ih =>
    intro k size acc hR words accRepr placed room i o hio
    obtain ⟨hRid, rFit⟩ := hR id List.mem_cons_self
    have w0 := words 0 id rfl
    simp only [Nat.add_zero, objWords, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at w0
    obtain ⟨wh, wo, wr, wch, wcar, wcdr⟩ := w0
    simp only [List.length_cons] at room placed
    have p0 : pl.φ size = some (Y - 48 * k - 16) := by
      have := placed 0 (by omega); rw [Nat.add_zero] at this; rw [this]; congr 1; omega
    have p1 : pl.φ (size + 1) = some (Y - 48 * k - 40) := by
      rw [placed 1 (by omega)]; congr 1; omega
    match i, hio with
    | 0, hio =>
      simp only [listObjs, List.getElem?_cons_zero, Option.some.injEq] at hio
      subst hio
      have a8 : Y - 24 * (2 * k + 0) - 16 - 8 = Y - 48 * k - 24 := by omega
      have a0 : Y - 24 * (2 * k + 0) - 16 = Y - 48 * k - 16 := by omega
      have a1 : Y - 24 * (2 * k + 0) - 16 + 8 = Y - 48 * k - 8 := by omega
      refine ⟨?_, ?_, ?_⟩
      · unfold word; rw [a8, wh]; exact Gc.customHeader_ok
      · unfold word; rw [a0, wo]; rfl
      · unfold word; rw [a1, wr, hRid, toNat_ofNat_small rFit]
    | 1, hio =>
      simp only [listObjs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hio
      subst hio
      have a8 : Y - 24 * (2 * k + 1) - 16 - 8 = Y - 48 * k - 48 := by omega
      have a0 : Y - 24 * (2 * k + 1) - 16 = Y - 48 * k - 40 := by omega
      have a1 : Y - 24 * (2 * k + 1) - 16 + 8 * 1 = Y - 48 * k - 32 := by omega
      refine ⟨?_, ?_⟩
      · unfold word; rw [a8, wch]
        show (2048#64 : BitVec 64).toNat % 256 = 0 ∧ (2048#64 : BitVec 64).toNat / 1024 = 2
        decide
      · intro f v hv
        match f, hv with
        | 0, hv =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
          subst hv
          show (pl.φ size).map (fun a => BitVec.ofNat 64 (a + 8 * 0)) = some (word c (_ + 8 * 0))
          rw [p0, Nat.mul_zero, Nat.add_zero, Nat.add_zero]
          unfold word; rw [a0, wcar]; rfl
        | 1, hv =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hv
          subst hv
          rw [accRepr]; unfold word; rw [a1, wcdr]
        | n + 2, hv => simp at hv
    | i + 2, hio =>
      simp only [listObjs, List.getElem?_cons_succ] at hio
      have r := ih (k + 1) (size + 2) (.ptr (size + 1) 0) (fun id' h' => hR id' (List.mem_cons_of_mem _ h'))
        (fun t id' hid x hx => by
          have := words (t + 1) id' (by simpa using hid) x
          rw [show k + 1 + t = k + (t + 1) by omega] at hx; exact this hx)
        (by
          show (pl.φ (size + 1)).map (fun a => BitVec.ofNat 64 (a + 8 * 0)) = _
          rw [p1]
          simp only [Option.map_some, Nat.mul_zero, Nat.add_zero, resWord, Nat.add_one_ne_zero, ↓reduceIte]
          congr 2; omega)
        (fun i' hi' => by
          rw [show size + 2 + i' = size + (i' + 2) by omega, placed (i' + 2) (by omega)]
          congr 2; omega)
        (by omega) i o hio
      rw [show 2 * (k + 1) + i = 2 * k + (i + 2) by omega] at r
      exact r

end OCaml.Vm.Sim
