import OCaml.Vm.Gc.Skiplist

/-!
# The global roots across one insertion

`caml_register_generational_global_root` and `caml_modify_generational_global_root`
insert into `caml_global_roots_young` or `caml_global_roots_old`
(`Skiplist.Ops.insert`). The other lists' footprints miss the inserted list's
and newlib's, so they keep their shapes and keys (`keep_list`); the inserted
list gains exactly the root (`GlobalRoots.insert_young`, `…_old`). A list's
cells are determined by memory (`Ops.unique`, from `Chain.unique`).
-/

namespace OCaml.Vm.Gc.Skiplist
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Primitives

variable {Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop}
  {foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop}

/-- One of the three global-root lists. -/
def IsList (sk : Nat) : Prop := sk = globalRoots ∨ sk = globalRootsYoung ∨ sk = globalRootsOld

/-- The three lists' footprints. -/
def ListsFoot (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : Prop :=
  ∃ sk cells, IsList sk ∧ Shape m sk cells ∧ foot m sk cells a

theorem Ops.unique (ops : Ops Shape foot) {m : Std.ExtHashMap Nat (BitVec 8)} {sk : Nat}
    {c1 c2 : List (BitVec 64)} (h1 : Shape m sk c1) (h2 : Shape m sk c2) : c1 = c2 :=
  Chain.unique _ _ _ (ops.level0 _ _ _ h1) (ops.level0 _ _ _ h2)

/-- **A list whose footprint is kept** keeps its shape, footprint and keys. -/
theorem Ops.keep_list (ops : Ops Shape foot) {m m' : Std.ExtHashMap Nat (BitVec 8)} {sk : Nat}
    {cells : List (BitVec 64)} (sh : Shape m sk cells)
    (agree : ∀ a, foot m sk cells a → (m'[a]?).getD 0 = (m[a]?).getD 0) :
    Shape m' sk cells ∧ (∀ a, foot m' sk cells a ↔ foot m sk cells a) ∧ keys m' cells = keys m cells := by
  obtain ⟨sh', ft⟩ := ops.frame m m' sk cells sh agree
  refine ⟨sh', ft, ?_⟩
  unfold keys
  apply List.map_congr_left
  intro x hx
  exact word_observed _ fun i hi => agree _ (ops.cell m sk cells sh x hx i (by omega))

/-- The footprint facts an insertion leaves for the lists it does not touch:
they miss the allocator's footprint and keep their bytes outside the touched
list's footprint and the allocator's. -/
structure InsertFrame (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (H : List (Nat × Nat)) (sk : Nat) (cells : List (BitVec 64)) (m m' : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  live : ∀ sk' cells', Shape m sk' cells' → ∀ a, foot m sk' cells' a → ¬ VsaIris.VsaHeap.vsaFoot H a
  seed : ∀ sk' cells', Shape m sk' cells' → ∀ a, foot m sk' cells' a → a < randomSeed ∨ randomSeed + 4 ≤ a
  kept : ∀ a, ¬ foot m sk cells a → ¬ VsaIris.VsaHeap.vsaFoot H a → a < Vsa.Sim.DlHeap.heapEnd →
    (a < randomSeed ∨ randomSeed + 4 ≤ a) → (m'[a]?).getD 0 = (m[a]?).getD 0

/-- Across a call on the young list, the old list keeps its shape and footprint. -/
theorem GlobalRoots.old_kept (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {cy : List (BitVec 64)} (shy : Shape m globalRootsYoung cy)
    (fr : InsertFrame Shape foot H globalRootsYoung cy m m') {co : List (BitVec 64)}
    (sho : Shape m globalRootsOld co) :
    Shape m' globalRootsOld co ∧ (∀ a, foot m' globalRootsOld co a ↔ foot m globalRootsOld co a) := by
  obtain ⟨c1, sh1, -⟩ := g.roots
  obtain ⟨sh', ft, -⟩ := ops.keep_list sho fun a f =>
    fr.kept a (fun y => (g.apart c1 cy co a sh1 shy sho).2 y f) (fr.live _ _ sho a f)
      (ops.low _ _ _ sho a f) (fr.seed _ _ sho a f)
  exact ⟨sh', ft⟩

/-- Across a call on the old list, the young list keeps its shape and footprint. -/
theorem GlobalRoots.young_kept (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {co : List (BitVec 64)} (sho : Shape m globalRootsOld co)
    (fr : InsertFrame Shape foot H globalRootsOld co m m') {cy : List (BitVec 64)}
    (shy : Shape m globalRootsYoung cy) :
    Shape m' globalRootsYoung cy ∧ (∀ a, foot m' globalRootsYoung cy a ↔ foot m globalRootsYoung cy a) := by
  obtain ⟨c1, sh1, -⟩ := g.roots
  obtain ⟨sh', ft, -⟩ := ops.keep_list shy fun a f =>
    fr.kept a (fun o => (g.apart c1 cy co a sh1 shy sho).2 f o) (fr.live _ _ shy a f)
      (ops.low _ _ _ shy a f) (fr.seed _ _ shy a f)
  exact ⟨sh', ft⟩

/-- Across a call on the young list, `caml_global_roots` keeps its shape and footprint. -/
theorem GlobalRoots.roots_kept_young (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {cy : List (BitVec 64)} (shy : Shape m globalRootsYoung cy)
    (fr : InsertFrame Shape foot H globalRootsYoung cy m m') {c1 : List (BitVec 64)}
    (sh1 : Shape m globalRoots c1) :
    Shape m' globalRoots c1 ∧ (∀ a, foot m' globalRoots c1 a ↔ foot m globalRoots c1 a) := by
  obtain ⟨c3, sh3, -⟩ := g.old
  obtain ⟨sh', ft, -⟩ := ops.keep_list sh1 fun a f =>
    fr.kept a ((g.apart c1 cy c3 a sh1 shy sh3).1 f).1 (fr.live _ _ sh1 a f) (ops.low _ _ _ sh1 a f)
      (fr.seed _ _ sh1 a f)
  exact ⟨sh', ft⟩

/-- Across a call on the old list, `caml_global_roots` keeps its shape and footprint. -/
theorem GlobalRoots.roots_kept_old (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {co : List (BitVec 64)} (sho : Shape m globalRootsOld co)
    (fr : InsertFrame Shape foot H globalRootsOld co m m') {c1 : List (BitVec 64)}
    (sh1 : Shape m globalRoots c1) :
    Shape m' globalRoots c1 ∧ (∀ a, foot m' globalRoots c1 a ↔ foot m globalRoots c1 a) := by
  obtain ⟨c2, sh2, -⟩ := g.young
  obtain ⟨sh', ft, -⟩ := ops.keep_list sh1 fun a f =>
    fr.kept a ((g.apart c1 c2 co a sh1 sh2 sho).1 f).2 (fr.live _ _ sh1 a f) (ops.low _ _ _ sh1 a f)
      (fr.seed _ _ sh1 a f)
  exact ⟨sh', ft⟩

/-- **The young list replaced**: the other lists keep their shapes and keys;
the new young keys stay apart from them. -/
theorem GlobalRoots.replace_young (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {cy cy' : List (BitVec 64)} (shy : Shape m globalRootsYoung cy)
    (shy' : Shape m' globalRootsYoung cy') (apartKeys : ∀ k ∈ keys m' cy', k ∉ rs ∧ k ∉ os)
    (footIn : ∀ a, foot m' globalRootsYoung cy' a → foot m globalRootsYoung cy a ∨ VsaIris.VsaHeap.vsaFoot H a)
    (fr : InsertFrame Shape foot H globalRootsYoung cy m m') :
    GlobalRoots Shape foot m' rs (keys m' cy') os := by
  obtain ⟨c1, sh1, k1⟩ := g.roots
  obtain ⟨c3, sh3, k3⟩ := g.old
  have ap := fun a => g.apart c1 cy c3 a sh1 shy sh3
  obtain ⟨sh1', ft1, ks1⟩ := ops.keep_list sh1 fun a f => fr.kept a ((ap a).1 f).1 (fr.live _ _ sh1 a f)
    (ops.low _ _ _ sh1 a f) (fr.seed _ _ sh1 a f)
  obtain ⟨sh3', ft3, ks3⟩ := ops.keep_list sh3 fun a f =>
    fr.kept a (fun y => (ap a).2 y f) (fr.live _ _ sh3 a f) (ops.low _ _ _ sh3 a f) (fr.seed _ _ sh3 a f)
  have nd := g.distinct
  simp only [List.nodup_append, List.mem_append] at nd
  refine { roots := ⟨c1, sh1', by rw [ks1, k1]⟩, young := ⟨cy', shy', rfl⟩, old := ⟨c3, sh3', by rw [ks3, k3]⟩,
           distinct := ?_, apart := ?_ }
  · simp only [List.nodup_append, List.mem_append]
    refine ⟨⟨nd.1.1, ops.nodup _ _ _ shy', ?_⟩, nd.2.1, ?_⟩
    · intro a ha b hb e
      subst e
      exact (apartKeys a hb).1 ha
    · intro a ha b hb e
      subst e
      rcases ha with ha | ha
      · exact nd.2.2 a (Or.inl ha) a hb rfl
      · exact (apartKeys a ha).2 hb
  · intro d1 d2 d3 a s1 s2 s3
    have e1 := ops.unique s1 sh1'
    have e2 := ops.unique s2 shy'
    have e3 := ops.unique s3 sh3'
    subst e1 e2 e3
    constructor
    · intro f1
      have f1m := (ft1 a).1 f1
      refine ⟨fun f2 => ?_, fun f3 => ((ap a).1 f1m).2 ((ft3 a).1 f3)⟩
      rcases footIn a f2 with y | v
      · exact ((ap a).1 f1m).1 y
      · exact fr.live _ _ sh1 a f1m v
    · intro f2 f3
      have f3m := (ft3 a).1 f3
      rcases footIn a f2 with y | v
      · exact (ap a).2 y f3m
      · exact fr.live _ _ sh3 a f3m v

/-- **The old list replaced**, the others unchanged. -/
theorem GlobalRoots.replace_old (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {co co' : List (BitVec 64)} (sho : Shape m globalRootsOld co)
    (sho' : Shape m' globalRootsOld co') (apartKeys : ∀ k ∈ keys m' co', k ∉ rs ∧ k ∉ ys)
    (footIn : ∀ a, foot m' globalRootsOld co' a → foot m globalRootsOld co a ∨ VsaIris.VsaHeap.vsaFoot H a)
    (fr : InsertFrame Shape foot H globalRootsOld co m m') :
    GlobalRoots Shape foot m' rs ys (keys m' co') := by
  obtain ⟨c1, sh1, k1⟩ := g.roots
  obtain ⟨c2, sh2, k2⟩ := g.young
  have ap := fun a => g.apart c1 c2 co a sh1 sh2 sho
  obtain ⟨sh1', ft1, ks1⟩ := ops.keep_list sh1 fun a f => fr.kept a ((ap a).1 f).2 (fr.live _ _ sh1 a f)
    (ops.low _ _ _ sh1 a f) (fr.seed _ _ sh1 a f)
  obtain ⟨sh2', ft2, ks2⟩ := ops.keep_list sh2 fun a f => fr.kept a ((ap a).2 f) (fr.live _ _ sh2 a f)
    (ops.low _ _ _ sh2 a f) (fr.seed _ _ sh2 a f)
  have nd := g.distinct
  simp only [List.nodup_append, List.mem_append] at nd
  refine { roots := ⟨c1, sh1', by rw [ks1, k1]⟩, young := ⟨c2, sh2', by rw [ks2, k2]⟩, old := ⟨co', sho', rfl⟩,
           distinct := ?_, apart := ?_ }
  · simp only [List.nodup_append, List.mem_append]
    refine ⟨nd.1, ops.nodup _ _ _ sho', ?_⟩
    intro a ha b hb e
    subst e
    rcases ha with ha | ha
    · exact (apartKeys a hb).1 ha
    · exact (apartKeys a hb).2 ha
  · intro d1 d2 d3 a s1 s2 s3
    have e1 := ops.unique s1 sh1'
    have e2 := ops.unique s2 sh2'
    have e3 := ops.unique s3 sho'
    subst e1 e2 e3
    constructor
    · intro f1
      have f1m := (ft1 a).1 f1
      refine ⟨fun f2 => ((ap a).1 f1m).1 ((ft2 a).1 f2), fun f3 => ?_⟩
      rcases footIn a f3 with o | v
      · exact ((ap a).1 f1m).2 o
      · exact fr.live _ _ sh1 a f1m v
    · intro f2 f3
      have f2m := (ft2 a).1 f2
      rcases footIn a f3 with o | v
      · exact (ap a).2 f2m o
      · exact fr.live _ _ sh2 a f2m v

/-- The keys after an insertion: the old ones and the key. -/
theorem insert_keys {m m' : Std.ExtHashMap Nat (BitVec 8)} {cells cells' : List (BitVec 64)} {r : BitVec 64}
    {xs : List (BitVec 64)} (hx : keys m cells = xs) (kin : r ∈ keys m' cells')
    (kold : ∀ k ∈ keys m cells, k ∈ keys m' cells') (kout : ∀ k ∈ keys m' cells', k = r ∨ k ∈ keys m cells) :
    ∀ k, k ∈ keys m' cells' ↔ k = r ∨ k ∈ xs := fun k => by
  rw [← hx]; exact ⟨kout k, fun h => h.elim (fun e => e ▸ kin) (kold k)⟩

/-- The keys after a removal: the old ones but the key. -/
theorem remove_keys {m m' : Std.ExtHashMap Nat (BitVec 8)} {cells cells' : List (BitVec 64)} {r : BitVec 64}
    {xs : List (BitVec 64)} (hx : keys m cells = xs) (kout : r ∉ keys m' cells')
    (kold : ∀ k ∈ keys m cells, k ≠ r → k ∈ keys m' cells') (ksub : ∀ k ∈ keys m' cells', k ∈ keys m cells) :
    ∀ k, k ∈ keys m' cells' ↔ k ≠ r ∧ k ∈ xs := fun k => by
  rw [← hx]
  exact ⟨fun h => ⟨fun e => kout (e ▸ h), ksub k h⟩, fun ⟨ne, h⟩ => kold k h ne⟩

/-- **The young list gains a root** apart from the other lists. -/
theorem GlobalRoots.insert_young (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {r : BitVec 64} (fresh : r ∉ rs ∧ r ∉ os)
    {cy cy' : List (BitVec 64)} (shy : Shape m globalRootsYoung cy) (hy : keys m cy = ys)
    (shy' : Shape m' globalRootsYoung cy') (kin : r ∈ keys m' cy')
    (kold : ∀ k ∈ keys m cy, k ∈ keys m' cy') (kout : ∀ k ∈ keys m' cy', k = r ∨ k ∈ keys m cy)
    (footIn : ∀ a, foot m' globalRootsYoung cy' a → foot m globalRootsYoung cy a ∨ VsaIris.VsaHeap.vsaFoot H a)
    (fr : InsertFrame Shape foot H globalRootsYoung cy m m') :
    GlobalRoots Shape foot m' rs (keys m' cy') os ∧ ∀ k, k ∈ keys m' cy' ↔ k = r ∨ k ∈ ys := by
  have mem := insert_keys hy kin kold kout
  have nd := g.distinct
  simp only [List.nodup_append, List.mem_append] at nd
  refine ⟨g.replace_young ops shy shy' (fun k hk => ?_) footIn fr, mem⟩
  rcases (mem k).1 hk with rfl | hy'
  · exact fresh
  · exact ⟨fun h => nd.1.2.2 k h k hy' rfl, fun h => nd.2.2 k (Or.inr hy') k h rfl⟩

/-- **The old list gains a root** apart from the other lists. -/
theorem GlobalRoots.insert_old (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {r : BitVec 64} (fresh : r ∉ rs ∧ r ∉ ys)
    {co co' : List (BitVec 64)} (sho : Shape m globalRootsOld co) (ho : keys m co = os)
    (sho' : Shape m' globalRootsOld co') (kin : r ∈ keys m' co')
    (kold : ∀ k ∈ keys m co, k ∈ keys m' co') (kout : ∀ k ∈ keys m' co', k = r ∨ k ∈ keys m co)
    (footIn : ∀ a, foot m' globalRootsOld co' a → foot m globalRootsOld co a ∨ VsaIris.VsaHeap.vsaFoot H a)
    (fr : InsertFrame Shape foot H globalRootsOld co m m') :
    GlobalRoots Shape foot m' rs ys (keys m' co') ∧ ∀ k, k ∈ keys m' co' ↔ k = r ∨ k ∈ os := by
  have mem := insert_keys ho kin kold kout
  have nd := g.distinct
  simp only [List.nodup_append, List.mem_append] at nd
  refine ⟨g.replace_old ops sho sho' (fun k hk => ?_) footIn fr, mem⟩
  rcases (mem k).1 hk with rfl | ho'
  · exact fresh
  · exact ⟨fun h => nd.2.2 k (Or.inl h) k ho' rfl, fun h => nd.2.2 k (Or.inr h) k ho' rfl⟩

/-- **The young list loses a root.** -/
theorem GlobalRoots.remove_young (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {r : BitVec 64}
    {cy cy' : List (BitVec 64)} (shy : Shape m globalRootsYoung cy) (hy : keys m cy = ys)
    (shy' : Shape m' globalRootsYoung cy') (kout : r ∉ keys m' cy')
    (kold : ∀ k ∈ keys m cy, k ≠ r → k ∈ keys m' cy') (ksub : ∀ k ∈ keys m' cy', k ∈ keys m cy)
    (footIn : ∀ a, foot m' globalRootsYoung cy' a → foot m globalRootsYoung cy a)
    (fr : InsertFrame Shape foot H globalRootsYoung cy m m') :
    GlobalRoots Shape foot m' rs (keys m' cy') os ∧ ∀ k, k ∈ keys m' cy' ↔ k ≠ r ∧ k ∈ ys := by
  have mem := remove_keys hy kout kold ksub
  have nd := g.distinct
  simp only [List.nodup_append, List.mem_append] at nd
  refine ⟨g.replace_young ops shy shy' (fun k hk => ?_) (fun a f => Or.inl (footIn a f)) fr, mem⟩
  have hy' := ((mem k).1 hk).2
  exact ⟨fun h => nd.1.2.2 k h k hy' rfl, fun h => nd.2.2 k (Or.inr hy') k h rfl⟩

/-- **The old list loses a root.** -/
theorem GlobalRoots.remove_old (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {r : BitVec 64}
    {co co' : List (BitVec 64)} (sho : Shape m globalRootsOld co) (ho : keys m co = os)
    (sho' : Shape m' globalRootsOld co') (kout : r ∉ keys m' co')
    (kold : ∀ k ∈ keys m co, k ≠ r → k ∈ keys m' co') (ksub : ∀ k ∈ keys m' co', k ∈ keys m co)
    (footIn : ∀ a, foot m' globalRootsOld co' a → foot m globalRootsOld co a)
    (fr : InsertFrame Shape foot H globalRootsOld co m m') :
    GlobalRoots Shape foot m' rs ys (keys m' co') ∧ ∀ k, k ∈ keys m' co' ↔ k ≠ r ∧ k ∈ os := by
  have mem := remove_keys ho kout kold ksub
  have nd := g.distinct
  simp only [List.nodup_append, List.mem_append] at nd
  refine ⟨g.replace_old ops sho sho' (fun k hk => ?_) (fun a f => Or.inl (footIn a f)) fr, mem⟩
  have ho' := ((mem k).1 hk).2
  exact ⟨fun h => nd.2.2 k (Or.inl h) k ho' rfl, fun h => nd.2.2 k (Or.inr h) k ho' rfl⟩

/-- **The global roots across memory that agrees on the three lists'
footprints.** -/
theorem GlobalRoots.keep (ops : Ops Shape foot) {m m' : Std.ExtHashMap Nat (BitVec 8)}
    {rs ys os : List (BitVec 64)} (g : GlobalRoots Shape foot m rs ys os)
    (agree : ∀ sk cells, (sk = globalRoots ∨ sk = globalRootsYoung ∨ sk = globalRootsOld) → Shape m sk cells →
      ∀ a, foot m sk cells a → (m'[a]?).getD 0 = (m[a]?).getD 0) :
    GlobalRoots Shape foot m' rs ys os := by
  obtain ⟨c1, sh1, k1⟩ := g.roots
  obtain ⟨c2, sh2, k2⟩ := g.young
  obtain ⟨c3, sh3, k3⟩ := g.old
  obtain ⟨sh1', ft1, ks1⟩ := ops.keep_list sh1 (agree _ _ (Or.inl rfl) sh1)
  obtain ⟨sh2', ft2, ks2⟩ := ops.keep_list sh2 (agree _ _ (Or.inr (Or.inl rfl)) sh2)
  obtain ⟨sh3', ft3, ks3⟩ := ops.keep_list sh3 (agree _ _ (Or.inr (Or.inr rfl)) sh3)
  refine { roots := ⟨c1, sh1', by rw [ks1, k1]⟩, young := ⟨c2, sh2', by rw [ks2, k2]⟩,
           old := ⟨c3, sh3', by rw [ks3, k3]⟩, distinct := g.distinct, apart := ?_ }
  intro d1 d2 d3 a s1 s2 s3
  have e1 := ops.unique s1 sh1'
  have e2 := ops.unique s2 sh2'
  have e3 := ops.unique s3 sh3'
  subst e1 e2 e3
  have ap := g.apart d1 d2 d3 a sh1 sh2 sh3
  rw [ft1, ft2, ft3]
  exact ap

/-- **The global roots across memory that agrees below the arena** (native
frame stores): every list keeps its shape, footprint and keys. -/
theorem GlobalRoots.keep_low (ops : Ops Shape foot) {m m' : Std.ExtHashMap Nat (BitVec 8)}
    {rs ys os : List (BitVec 64)} (g : GlobalRoots Shape foot m rs ys os)
    (agree : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → (m'[a]?).getD 0 = (m[a]?).getD 0) :
    GlobalRoots Shape foot m' rs ys os ∧
      ∀ sk cells, Shape m sk cells → Shape m' sk cells ∧ (∀ a, foot m' sk cells a ↔ foot m sk cells a) ∧
        keys m' cells = keys m cells :=
  ⟨g.keep ops fun _ _ _ sh a f => agree a (ops.low _ _ _ sh a f),
    fun _ _ sh => ops.keep_list sh fun a f => agree a (ops.low _ _ _ sh a f)⟩


/-- **The lists' footprints after a call on the young list** lie in the old
ones and newlib's footprint. -/
theorem GlobalRoots.feet_young (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {cy cy' : List (BitVec 64)} (shy : Shape m globalRootsYoung cy)
    (shy' : Shape m' globalRootsYoung cy')
    (footIn : ∀ a, foot m' globalRootsYoung cy' a → foot m globalRootsYoung cy a ∨ VsaIris.VsaHeap.vsaFoot H a)
    (fr : InsertFrame Shape foot H globalRootsYoung cy m m') :
    ∀ a, ListsFoot Shape foot m' a → ListsFoot Shape foot m a ∨ VsaIris.VsaHeap.vsaFoot H a := by
  rintro a ⟨sk, cells, list, sh, f⟩
  rcases list with rfl | rfl | rfl
  · obtain ⟨c1, sh1, -⟩ := g.roots
    obtain ⟨sh1', ft⟩ := g.roots_kept_young ops shy fr sh1
    have e := ops.unique sh sh1'
    subst e
    exact Or.inl ⟨_, _, Or.inl rfl, sh1, (ft a).1 f⟩
  · have e := ops.unique sh shy'
    subst e
    rcases footIn a f with o | v
    · exact Or.inl ⟨_, _, Or.inr (Or.inl rfl), shy, o⟩
    · exact Or.inr v
  · obtain ⟨co, sho, -⟩ := g.old
    obtain ⟨sho', ft⟩ := g.old_kept ops shy fr sho
    have e := ops.unique sh sho'
    subst e
    exact Or.inl ⟨_, _, Or.inr (Or.inr rfl), sho, (ft a).1 f⟩

/-- **The lists' footprints after a call on the old list.** -/
theorem GlobalRoots.feet_old (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {co co' : List (BitVec 64)} (sho : Shape m globalRootsOld co)
    (sho' : Shape m' globalRootsOld co')
    (footIn : ∀ a, foot m' globalRootsOld co' a → foot m globalRootsOld co a ∨ VsaIris.VsaHeap.vsaFoot H a)
    (fr : InsertFrame Shape foot H globalRootsOld co m m') :
    ∀ a, ListsFoot Shape foot m' a → ListsFoot Shape foot m a ∨ VsaIris.VsaHeap.vsaFoot H a := by
  rintro a ⟨sk, cells, list, sh, f⟩
  rcases list with rfl | rfl | rfl
  · obtain ⟨c1, sh1, -⟩ := g.roots
    obtain ⟨sh1', ft⟩ := g.roots_kept_old ops sho fr sh1
    have e := ops.unique sh sh1'
    subst e
    exact Or.inl ⟨_, _, Or.inl rfl, sh1, (ft a).1 f⟩
  · obtain ⟨cy, shy, -⟩ := g.young
    obtain ⟨shy', ft⟩ := g.young_kept ops sho fr shy
    have e := ops.unique sh shy'
    subst e
    exact Or.inl ⟨_, _, Or.inr (Or.inl rfl), shy, (ft a).1 f⟩
  · have e := ops.unique sh sho'
    subst e
    rcases footIn a f with o | v
    · exact Or.inl ⟨_, _, Or.inr (Or.inr rfl), sho, o⟩
    · exact Or.inr v

/-- **The lists' footprints across memory that agrees on them.** -/
theorem GlobalRoots.listsFoot_keep (ops : Ops Shape foot) {m m' : Std.ExtHashMap Nat (BitVec 8)}
    {rs ys os : List (BitVec 64)} (g : GlobalRoots Shape foot m rs ys os)
    (agree : ∀ a, ListsFoot Shape foot m a → (m'[a]?).getD 0 = (m[a]?).getD 0) (a : Nat) :
    ListsFoot Shape foot m' a ↔ ListsFoot Shape foot m a := by
  have keep : ∀ sk cells, IsList sk → Shape m sk cells →
      Shape m' sk cells ∧ (∀ a, foot m' sk cells a ↔ foot m sk cells a) ∧ keys m' cells = keys m cells :=
    fun sk cells list sh => ops.keep_list sh fun a f => agree a ⟨sk, cells, list, sh, f⟩
  constructor
  · rintro ⟨sk, cells, list, sh', f⟩
    have cellsM : ∃ cs, Shape m sk cs := by
      rcases list with rfl | rfl | rfl
      · obtain ⟨cs, sh, -⟩ := g.roots; exact ⟨cs, sh⟩
      · obtain ⟨cs, sh, -⟩ := g.young; exact ⟨cs, sh⟩
      · obtain ⟨cs, sh, -⟩ := g.old; exact ⟨cs, sh⟩
    obtain ⟨cs, sh⟩ := cellsM
    obtain ⟨shm', ft, -⟩ := keep _ _ list sh
    have e := ops.unique sh' shm'
    subst e
    exact ⟨sk, cells, list, sh, (ft a).1 f⟩
  · rintro ⟨sk, cells, list, sh, f⟩
    obtain ⟨sh', ft, -⟩ := keep _ _ list sh
    exact ⟨sk, cells, list, sh', (ft a).2 f⟩

end OCaml.Vm.Gc.Skiplist
