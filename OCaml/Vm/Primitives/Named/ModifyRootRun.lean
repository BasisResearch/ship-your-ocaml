import OCaml.Vm.Primitives.Named.ModifyRoot
import OCaml.Vm.Primitives.Named.RegisterRootRun

/-!
# `caml_modify_generational_global_root(r, v)` as a machine run

The function classifies the new value `v` and the old `w = *r` (immediate,
young, `In_heap` by the page table, other), removes `r` from the lists it
leaves, inserts it in the one it joins, and stores `*r = v`. The lists keep
the invariant `RootAt`: a young value's root is in the young list only, an
old value's in either, any other value's in neither.

Between the prologue and the store the run keeps `Acting`: the frame and the
callee-saved registers, the global roots, and every byte outside the lists'
footprints, newlib's footprint and the callees' stack window, relative to the
memory after the prologue. Each skiplist call steps it (`Acting.call`).
-/

namespace OCaml.Vm.Primitives.Named.ModifyRoot
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm OCaml.Vm.Primitives OCaml.Vm.Gc OCaml.Vm.Gc.Skiplist
open OCaml.Vm.Boot.Startup (NativeFrame HeapReady nativeFrameBase)
open NamedValue (regsAt regsAt_of gpr_some gpr_some_of gprReg_ne_htif wl_nil)
open RegisterRoot (Young Old rootValue YoungAt ListsFoot IsList lists_kept)

/-- **Where a generational root lies** by its value `w`: a young value's
root in the young list only, an old value's in either, any other value's in
neither. -/
structure RootAt (start stop : BitVec 64) (cls : Nat → Nat) (w r : BitVec 64) (ys os : List (BitVec 64)) :
    Prop where
  young : Young start stop w → r ∈ ys ∧ r ∉ os
  old : Old start stop cls w → r ∈ ys ∨ r ∈ os
  none : ¬ Young start stop w → ¬ Old start stop cls w → r ∉ ys ∧ r ∉ os

variable {Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop}
  {foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop}

/-- **Between the prologue and the store**: `s0 = v`, `s1 = r`, the 32-byte
frame, the global roots `rs ys os`, newlib's and the lists' footprints within
those after the prologue (`m1`, `H0`), every other byte outside the callees'
stack window as after the prologue. -/
structure Acting (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (H0 : List (Nat × Nat)) (m1 : Std.ExtHashMap Nat (BitVec 8)) (sp v r : BitVec 64) (rs : List (BitVec 64))
    (c x : Config) (ys os : List (BitVec 64)) : Prop where
  good : GoodState x.σ
  image : ExecutableImage x
  minstret : ∃ w, x.σ.regs.get? Register.minstret = some w
  tick : x.tick < 2
  link : ∃ l : BitVec 64, gprGet x.σ 1 = some l ∧ l.toNat % 4 = 0
  stack : gprGet x.σ 2 = some (sp + 18446744073709551584#64)
  s0 : gprGet x.σ 8 = some v
  s1 : gprGet x.σ 9 = some r
  a0 : (gprGet x.σ 10).isSome
  saved : ∀ n ∈ [18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet x.σ n = gprGet c.σ n
  gp : gpr x 3 = gpr c 3
  output : x.σ.sailOutput = c.σ.sailOutput
  heap : ∃ H cap, HeapReady H cap x ∧
    ∀ a, VsaIris.VsaHeap.vsaFoot H a → VsaIris.VsaHeap.vsaFoot H0 a ∨ ListsFoot Shape foot m1 a
  roots : GlobalRoots Shape foot x.σ.mem rs ys os
  feet : ∀ sk cells, IsList sk → Shape x.σ.mem sk cells →
    ∀ a, foot x.σ.mem sk cells a → ListsFoot Shape foot m1 a ∨ VsaIris.VsaHeap.vsaFoot H0 a
  kept : ∀ a, ¬ ListsFoot Shape foot m1 a → ¬ VsaIris.VsaHeap.vsaFoot H0 a →
    (a < (sp.toNat - 32) - opStack ∨ sp.toNat - 32 ≤ a) → (a < randomSeed ∨ randomSeed + 4 ≤ a) →
    (x.σ.mem[a]?).getD 0 = (m1[a]?).getD 0

/-- **At a skiplist call** from the modification: the callee's entry `pc`, the
link, `sp`, `a0 = hdr`, `a1 = r` and the memory, callee-saved registers, `gp`
and output of the `Acting` state `x` it came from. -/
structure OpEntry (pc link sp r : BitVec 64) (hdr : Nat) (x z : Config) : Prop where
  pc : PCAt pc z
  leaf : LeafInput link z
  stack : gprGet z.σ 2 = some sp
  list : gprGet z.σ 10 = some (BitVec.ofNat 64 hdr)
  key : gprGet z.σ 11 = some r
  memory : z.σ.mem = x.σ.mem
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet z.σ n = gprGet x.σ n
  gp : gpr z 3 = gpr x 3
  output : z.σ.sailOutput = x.σ.sailOutput

/-- **A skiplist call's return keeps `Acting`'s frame facts**: from the
callee's `Returned` on the touched list `hdr`, every field but the roots and
the lists' footprints. -/
theorem Acting.returned {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)}
    {sp v r : BitVec 64} {rs ys os : List (BitVec 64)} {c x z d : Config} {pc link : BitVec 64} {hdr : Nat}
    {cells : List (BitVec 64)} {H : List (Nat × Nat)}
    (act : Acting Shape foot H0 m1 sp v r rs c x ys os) (entry : OpEntry pc link (sp + 18446744073709551584#64) r hdr x z)
    (list : hdr = globalRootsYoung ∨ hdr = globalRootsOld) (sh : Shape z.σ.mem hdr cells)
    (bound : ∀ a, VsaIris.VsaHeap.vsaFoot H a → VsaIris.VsaHeap.vsaFoot H0 a ∨ ListsFoot Shape foot m1 a)
    (spNat : (sp + 18446744073709551584#64).toNat = sp.toNat - 32)
    (ret : Returned H (foot z.σ.mem hdr cells) (sp + 18446744073709551584#64) link z d) :
    GoodState d.σ ∧ ExecutableImage d ∧ (∃ w, d.σ.regs.get? Register.minstret = some w) ∧ d.tick < 2 ∧
    PCAt link d ∧ gprGet d.σ 1 = some link ∧ gprGet d.σ 2 = some (sp + 18446744073709551584#64) ∧
    gprGet d.σ 8 = some v ∧ gprGet d.σ 9 = some r ∧ (gprGet d.σ 10).isSome ∧
    (∀ n ∈ [18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet d.σ n = gprGet c.σ n) ∧ gpr d 3 = gpr c 3 ∧
    d.σ.sailOutput = c.σ.sailOutput ∧
    (∃ H' cap', HeapReady H' cap' d ∧ ∀ a, VsaIris.VsaHeap.vsaFoot H' a →
      VsaIris.VsaHeap.vsaFoot H0 a ∨ ListsFoot Shape foot m1 a) ∧
    ∀ a, ¬ ListsFoot Shape foot m1 a → ¬ VsaIris.VsaHeap.vsaFoot H0 a →
      (a < (sp.toNat - 32) - opStack ∨ sp.toNat - 32 ≤ a) → (a < randomSeed ∨ randomSeed + 4 ≤ a) →
      (d.σ.mem[a]?).getD 0 = (m1[a]?).getD 0 := by
  have shx : Shape x.σ.mem hdr cells := by rw [← entry.memory]; exact sh
  have touchedIn : ∀ a, foot z.σ.mem hdr cells a → ListsFoot Shape foot m1 a ∨ VsaIris.VsaHeap.vsaFoot H0 a :=
    fun a f => act.feet hdr cells (Or.inr list) shx a (by rw [← entry.memory]; exact f)
  have sv (n : Nat) (hn : n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) : gprGet d.σ n = gprGet x.σ n :=
    (ret.saved n hn).trans (entry.saved n hn)
  obtain ⟨H', cap', hr, hb⟩ := ret.heap
  refine ⟨ret.good, ret.image, ret.minstret, ret.tick, ret.pc, ?_, ret.stack, (sv 8 (by decide)).trans act.s0,
    (sv 9 (by decide)).trans act.s1, ?_, fun n hn => (sv n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)).trans
      (act.saved n hn), ret.gprs.gp.trans (entry.gp.trans act.gp), ret.output.trans (entry.output.trans act.output),
    ⟨H', cap', hr, fun a f => ?_⟩, fun a nl nf win seed => ?_⟩
  · exact ret.link
  · exact ret.gprs.present 10 (by decide) (by decide) (gpr_some_of entry.list)
  · rcases hb a f with old | touched
    · exact bound a old
    · rcases touchedIn a touched with l | v
      · exact Or.inr l
      · exact Or.inl v
  · rw [ret.kept a (fun t => by rcases touchedIn a t with l | v; exact nl l; exact nf v)
      (fun f => by rcases bound a f with v | l; exact nf v; exact nl l) (by rw [spNat]; exact win) seed,
      entry.memory]
    exact act.kept a nl nf win seed

/-- The list footprints at `z` bounded as at `x` when `z` has `x`'s memory. -/
theorem feet_of_memory {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)} {x z : Config}
    (feet : ∀ sk cells, IsList sk → Shape x.σ.mem sk cells →
      ∀ a, foot x.σ.mem sk cells a → ListsFoot Shape foot m1 a ∨ VsaIris.VsaHeap.vsaFoot H0 a)
    (mem : z.σ.mem = x.σ.mem) :
    ∀ sk cells, IsList sk → Shape z.σ.mem sk cells →
      ∀ a, foot z.σ.mem sk cells a → ListsFoot Shape foot m1 a ∨ VsaIris.VsaHeap.vsaFoot H0 a := by
  rw [mem]; exact feet

/-- **A call on the young list steps `Acting`**: any callee shaped like
`Ops.insert`/`Ops.remove`, whose new keys `Q` stay apart from the other lists. -/
theorem Acting.step_young (ops : Ops Shape foot) {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)}
    {sp v r : BitVec 64} {rs ys os : List (BitVec 64)} {c x z : Config} {pc link : BitVec 64}
    (act : Acting Shape foot H0 m1 sp v r rs c x ys os)
    (entry : OpEntry pc link (sp + 18446744073709551584#64) r globalRootsYoung x z) (aligned : link.toNat % 4 = 0)
    (spNat : (sp + 18446744073709551584#64).toNat = sp.toNat - 32)
    (frame' : NativeFrame (sp + 18446744073709551584#64) opStack) {Q : List (BitVec 64) → Prop}
    (apartKeys : ∀ ks, Q ks → ∀ k ∈ ks, k ∉ rs ∧ k ∉ os)
    (op : ∀ H cap cy, Shape z.σ.mem globalRootsYoung cy → keys z.σ.mem cy = ys → HeapReady H cap z →
      FnSummary pc (fun d => d = z) (fun d => Returned H (foot z.σ.mem globalRootsYoung cy)
        (sp + 18446744073709551584#64) link z d ∧ ∃ cy', Shape d.σ.mem globalRootsYoung cy' ∧ Q (keys d.σ.mem cy') ∧
        ∀ a, foot d.σ.mem globalRootsYoung cy' a → foot z.σ.mem globalRootsYoung cy a ∨ VsaIris.VsaHeap.vsaFoot H a)) :
    ∃ d ys', Steps z d ∧ PCAt link d ∧ Acting Shape foot H0 m1 sp v r rs c d ys' os ∧ Q ys' := by
  obtain ⟨H, cap, hr, hb⟩ := act.heap
  have hrz : HeapReady H cap z := RegisterRoot.HeapReady.of_mem hr entry.memory
  have gz : GlobalRoots Shape foot z.σ.mem rs ys os := by rw [entry.memory]; exact act.roots
  obtain ⟨cy, shz, hy⟩ := gz.young
  obtain ⟨d, run, ret, cy', sh', q, footIn⟩ := (op H cap cy shz hy hrz).run z ⟨entry.pc, rfl⟩
  obtain ⟨good, image, minstret, tick, pc', link1, stack, s0, s1, a0, saved, gp, output, heap, kept⟩ :=
    act.returned entry (Or.inl rfl) shz hb spNat ret
  have lowSp := frame'.lower
  have fr : InsertFrame Shape foot H globalRootsYoung cy z.σ.mem d.σ.mem :=
    { live := fun sk cells sh a f => (ops.live _ _ _ sh H cap z rfl hrz a f).1
      seed := fun sk cells sh a f => (ops.live _ _ _ sh H cap z rfl hrz a f).2
      kept := fun a nt nf lo seed => ret.kept a nt nf (Or.inl (by unfold opStack at lowSp ⊢; omega)) seed }
  have feetZ := feet_of_memory act.feet entry.memory
  refine ⟨d, keys d.σ.mem cy', run, pc',
    { good, image, minstret, tick, link := ⟨link, link1, aligned⟩, stack, s0, s1, a0, saved, gp, output, heap,
      roots := gz.replace_young ops shz sh' (apartKeys _ q) footIn fr, feet := ?_, kept }, q⟩
  intro sk cells list sh a f
  rcases list with rfl | rfl | rfl
  · obtain ⟨c1, sh1, -⟩ := gz.roots
    obtain ⟨sh1', ft⟩ := gz.roots_kept_young ops shz fr sh1
    have e := ops.unique sh sh1'
    subst e
    exact feetZ _ _ (Or.inl rfl) sh1 a ((ft a).1 f)
  · have e := ops.unique sh sh'
    subst e
    rcases footIn a f with old | free
    · exact feetZ _ _ (Or.inr (Or.inl rfl)) shz a old
    · rcases hb a free with v' | l
      · exact Or.inr v'
      · exact Or.inl l
  · obtain ⟨co, sho, -⟩ := gz.old
    obtain ⟨sho', ft⟩ := gz.old_kept ops shz fr sho
    have e := ops.unique sh sho'
    subst e
    exact feetZ _ _ (Or.inr (Or.inr rfl)) sho a ((ft a).1 f)

/-- **A call on the old list steps `Acting`.** -/
theorem Acting.step_old (ops : Ops Shape foot) {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)}
    {sp v r : BitVec 64} {rs ys os : List (BitVec 64)} {c x z : Config} {pc link : BitVec 64}
    (act : Acting Shape foot H0 m1 sp v r rs c x ys os)
    (entry : OpEntry pc link (sp + 18446744073709551584#64) r globalRootsOld x z) (aligned : link.toNat % 4 = 0)
    (spNat : (sp + 18446744073709551584#64).toNat = sp.toNat - 32)
    (frame' : NativeFrame (sp + 18446744073709551584#64) opStack) {Q : List (BitVec 64) → Prop}
    (apartKeys : ∀ ks, Q ks → ∀ k ∈ ks, k ∉ rs ∧ k ∉ ys)
    (op : ∀ H cap co, Shape z.σ.mem globalRootsOld co → keys z.σ.mem co = os → HeapReady H cap z →
      FnSummary pc (fun d => d = z) (fun d => Returned H (foot z.σ.mem globalRootsOld co)
        (sp + 18446744073709551584#64) link z d ∧ ∃ co', Shape d.σ.mem globalRootsOld co' ∧ Q (keys d.σ.mem co') ∧
        ∀ a, foot d.σ.mem globalRootsOld co' a → foot z.σ.mem globalRootsOld co a ∨ VsaIris.VsaHeap.vsaFoot H a)) :
    ∃ d os', Steps z d ∧ PCAt link d ∧ Acting Shape foot H0 m1 sp v r rs c d ys os' ∧ Q os' := by
  obtain ⟨H, cap, hr, hb⟩ := act.heap
  have hrz : HeapReady H cap z := RegisterRoot.HeapReady.of_mem hr entry.memory
  have gz : GlobalRoots Shape foot z.σ.mem rs ys os := by rw [entry.memory]; exact act.roots
  obtain ⟨co, shz, ho⟩ := gz.old
  obtain ⟨d, run, ret, co', sh', q, footIn⟩ := (op H cap co shz ho hrz).run z ⟨entry.pc, rfl⟩
  obtain ⟨good, image, minstret, tick, pc', link1, stack, s0, s1, a0, saved, gp, output, heap, kept⟩ :=
    act.returned entry (Or.inr rfl) shz hb spNat ret
  have lowSp := frame'.lower
  have fr : InsertFrame Shape foot H globalRootsOld co z.σ.mem d.σ.mem :=
    { live := fun sk cells sh a f => (ops.live _ _ _ sh H cap z rfl hrz a f).1
      seed := fun sk cells sh a f => (ops.live _ _ _ sh H cap z rfl hrz a f).2
      kept := fun a nt nf lo seed => ret.kept a nt nf (Or.inl (by unfold opStack at lowSp ⊢; omega)) seed }
  have feetZ := feet_of_memory act.feet entry.memory
  refine ⟨d, keys d.σ.mem co', run, pc',
    { good, image, minstret, tick, link := ⟨link, link1, aligned⟩, stack, s0, s1, a0, saved, gp, output, heap,
      roots := gz.replace_old ops shz sh' (apartKeys _ q) footIn fr, feet := ?_, kept }, q⟩
  intro sk cells list sh a f
  rcases list with rfl | rfl | rfl
  · obtain ⟨c1, sh1, -⟩ := gz.roots
    obtain ⟨sh1', ft⟩ := gz.roots_kept_old ops shz fr sh1
    have e := ops.unique sh sh1'
    subst e
    exact feetZ _ _ (Or.inl rfl) sh1 a ((ft a).1 f)
  · obtain ⟨cy, shy, -⟩ := gz.young
    obtain ⟨shy', ft⟩ := gz.young_kept ops shz fr shy
    have e := ops.unique sh shy'
    subst e
    exact feetZ _ _ (Or.inr (Or.inl rfl)) shy a ((ft a).1 f)
  · have e := ops.unique sh sh'
    subst e
    rcases footIn a f with old | free
    · exact feetZ _ _ (Or.inr (Or.inr rfl)) shz a old
    · rcases hb a free with v' | l
      · exact Or.inr v'
      · exact Or.inl l

/-! ### The call, its input and its post -/

/-- The prologue's three saves into the 32-byte frame. -/
def proLog (sp s0 s1 ra : BitVec 64) : List WEntry :=
  [((sp - 32#64 + 16#64).toNat, 8, s0), ((sp - 32#64 + 8#64).toNat, 8, s1), ((sp - 32#64 + 24#64).toNat, 8, ra)]

/-- **A call of `caml_modify_generational_global_root(r, v)`**: a root slot `r`
in the arena (not one of `caml_global_roots`), placed by `RootAt` for its
current value, newlib's heap, a frame for the prologue and the callees, the
global roots, the page table and the young bounds. -/
structure ModifyInput (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop)
    (H : List (Nat × Nat)) (cap : Nat) (rs ys os : List (BitVec 64)) (cls : Nat → Nat)
    (D start stop sp ra r v : BitVec 64) (c : Config) : Prop where
  leaf : LeafInput ra c
  slotReg : gprGet c.σ 10 = some r
  valueReg : gprGet c.σ 11 = some v
  stack : gprGet c.σ 2 = some sp
  slot : WriteWindow r 8
  slotLow : Vsa.Sim.DlHeap.heapStart ≤ r.toNat
  slotHigh : r.toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd
  heap : HeapReady H cap c
  frame : NativeFrame sp (32 + opStack)
  roots : GlobalRoots Shape foot c.σ.mem rs ys os
  root : RootAt start stop cls (rootValue c r) r ys os
  notGlobal : r ∉ rs
  table : Table c.σ.mem cls
  young : YoungAt c.σ.mem D start stop
  /-- `Caml_state`'s young bounds lie in the arena, below the native stack -/
  startBelow : (D + 32#64).toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd
  stopBelow : (D + 40#64).toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd
  /-- the slot is apart from the lists and newlib's own bytes -/
  slotApart : ∀ a, r.toNat ≤ a → a < r.toNat + 8 →
    ¬ ListsFoot Shape foot c.σ.mem a ∧ ¬ VsaIris.VsaHeap.vsaFoot H a
  /-- the caller's `s0` and `s1`, which the frame saves and restores -/
  s0 : (gprGet c.σ 8).isSome
  s1 : (gprGet c.σ 9).isSome

/-- **The root modified**: back at `ra` with `sp` and the callee-saved
registers; `*r = v`; `r` placed by `RootAt` for `v`, every other root where it
was; newlib's footprint within the old and the lists'; every byte outside the
lists, newlib's footprint, the slot, the stack window and `random_seed` kept. -/
structure RootModified (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (H : List (Nat × Nat)) (rs ys os : List (BitVec 64)) (cls : Nat → Nat)
    (start stop sp ra r v : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ w, d.σ.regs.get? Register.minstret = some w
  tick : d.tick < 2
  pc : PCAt ra d
  stack : gprGet d.σ 2 = some sp
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet d.σ n = gprGet c.σ n
  gprs : GprsKept c d
  output : d.σ.sailOutput = c.σ.sailOutput
  heap : ∃ H' cap', HeapReady H' cap' d ∧
    ∀ a, VsaIris.VsaHeap.vsaFoot H' a → VsaIris.VsaHeap.vsaFoot H a ∨ ListsFoot Shape foot c.σ.mem a
  roots : ∃ ys' os', GlobalRoots Shape foot d.σ.mem rs ys' os' ∧
    (∀ k, k ≠ r → (k ∈ ys' ↔ k ∈ ys) ∧ (k ∈ os' ↔ k ∈ os)) ∧ RootAt start stop cls v r ys' os'
  slot : bytesT d.σ.mem r.toNat 8 = v
  kept : ∀ a, ¬ ListsFoot Shape foot c.σ.mem a → ¬ VsaIris.VsaHeap.vsaFoot H a → (a < r.toNat ∨ r.toNat + 8 ≤ a) →
    (a < sp.toNat - (32 + opStack) ∨ sp.toNat ≤ a) → (a < randomSeed ∨ randomSeed + 4 ≤ a) →
    (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0

/-- The lists' footprints are the same after stores above the arena. -/
theorem listsFoot_low (ops : Ops Shape foot) {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os)
    (agree : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → (m'[a]?).getD 0 = (m[a]?).getD 0) (a : Nat) :
    ListsFoot Shape foot m' a ↔ ListsFoot Shape foot m a := by
  obtain ⟨-, keep⟩ := g.keep_low ops agree
  constructor
  · rintro ⟨sk, cells, list, sh', f⟩
    have cellsM : ∃ cs, Shape m sk cs := by
      rcases list with rfl | rfl | rfl
      · obtain ⟨cs, sh, -⟩ := g.roots; exact ⟨cs, sh⟩
      · obtain ⟨cs, sh, -⟩ := g.young; exact ⟨cs, sh⟩
      · obtain ⟨cs, sh, -⟩ := g.old; exact ⟨cs, sh⟩
    obtain ⟨cs, sh⟩ := cellsM
    obtain ⟨shm', ft, -⟩ := keep _ _ sh
    have e := ops.unique sh' shm'
    subst e
    exact ⟨sk, cells, list, sh, (ft a).1 f⟩
  · rintro ⟨sk, cells, list, sh, f⟩
    obtain ⟨sh', ft, -⟩ := keep _ _ sh
    exact ⟨sk, cells, list, sh', (ft a).2 f⟩

/-! ### The prologue -/

/-- `Acting` right after the prologue: its memory is `m1`. -/
structure Started (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (H : List (Nat × Nat)) (m1 : Std.ExtHashMap Nat (BitVec 8)) (sp v r : BitVec 64) (rs ys os : List (BitVec 64))
    (c x : Config) : Prop where
  acting : Acting Shape foot H m1 sp v r rs c x ys os
  memory : x.σ.mem = m1
  slotReg : gprGet x.σ 10 = some r
  valueReg : gprGet x.σ 11 = some v

/-- **The prologue**: the frame's three saves, `s0 = v`, `s1 = r`; `Acting`
holds after it with `m1` its memory, at `pc` (`0x8000cbe0` for an immediate
`v`, `0x8000cb28` for a block). -/
theorem prologue {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop} (ops : Ops Shape foot)
    {H : List (Nat × Nat)} {cap : Nat} {rs ys os : List (BitVec 64)} {cls : Nat → Nat}
    {D start stop sp ra r v : BitVec 64} {c : Config} {pc : BitVec 64}
    (h : ModifyInput Shape foot Table H cap rs ys os cls D start stop sp ra r v c)
    (blk : FnSummary 0x8000cb08#64 (fun d => d = c)
      (WriteRegistersPost [2, 8, 9, 15] (proLog sp (regsAt c 8) (regsAt c 9) ra) c pc r
        [(9, r), (8, v), (15, v &&& 1#64), (2, sp + 18446744073709551584#64), (1, ra), (10, r), (11, v)]))
    (entry : PCAt 0x8000cb08#64 c) :
    ∃ x, Steps c x ∧ PCAt pc x ∧
      Started Shape foot H (writeLog c.σ.mem (proLog sp (regsAt c 8) (regsAt c 9) ra)) sp v r rs ys os c x := by
  have frame := h.frame
  have lower : Vsa.Sim.DlHeap.heapEnd + (32 + 768) ≤ sp.toNat := frame.lower
  have hE : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have op := frame.resize (small := opStack) (by unfold opStack; omega) (by decide)
  have slot (k : Nat) (hk : k ≤ 32) : (sp - 32#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 32 + k := by
    rw [(RegisterRoot.frame32 op hk).1, BitVec.toNat_ofNat]
    have := frame.upper; simp only [Layout.sym_stack_top] at this; omega
  have log0 : LogInW [⟨sp.toNat - 32, sp.toNat⟩] (proLog sp (regsAt c 8) (regsAt c 9) ra) := by
    have e8 := slot 8 (by decide)
    have e16 := slot 16 (by decide)
    have e24 := slot 24 (by decide)
    simp only [proLog, LogInW, InsideW, e8, e16, e24, and_true]; omega
  obtain ⟨x, run, p⟩ := blk.run c ⟨entry, rfl⟩
  have mem : x.σ.mem = writeLog c.σ.mem (proLog sp (regsAt c 8) (regsAt c 9) ra) := p.memory
  have low : ∀ a, a < Vsa.Sim.DlHeap.heapEnd →
      ((writeLog c.σ.mem (proLog sp (regsAt c 8) (regsAt c 9) ra))[a]?).getD 0 = (c.σ.mem[a]?).getD 0 :=
    fun a ha => by rw [frameOn_writeLog _ _ _ log0 a ⟨Or.inl (show a < sp.toNat - 32 by omega), trivial⟩]
  have r' (n : Nat) (w : BitVec 64)
      (hl : lookupG n [(9, r), (8, v), (15, v &&& 1#64), (2, sp + 18446744073709551584#64), (1, ra), (10, r),
        (11, v)] = some w) : gprGet x.σ n = some w := gholds_lookup _ p.regs hl
  have keep (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [2, 8, 9, 15]) : gprGet x.σ n = gprGet c.σ n :=
    p.gpr_frame (by decide) n lo hi out
  refine ⟨x, run, p.pc, { acting := ?_, memory := mem, slotReg := r' 10 _ rfl, valueReg := r' 11 _ rfl }⟩
  refine
    { good := p.good
      image := p.image
      minstret := p.minstret
      tick := p.tick
      link := ⟨ra, r' 1 _ rfl, h.leaf.aligned⟩
      stack := r' 2 _ rfl
      s0 := r' 8 _ rfl
      s1 := r' 9 _ rfl
      a0 := gpr_some_of (r' 10 _ rfl)
      saved := fun n hn => keep n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; omega)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; omega)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)
      gp := keep 3 (by decide) (by decide) (by decide)
      output := p.output
      heap := ⟨H, cap, OCaml.Vm.Gc.HeapReady.keep_windows h.heap (ws := [⟨sp.toNat - 32, sp.toNat⟩])
        (fun w hw => by
          simp only [List.mem_singleton] at hw
          subst hw
          exact Or.inr (Or.inl (Nat.le_sub_of_add_le
            (Nat.le_trans (Nat.add_le_add_left (by decide : 32 ≤ 32 + 768) _) lower))))
        (fun a out => by rw [mem, frameOn_writeLog _ _ _ log0 a ⟨out _ List.mem_cons_self, trivial⟩]),
        fun a f => Or.inl f⟩
      roots := by rw [mem]; exact (h.roots.keep_low ops low).1
      feet := fun sk cells list sh a f => Or.inl ⟨sk, cells, list, by rw [← mem]; exact sh, by rw [← mem]; exact f⟩
      kept := fun a _ _ _ _ => by rw [mem] }

/-! ### Steps that keep memory -/

/-- **A step writing only temporaries and the link keeps `Acting`** (blocks
with no stores, calls). -/
theorem Acting.block {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)} {sp v r : BitVec 64}
    {rs ys os : List (BitVec 64)} {c x y : Config} {writes : List Nat} {pc val : BitVec 64} {regs : GRegs}
    (act : Acting Shape foot H0 m1 sp v r rs c x ys os) (p : RegistersPost writes x.σ.mem x pc val regs y)
    (keys : KeysOK writes) (temps : ∀ n ∈ writes, n = 1 ∨ (10 ≤ n ∧ n ≤ 17)) (a0 : (gprGet y.σ 10).isSome)
    (link : ∃ l : BitVec 64, gprGet y.σ 1 = some l ∧ l.toNat % 4 = 0) :
    Acting Shape foot H0 m1 sp v r rs c y ys os := by
  have mem : y.σ.mem = x.σ.mem := p.memory
  have keep (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : 1 < n ∧ (n < 10 ∨ 17 < n)) : gprGet y.σ n = gprGet x.σ n :=
    p.gpr_frame keys n lo hi fun m => by have := temps n m; omega
  obtain ⟨H, cap, hr, hb⟩ := act.heap
  exact
    { good := p.good
      image := p.image
      minstret := p.minstret
      tick := p.tick
      link := link
      stack := (keep 2 (by decide) (by decide) (by decide)).trans act.stack
      s0 := (keep 8 (by decide) (by decide) (by decide)).trans act.s0
      s1 := (keep 9 (by decide) (by decide) (by decide)).trans act.s1
      a0 := a0
      saved := fun n hn => by
        have hr : 18 ≤ n ∧ n ≤ 27 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; omega
        exact (keep n (by omega) (by omega) (by omega)).trans (act.saved n hn)
      gp := (keep 3 (by decide) (by decide) (by decide)).trans act.gp
      output := p.output.trans act.output
      heap := ⟨H, cap, RegisterRoot.HeapReady.of_mem hr mem, hb⟩
      roots := by rw [mem]; exact act.roots
      feet := by rw [mem]; exact act.feet
      kept := fun a nl nf win seed => by rw [mem]; exact act.kept a nl nf win seed }

/-- A block that keeps the link. -/
theorem Acting.temps {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)} {sp v r : BitVec 64}
    {rs ys os : List (BitVec 64)} {c x y : Config} {writes : List Nat} {pc val : BitVec 64} {regs : GRegs}
    (act : Acting Shape foot H0 m1 sp v r rs c x ys os) (p : RegistersPost writes x.σ.mem x pc val regs y)
    (keys : KeysOK writes) (temps : ∀ n ∈ writes, 10 ≤ n ∧ n ≤ 17) (a0 : (gprGet y.σ 10).isSome) :
    Acting Shape foot H0 m1 sp v r rs c y ys os := by
  obtain ⟨l, hl, al⟩ := act.link
  exact act.block p keys (fun n m => Or.inr (temps n m)) a0
    ⟨l, (p.gpr_frame keys 1 (by decide) (by decide) fun m => by have := temps 1 m; omega).trans hl, al⟩

/-- **A page-table lookup keeps `Acting`**: its call block (`a0 = w`), the
call and `caml_page_table_lookup`, before any list changed (memory `m1`). -/
theorem Acting.lookup {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop} (pt : PageTableLookup Table)
    {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)} {sp v r : BitVec 64}
    {rs ys os : List (BitVec 64)} {cls : Nat → Nat} {c x : Config} {call : CallInstr}
    (shape : CallShape call) (decode : CallDecode call) (pins : ∀ y : Config, ExecutableImage y → CallPins call y)
    (target : call.target = pageTableLookupPc) (aligned : call.link.toNat % 4 = 0)
    (act : Acting Shape foot H0 m1 sp v r rs c x ys os) (mem : x.σ.mem = m1) (table : Table m1 cls)
    {w : BitVec 64} {regs : GRegs}
    {writes : List Nat} (keys : KeysOK writes) (temps : ∀ n ∈ writes, 10 ≤ n ∧ n ≤ 17)
    (blk : ∃ y, Steps x y ∧ WriteRegistersPost writes [] x call.pc w regs y) (wr : lookupG 10 regs = some w) :
    ∃ y, Steps x y ∧ PCAt call.link y ∧ Acting Shape foot H0 m1 sp v r rs c y ys os ∧ y.σ.mem = m1 ∧
      gprGet y.σ 10 = some (BitVec.ofNat 64 (cls (w.toNat / 4096))) := by
  obtain ⟨y1, run1, p1⟩ := blk
  have a1 : Acting Shape foot H0 m1 sp v r rs c y1 ys os :=
    act.temps p1 keys temps (gpr_some_of (gholds_lookup _ p1.regs wr))
  have y1_10 : gprGet y1.σ 10 = some w := gholds_lookup _ p1.regs wr
  let args : GRegs := [(10, w), (2, sp + 18446744073709551584#64)]
  obtain ⟨y2, run2, p2⟩ := (call_registers_summary shape decode y1 (pins y1 p1.image) p1.good p1.image p1.tick
    p1.minstret args ⟨y1_10, a1.stack, trivial⟩ (by change KeysOK [10, 2]; decide)
    (by simp [KeysAvoidRa, args, keysG]) rfl).run y1 ⟨p1.pc, rfl⟩
  have a2 : Acting Shape foot H0 m1 sp v r rs c y2 ys os :=
    a1.block p2 (by decide) (by decide) (gpr_some_of (gholds_lookup _ p2.regs rfl))
      ⟨call.link, gholds_lookup _ p2.regs rfl, aligned⟩
  have mem2 : y2.σ.mem = m1 := by rw [p2.memory, p1.memory, wl_nil, mem]
  obtain ⟨y3, run3, p3⟩ := (pt.call y2 call.link w cls (by rw [mem2]; exact table)
    ⟨p2.good, p2.image, p2.minstret, gholds_lookup _ p2.regs rfl, aligned, p2.tick⟩
    (gholds_lookup _ p2.regs rfl)).run y2 ⟨by have := p2.pc; rwa [target] at this, rfl⟩
  have keep3 (n : Nat) (hn : n ∈ [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) :
      gprGet y3.σ n = gprGet y2.σ n := p3.saved n hn
  have mem3 : y3.σ.mem = y2.σ.mem := p3.memory
  obtain ⟨H, cap, hr, hb⟩ := a2.heap
  refine ⟨y3, run1.trans (run2.trans run3), p3.pc,
    { good := p3.good
      image := p3.image
      minstret := p3.minstret
      tick := p3.tick
      link := ⟨call.link, (keep3 1 (by decide)).trans (gholds_lookup _ p2.regs rfl), aligned⟩
      stack := (keep3 2 (by decide)).trans a2.stack
      s0 := (keep3 8 (by decide)).trans a2.s0
      s1 := (keep3 9 (by decide)).trans a2.s1
      a0 := gpr_some_of p3.result
      saved := fun n hn => (keep3 n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)).trans
        (a2.saved n hn)
      gp := (keep3 3 (by decide)).trans a2.gp
      output := p3.output.trans a2.output
      heap := ⟨H, cap, RegisterRoot.HeapReady.of_mem hr mem3, hb⟩
      roots := by rw [mem3]; exact a2.roots
      feet := by rw [mem3]; exact a2.feet
      kept := fun a nl nf win seed => by rw [mem3]; exact a2.kept a nl nf win seed },
    by rw [mem3, mem2], p3.result⟩

/-- **Into a skiplist call**: its block (`a0 = hdr`, `a1 = r`) and the `jal`. -/
theorem Acting.enter {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)} {sp v r : BitVec 64}
    {rs ys os : List (BitVec 64)} {c x y : Config} {call : CallInstr} {opPc : BitVec 64} {hdr : Nat}
    (shape : CallShape call) (decode : CallDecode call) (pins : ∀ y : Config, ExecutableImage y → CallPins call y)
    (target : call.target = opPc) (linkAligned : call.link.toNat % 4 = 0)
    (act : Acting Shape foot H0 m1 sp v r rs c x ys os)
    {writes : List Nat} {val : BitVec 64} {regs : GRegs}
    (p : RegistersPost writes x.σ.mem x call.pc val regs y) (keys : KeysOK writes)
    (temps : ∀ n ∈ writes, 10 ≤ n ∧ n ≤ 17)
    (a0 : gprGet y.σ 10 = some (BitVec.ofNat 64 hdr)) (a1 : gprGet y.σ 11 = some r) :
    ∃ z, Steps y z ∧ OpEntry opPc call.link (sp + 18446744073709551584#64) r hdr x z ∧
      gprGet z.σ 12 = gprGet y.σ 12 := by
  have ay : Acting Shape foot H0 m1 sp v r rs c y ys os := act.temps p keys temps (gpr_some_of a0)
  let args : GRegs := [(10, BitVec.ofNat 64 hdr), (11, r), (2, sp + 18446744073709551584#64)]
  obtain ⟨z, run, q⟩ := (call_registers_summary shape decode y (pins y p.image) p.good p.image p.tick p.minstret args
    ⟨a0, a1, ay.stack, trivial⟩ (by change KeysOK [10, 11, 2]; decide) (by simp [KeysAvoidRa, args, keysG]) rfl).run
    y ⟨p.pc, rfl⟩
  have keep (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : 1 < n) : gprGet z.σ n = gprGet y.σ n :=
    q.gpr_frame (by decide) n lo hi (by simp only [List.mem_singleton]; omega)
  have keepX (n : Nat) (hn : n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) : gprGet z.σ n = gprGet x.σ n := by
    have hr : 8 ≤ n ∧ n ≤ 27 ∧ (n < 10 ∨ 17 < n) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; omega
    exact (keep n (by omega) (by omega) (by omega)).trans
      (p.gpr_frame keys n (by omega) (by omega) fun m => by have := temps n m; omega)
  have entry : OpEntry opPc call.link (sp + 18446744073709551584#64) r hdr x z :=
    { pc := by have := q.pc; rwa [target] at this
      leaf := ⟨q.good, q.image, q.minstret, gholds_lookup _ q.regs rfl, linkAligned, q.tick⟩
      stack := gholds_lookup _ q.regs rfl
      list := gholds_lookup _ q.regs rfl
      key := gholds_lookup _ q.regs rfl
      memory := q.memory.trans p.memory
      saved := keepX
      gp := (keep 3 (by decide) (by decide) (by decide)).trans
        (p.gpr_frame keys 3 (by decide) (by decide) fun m => by have := temps 3 m; omega)
      output := q.output.trans p.output }
  exact ⟨z, run, entry, keep 12 (by decide) (by decide) (by decide)⟩

end OCaml.Vm.Primitives.Named.ModifyRoot
