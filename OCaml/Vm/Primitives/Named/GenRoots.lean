import OCaml.Vm.Primitives.Named.ModifyRootPaths

/-!
# The generational roots as an invariant over memory

`caml_register_generational_global_root` and
`caml_modify_generational_global_root` change the three skiplists of
`caml_global_roots{,_young,_old}`, whose cells live in newlib's heap; what
they keep depends on memory. `RootsAt` is the invariant a caller carries:

* the lists (`GlobalRoots`), the page table (`Table`, footprint `tfoot`) and
  the young bounds (`YoungAt`) — the environment `EnvAt`;
* the registered slots, each placed by `RootAt` for its current value, in the
  arena, apart from each other, the lists and newlib's footprint.

`Carry` is what a call guarantees about memory (`heap`/`feet` bounds and the
kept bytes); `EnvAt.carry` moves the environment across it.
-/

namespace OCaml.Vm.Primitives.Named.GenRoots
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm OCaml.Vm.Primitives OCaml.Vm.Gc OCaml.Vm.Gc.Skiplist
open OCaml.Vm.Boot.Startup (NativeFrame HeapReady nativeFrameBase)
open RegisterRoot (Young Old rootValue YoungAt)
open ModifyRoot (RootAt)

variable {Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop}
  {foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop}
  {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop}
  {tfoot : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop}

/-- The generational roots' abstract state: the lists' keys, the page-table
classes, `Caml_state` with the young bounds, and the registered slots. -/
structure RootsState where
  rs : List (BitVec 64)
  ys : List (BitVec 64)
  os : List (BitVec 64)
  cls : Nat → Nat
  D : BitVec 64
  start : BitVec 64
  stop : BitVec 64
  slots : List (BitVec 64)

/-- **The page table's frame** (a6-gc): stores off its footprint `tfoot`
keep its classes and its footprint. `PageTableLookup.frame` asks agreement on
the whole arena, which a skiplist insertion breaks. -/
structure TableFrame (Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop)
    (tfoot : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop) : Prop where
  frame : ∀ m m' cls, Table m cls → (∀ a, tfoot m a → (m'[a]?).getD 0 = (m[a]?).getD 0) →
    Table m' cls ∧ ∀ a, tfoot m' a ↔ tfoot m a

/-- A byte the roots calls may leave alone: off the lists, newlib's footprint
and `random_seed`. -/
structure Off (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (H : List (Nat × Nat)) (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : Prop where
  lists : ¬ ListsFoot Shape foot m a
  heap : ¬ VsaIris.VsaHeap.vsaFoot H a
  seed : a < randomSeed ∨ randomSeed + 4 ≤ a

/-- A byte of an 8-byte word. -/
def InWord (w : Nat) (a : Nat) : Prop := w ≤ a ∧ a < w + 8

/-- A byte of a registered slot. -/
def InSlots (slots : List (BitVec 64)) (a : Nat) : Prop := ∃ r ∈ slots, InWord r.toNat a

/-- The three words `YoungAt` reads: `Caml_state`, `young_start`, `young_end`. -/
def StateWord (S : RootsState) (a : Nat) : Prop :=
  InWord 0x80064d08 a ∨ InWord (S.D + 32#64).toNat a ∨ InWord (S.D + 40#64).toNat a

/-- **The roots' environment at `m`**: the page table, the young bounds, and
their bytes off the lists, newlib's footprint and the slots. -/
structure EnvAt (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop) (tfoot : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop)
    (H : List (Nat × Nat)) (S : RootsState) (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  table : Table m S.cls
  young : YoungAt m S.D S.start S.stop
  startBelow : (S.D + 32#64).toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd
  stopBelow : (S.D + 40#64).toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd
  tableBelow : ∀ a, tfoot m a → a < Vsa.Sim.DlHeap.heapEnd
  tableOff : ∀ a, tfoot m a → Off Shape foot H m a ∧ ¬ InSlots S.slots a
  stateOff : ∀ a, StateWord S a → Off Shape foot H m a ∧ ¬ InSlots S.slots a

/-- **The generational roots at `m`**: the environment, the lists, and the
registered slots placed by `RootAt` for their values. -/
structure RootsAt (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop) (tfoot : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop)
    (H : List (Nat × Nat)) (S : RootsState) (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  env : EnvAt Shape foot Table tfoot H S m
  roots : GlobalRoots Shape foot m S.rs S.ys S.os
  placed : ∀ r ∈ S.slots, RootAt S.start S.stop S.cls (bytesVal .ld (read8 m r.toNat)) r S.ys S.os
  slotLow : ∀ r ∈ S.slots, Vsa.Sim.DlHeap.heapStart ≤ r.toNat
  slotHigh : ∀ r ∈ S.slots, r.toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd
  slotAligned : ∀ r ∈ S.slots, r.toNat % 8 = 0
  slotOff : ∀ r ∈ S.slots, ∀ a, InWord r.toNat a → Off Shape foot H m a
  slotsApart : ∀ r ∈ S.slots, ∀ r' ∈ S.slots, r ≠ r' → r.toNat + 8 ≤ r'.toNat ∨ r'.toNat + 8 ≤ r.toNat
  /-- the generational lists hold registered slots only -/
  listed : ∀ k, k ∈ S.ys ∨ k ∈ S.os → k ∈ S.slots
  notGlobal : ∀ r ∈ S.slots, r ∉ S.rs

/-- **What a roots call guarantees about memory**: newlib's footprint and the
lists' footprints within the old ones, and every byte below the arena's end,
off them and outside `own`, kept. -/
structure Carry (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (H H' : List (Nat × Nat)) (own : Nat → Prop) (m m' : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  heap : ∀ a, VsaIris.VsaHeap.vsaFoot H' a → VsaIris.VsaHeap.vsaFoot H a ∨ ListsFoot Shape foot m a
  feet : ∀ a, ListsFoot Shape foot m' a → ListsFoot Shape foot m a ∨ VsaIris.VsaHeap.vsaFoot H a
  kept : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → Off Shape foot H m a → ¬ own a →
    (m'[a]?).getD 0 = (m[a]?).getD 0

/-- Off-bytes stay off across a call. -/
theorem Off.carry {H H' : List (Nat × Nat)} {own : Nat → Prop} {m m' : Std.ExtHashMap Nat (BitVec 8)} {a : Nat}
    (cr : Carry Shape foot H H' own m m') (o : Off Shape foot H m a) : Off Shape foot H' m' a :=
  ⟨fun l => (cr.feet a l).elim o.lists o.heap, fun v => (cr.heap a v).elim o.heap o.lists, o.seed⟩

/-- A word below the arena's end, off and outside `own`, reads the same. -/
theorem read8_carry {H H' : List (Nat × Nat)} {own : Nat → Prop} {m m' : Std.ExtHashMap Nat (BitVec 8)}
    (cr : Carry Shape foot H H' own m m') {w : Nat} (below : w + 8 ≤ Vsa.Sim.DlHeap.heapEnd)
    (off : ∀ a, InWord w a → Off Shape foot H m a ∧ ¬ own a) : read8 m' w = read8 m w := by
  have k (i : Nat) (hi : i < 8) : (m'[w + i]?).getD 0 = (m[w + i]?).getD 0 :=
    cr.kept _ (by omega) (off _ ⟨by omega, by omega⟩).1 (off _ ⟨by omega, by omega⟩).2
  simp only [read8]
  rw [show w = w + 0 from rfl, k 0 (by decide), k 1 (by decide), k 2 (by decide), k 3 (by decide), k 4 (by decide),
    k 5 (by decide), k 6 (by decide), k 7 (by decide)]

/-- **The environment across a call** whose own bytes are slots, onto slots
`slots'` whose new bytes miss the page table and the state words. -/
theorem EnvAt.carry (tf : TableFrame Table tfoot) {H H' : List (Nat × Nat)} {S : RootsState}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {own : Nat → Prop} (e : EnvAt Shape foot Table tfoot H S m)
    (cr : Carry Shape foot H H' own m m') (ownSlots : ∀ a, own a → InSlots S.slots a) (slots' : List (BitVec 64))
    (fresh : ∀ a, InSlots slots' a → InSlots S.slots a ∨ (¬ tfoot m a ∧ ¬ StateWord S a)) :
    EnvAt Shape foot Table tfoot H' { S with slots := slots' } m' := by
  have tkeep : ∀ a, tfoot m a → (m'[a]?).getD 0 = (m[a]?).getD 0 := fun a t =>
    cr.kept a (e.tableBelow a t) (e.tableOff a t).1 fun o => (e.tableOff a t).2 (ownSlots a o)
  obtain ⟨table', tf'⟩ := tf.frame m m' S.cls e.table tkeep
  have wordKeep (w : Nat) (below : w + 8 ≤ Vsa.Sim.DlHeap.heapEnd) (sw : ∀ a, InWord w a → StateWord S a) :
      read8 m' w = read8 m w :=
    read8_carry cr below fun a iw => ⟨(e.stateOff a (sw a iw)).1, fun o => (e.stateOff a (sw a iw)).2 (ownSlots a o)⟩
  have y := e.young
  refine
    { table := table'
      young :=
        { state := by
            rw [wordKeep (0x80064d08#64).toNat (by decide) fun a iw => Or.inl iw]; exact y.state
          startWord := by
            rw [wordKeep _ e.startBelow fun a iw => Or.inr (Or.inl iw)]; exact y.startWord
          stopWord := by
            rw [wordKeep _ e.stopBelow fun a iw => Or.inr (Or.inr iw)]; exact y.stopWord
          startWin := y.startWin
          stopWin := y.stopWin }
      startBelow := e.startBelow
      stopBelow := e.stopBelow
      tableBelow := fun a t => e.tableBelow a ((tf' a).1 t)
      tableOff := fun a t => ?_
      stateOff := fun a sw => ?_ }
  · have t0 := (tf' a).1 t
    refine ⟨(e.tableOff a t0).1.carry cr, fun i => ?_⟩
    rcases fresh a i with old | ⟨nt, -⟩
    · exact (e.tableOff a t0).2 old
    · exact nt t0
  · refine ⟨(e.stateOff a sw).1.carry cr, fun i => ?_⟩
    rcases fresh a i with old | ⟨-, ns⟩
    · exact (e.stateOff a sw).2 old
    · exact ns sw

/-! ### Registering a slot -/

/-- `RootAt` depends on the lists only through `r`'s membership. -/
theorem RootAt.of_iff {start stop : BitVec 64} {cls : Nat → Nat} {w r : BitVec 64} {ys os ys' os' : List (BitVec 64)}
    (p : RootAt start stop cls w r ys os) (hy : r ∈ ys' ↔ r ∈ ys) (ho : r ∈ os' ↔ r ∈ os) :
    RootAt start stop cls w r ys' os' :=
  ⟨fun yv => ⟨hy.2 (p.young yv).1, fun h => (p.young yv).2 (ho.1 h)⟩,
    fun ov => (p.old ov).imp hy.2 ho.2,
    fun ny no => ⟨fun h => (p.none ny no).1 (hy.1 h), fun h => (p.none ny no).2 (ho.1 h)⟩⟩

/-- **A slot fit to register** at `m`: new, in the arena, off the lists and
newlib's footprint, apart from the other slots, the page table and the state
words. -/
structure Fresh (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (tfoot : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop) (H : List (Nat × Nat)) (S : RootsState)
    (m : Std.ExtHashMap Nat (BitVec 8)) (r : BitVec 64) : Prop where
  notSlot : r ∉ S.slots
  notGlobal : r ∉ S.rs
  low : Vsa.Sim.DlHeap.heapStart ≤ r.toNat
  high : r.toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd
  aligned : r.toNat % 8 = 0
  off : ∀ a, InWord r.toNat a → Off Shape foot H m a
  apart : ∀ r' ∈ S.slots, r.toNat + 8 ≤ r'.toNat ∨ r'.toNat + 8 ≤ r.toNat
  notTable : ∀ a, InWord r.toNat a → ¬ tfoot m a
  notState : ∀ a, InWord r.toNat a → ¬ StateWord S a

/-- The slots' values across a call that keeps their bytes. -/
theorem RootsAt.value {H H' : List (Nat × Nat)} {S : RootsState} {own : Nat → Prop}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} (I : RootsAt Shape foot Table tfoot H S m)
    (cr : Carry Shape foot H H' own m m') {r : BitVec 64} (hr : r ∈ S.slots) (notOwn : ∀ a, InWord r.toNat a → ¬ own a) :
    read8 m' r.toNat = read8 m r.toNat :=
  read8_carry cr (I.slotHigh r hr) fun a iw => ⟨I.slotOff r hr a iw, notOwn a iw⟩

/-- **The roots after `caml_register_generational_global_root(r)`**: `r`
joins the slots, placed for its value. -/
theorem RootsAt.register (tf : TableFrame Table tfoot) {H H' : List (Nat × Nat)} {S : RootsState}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {r : BitVec 64} {ys' os' : List (BitVec 64)}
    (I : RootsAt Shape foot Table tfoot H S m) (fresh : Fresh Shape foot tfoot H S m r)
    (cr : Carry Shape foot H H' (fun _ => False) m m') (g : GlobalRoots Shape foot m' S.rs ys' os')
    (hy : ∀ k, k ∈ ys' ↔ (Young S.start S.stop (bytesVal .ld (read8 m r.toNat)) ∧ k = r) ∨ k ∈ S.ys)
    (ho : ∀ k, k ∈ os' ↔ (Old S.start S.stop S.cls (bytesVal .ld (read8 m r.toNat)) ∧ k = r) ∨ k ∈ S.os) :
    RootsAt Shape foot Table tfoot H' { S with ys := ys', os := os', slots := r :: S.slots } m' := by
  have notY : r ∉ S.ys := fun h => fresh.notSlot (I.listed r (Or.inl h))
  have notO : r ∉ S.os := fun h => fresh.notSlot (I.listed r (Or.inr h))
  have other (k : BitVec 64) (ne : k ≠ r) : (k ∈ ys' ↔ k ∈ S.ys) ∧ (k ∈ os' ↔ k ∈ S.os) :=
    ⟨(hy k).trans ⟨fun h => h.resolve_left fun p => ne p.2, Or.inr⟩,
      (ho k).trans ⟨fun h => h.resolve_left fun p => ne p.2, Or.inr⟩⟩
  have env := I.env.carry tf cr (fun _ f => f.elim) (r :: S.slots) fun a ⟨r', hr', iw⟩ => by
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact Or.inr ⟨fresh.notTable a iw, fresh.notState a iw⟩
    · exact Or.inl ⟨r', hr', iw⟩
  refine
    { env := { env with }
      roots := g
      placed := fun r' hr' => ?_
      slotLow := fun r' hr' => ?_
      slotHigh := fun r' hr' => ?_
      slotAligned := fun r' hr' => ?_
      slotOff := fun r' hr' a iw => ?_
      slotsApart := fun r1 h1 r2 h2 ne => ?_
      listed := fun k hk => ?_
      notGlobal := fun r' hr' => ?_ }
  · rcases List.mem_cons.1 hr' with rfl | hr'
    · rw [read8_carry cr fresh.high fun a iw => ⟨fresh.off a iw, id⟩]
      refine ⟨fun yv => ⟨(hy r').2 (Or.inl ⟨yv, rfl⟩), fun h => ?_⟩, fun ov => Or.inr ((ho r').2 (Or.inl ⟨ov, rfl⟩)),
        fun ny no => ⟨fun h => ?_, fun h => ?_⟩⟩
      · rcases (ho r').1 h with ⟨ov, -⟩ | h
        · exact ov.2.1 ⟨yv.2.1, yv.2.2⟩
        · exact notO h
      · rcases (hy r').1 h with ⟨yv, -⟩ | h
        · exact ny yv
        · exact notY h
      · rcases (ho r').1 h with ⟨ov, -⟩ | h
        · exact no ov
        · exact notO h
    · have ne : r' ≠ r := fun e => fresh.notSlot (e ▸ hr')
      rw [I.value cr hr' fun _ _ f => f]
      exact RootAt.of_iff (I.placed r' hr') (other r' ne).1 (other r' ne).2
  · rcases List.mem_cons.1 hr' with rfl | hr'
    · exact fresh.low
    · exact I.slotLow r' hr'
  · rcases List.mem_cons.1 hr' with rfl | hr'
    · exact fresh.high
    · exact I.slotHigh r' hr'
  · rcases List.mem_cons.1 hr' with rfl | hr'
    · exact fresh.aligned
    · exact I.slotAligned r' hr'
  · rcases List.mem_cons.1 hr' with rfl | hr'
    · exact (fresh.off a iw).carry cr
    · exact (I.slotOff r' hr' a iw).carry cr
  · rcases List.mem_cons.1 h1 with e1 | h1' <;> rcases List.mem_cons.1 h2 with e2 | h2'
    · exact (ne (e1.trans e2.symm)).elim
    · subst e1; exact fresh.apart r2 h2'
    · subst e2; exact (fresh.apart r1 h1').symm
    · exact I.slotsApart r1 h1' r2 h2' ne
  · rcases hk with h | h
    · rcases (hy k).1 h with ⟨-, rfl⟩ | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (I.listed k (Or.inl h))
    · rcases (ho k).1 h with ⟨-, rfl⟩ | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (I.listed k (Or.inr h))
  · rcases List.mem_cons.1 hr' with rfl | hr'
    · exact fresh.notGlobal
    · exact I.notGlobal r' hr'

/-! ### Modifying a slot -/

/-- **The roots after `caml_modify_generational_global_root(r, v)`** on a
registered slot `r`: `r` placed for `v`, every other slot where it was. -/
theorem RootsAt.modify (tf : TableFrame Table tfoot) {H H' : List (Nat × Nat)} {S : RootsState}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {r v : BitVec 64} {ys' os' : List (BitVec 64)}
    (I : RootsAt Shape foot Table tfoot H S m) (hr : r ∈ S.slots)
    (cr : Carry Shape foot H H' (InWord r.toNat) m m') (g : GlobalRoots Shape foot m' S.rs ys' os')
    (memb : ∀ k, k ≠ r → (k ∈ ys' ↔ k ∈ S.ys) ∧ (k ∈ os' ↔ k ∈ S.os))
    (place : RootAt S.start S.stop S.cls v r ys' os') (slot : bytesT m' r.toNat 8 = v) :
    RootsAt Shape foot Table tfoot H' { S with ys := ys', os := os' } m' := by
  have env := I.env.carry tf cr (fun a iw => ⟨r, hr, iw⟩) S.slots fun a i => Or.inl i
  refine
    { env := { env with }
      roots := g
      placed := fun r' hr' => ?_
      slotLow := I.slotLow
      slotHigh := I.slotHigh
      slotAligned := I.slotAligned
      slotOff := fun r' hr' a iw => (I.slotOff r' hr' a iw).carry cr
      slotsApart := I.slotsApart
      listed := fun k hk => ?_
      notGlobal := I.notGlobal }
  · by_cases e : r' = r
    · subst e
      rw [read8_value, slot]
      exact place
    · rw [I.value cr hr' fun a iw iw' => by
        rcases I.slotsApart r' hr' r hr e with h | h
        · exact absurd iw'.1 (by have := iw.2; omega)
        · exact absurd iw.1 (by have := iw'.2; omega)]
      exact RootAt.of_iff (I.placed r' hr') (memb r' e).1 (memb r' e).2
  · by_cases e : k = r
    · exact e ▸ hr
    · rcases hk with h | h
      · exact I.listed k (Or.inl ((memb k e).1.1 h))
      · exact I.listed k (Or.inr ((memb k e).2.1 h))

/-! ### The contract -/

/-- An aligned word in the arena is a store window. -/
theorem arena_window {r : BitVec 64} (low : Vsa.Sim.DlHeap.heapStart ≤ r.toNat)
    (high : r.toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd) (aligned : r.toNat % 8 = 0) : WriteWindow r 8 := by
  have hS : Vsa.Sim.DlHeap.heapStart = 0x8007d140 := rfl
  have hE : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have hT : Layout.sym_tohost + 16 ≤ 0x8007d140 := by decide
  exact ⟨by omega, by omega, by omega, aligned⟩

/-- **A roots call's ABI return**: at `ra` with `sp`, the callee-saved
registers, every register that held a value, and the output. -/
structure RootsReturn (sp ra : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ w, d.σ.regs.get? Register.minstret = some w
  tick : d.tick < 2
  pc : PCAt ra d
  stack : gprGet d.σ 2 = some sp
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet d.σ n = gprGet c.σ n
  gprs : GprsKept c d
  output : d.σ.sailOutput = c.σ.sailOutput

/-- **After a roots call**: newlib ready on `H'`, the roots at `S'`, and every
byte off the lists, newlib's footprint and `random_seed`, outside `own` and the
stack window below `sp`, kept. -/
structure RootsNext (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop) (tfoot : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop)
    (H H' : List (Nat × Nat)) (cap' : Nat) (S' : RootsState) (sp : BitVec 64) (depth : Nat) (own : Nat → Prop)
    (c d : Config) : Prop where
  heap : HeapReady H' cap' d
  roots : RootsAt Shape foot Table tfoot H' S' d.σ.mem
  kept : ∀ a, Off Shape foot H c.σ.mem a → ¬ own a → (a < sp.toNat - depth ∨ sp.toNat ≤ a) →
    (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0

/-- The call of `caml_register_generational_global_root(r)`. -/
structure RegisterEntry (H : List (Nat × Nat)) (cap : Nat) (sp ra r : BitVec 64) (c : Config) : Prop where
  leaf : LeafInput ra c
  slot : gprGet c.σ 10 = some r
  stack : gprGet c.σ 2 = some sp
  heap : HeapReady H cap c
  frame : NativeFrame sp opStack

/-- The call of `caml_modify_generational_global_root(r, v)`. -/
structure ModifyEntry (H : List (Nat × Nat)) (cap : Nat) (sp ra r v : BitVec 64) (c : Config) : Prop where
  leaf : LeafInput ra c
  slot : gprGet c.σ 10 = some r
  value : gprGet c.σ 11 = some v
  stack : gprGet c.σ 2 = some sp
  heap : HeapReady H cap c
  frame : NativeFrame sp (32 + opStack)
  s0 : (gprGet c.σ 8).isSome
  s1 : (gprGet c.σ 9).isSome

/-- **The generational global-root calls over the roots invariant**
(replaces `NamedRegister.RootCalls`): `register(r)` adds a fresh slot,
`modify(r, v)` stores `v` into a registered one; both keep `RootsAt`. -/
structure RootCallsG (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop)
    (tfoot : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop) : Prop where
  register : ∀ (c : Config) (H : List (Nat × Nat)) (cap : Nat) (S : RootsState) (sp ra r : BitVec 64),
    RootsAt Shape foot Table tfoot H S c.σ.mem → Fresh Shape foot tfoot H S c.σ.mem r →
    RegisterEntry H cap sp ra r c →
    FnSummary 0x8000ca04#64 (fun d => d = c) (fun d => RootsReturn sp ra c d ∧
      ∃ H' cap' ys' os', RootsNext Shape foot Table tfoot H H' cap'
        { S with ys := ys', os := os', slots := r :: S.slots } sp opStack (fun _ => False) c d)
  modify : ∀ (c : Config) (H : List (Nat × Nat)) (cap : Nat) (S : RootsState) (sp ra r v : BitVec 64),
    RootsAt Shape foot Table tfoot H S c.σ.mem → r ∈ S.slots → ModifyEntry H cap sp ra r v c →
    FnSummary 0x8000cb08#64 (fun d => d = c) (fun d => RootsReturn sp ra c d ∧ bytesT d.σ.mem r.toNat 8 = v ∧
      ∃ H' cap' ys' os', RootsNext Shape foot Table tfoot H H' cap' { S with ys := ys', os := os' } sp
        (32 + opStack) (InWord r.toNat) c d)

/-- **`RootCallsG` from the two machine runs** over a6-gc's skiplist, page
table lookup and page-table frame. -/
theorem rootCallsG (ops : Ops Shape foot) (pt : PageTableLookup Table) (tf : TableFrame Table tfoot) :
    RootCallsG Shape foot Table tfoot where
  register := fun c H cap S sp ra r I fresh e => by
    have frame := e.frame
    have lower : Vsa.Sim.DlHeap.heapEnd + 768 ≤ sp.toNat := frame.lower
    have input : RegisterRoot.RootInput Shape foot Table H cap S.rs S.ys S.os S.cls S.D S.start S.stop sp ra r c :=
      { leaf := e.leaf
        slot := e.slot
        stack := e.stack
        window := (arena_window fresh.low fresh.high fresh.aligned).read
        heap := e.heap
        frame := frame
        roots := I.roots
        fresh := by
          simp only [List.mem_append, not_or]
          exact ⟨⟨fresh.notGlobal, fun h => fresh.notSlot (I.listed r (Or.inl h))⟩,
            fun h => fresh.notSlot (I.listed r (Or.inr h))⟩
        table := I.env.table
        young := I.env.young }
    refine (RegisterRoot.register_root_run ops pt input).weaken (fun _ h => h) fun d f => ?_
    obtain ⟨H', cap', hr, hb⟩ := f.heap
    obtain ⟨ys', os', g, hy, ho⟩ := f.roots
    have below (a : Nat) (ha : a < Vsa.Sim.DlHeap.heapEnd) : a < sp.toNat - opStack := by
      unfold opStack; omega
    have cr : Carry Shape foot H H' (fun _ => False) c.σ.mem d.σ.mem :=
      { heap := hb
        feet := f.feet
        kept := fun a ha o _ => f.kept a o.lists o.heap (Or.inl (below a ha)) o.seed }
    exact ⟨⟨f.good, f.image, f.minstret, f.tick, f.pc, f.stack, f.saved, f.gprs, f.output⟩,
      H', cap', ys', os', ⟨hr, I.register tf fresh cr g hy ho, fun a o _ win => f.kept a o.lists o.heap win o.seed⟩⟩
  modify := fun c H cap S sp ra r v I hr e => by
    have frame := e.frame
    have lower : Vsa.Sim.DlHeap.heapEnd + (32 + 768) ≤ sp.toNat := frame.lower
    have input : ModifyRoot.ModifyInput Shape foot Table H cap S.rs S.ys S.os S.cls S.D S.start S.stop sp ra r v c :=
      { leaf := e.leaf
        slotReg := e.slot
        valueReg := e.value
        stack := e.stack
        slot := arena_window (I.slotLow r hr) (I.slotHigh r hr) (I.slotAligned r hr)
        slotLow := I.slotLow r hr
        slotHigh := I.slotHigh r hr
        heap := e.heap
        frame := frame
        roots := I.roots
        root := I.placed r hr
        notGlobal := I.notGlobal r hr
        table := I.env.table
        young := I.env.young
        startBelow := I.env.startBelow
        stopBelow := I.env.stopBelow
        slotApart := fun a lo hi => ⟨(I.slotOff r hr a ⟨lo, hi⟩).lists, (I.slotOff r hr a ⟨lo, hi⟩).heap⟩
        s0 := e.s0
        s1 := e.s1 }
    refine (ModifyRoot.modify_root_run ops pt input).weaken (fun _ h => h) fun d f => ?_
    obtain ⟨H', cap', hr', hb⟩ := f.heap
    obtain ⟨ys', os', g, memb, place⟩ := f.roots
    have below (a : Nat) (ha : a < Vsa.Sim.DlHeap.heapEnd) : a < sp.toNat - (32 + opStack) := by
      unfold opStack; omega
    have slotOut (a : Nat) (n : ¬ InWord r.toNat a) : a < r.toNat ∨ r.toNat + 8 ≤ a := by
      unfold InWord at n; omega
    have cr : Carry Shape foot H H' (InWord r.toNat) c.σ.mem d.σ.mem :=
      { heap := hb
        feet := f.feet
        kept := fun a ha o n => f.kept a o.lists o.heap (slotOut a n) (Or.inl (below a ha)) o.seed }
    exact ⟨⟨f.good, f.image, f.minstret, f.tick, f.pc, f.stack, f.saved, f.gprs, f.output⟩, f.slot,
      H', cap', ys', os',
      ⟨hr', I.modify tf hr cr g memb place f.slot, fun a o n win => f.kept a o.lists o.heap (slotOut a n) win o.seed⟩⟩

end OCaml.Vm.Primitives.Named.GenRoots
