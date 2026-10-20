import OCaml.Vm.Gc.SlotSupply
import OCaml.Vm.Gc.ChainScan
import OCaml.Vm.Gc.Skiplist
import OCaml.Vm.Gc.StackLoop

/-! # Root loops from the collection in progress

A chain walk's per-call obligations (`ChainScan.ChainLoop.WalkStep`) follow
from `SlotSupply` and static separation facts: the remaining cells form a
level-0 chain whose words, root slots and the callee's frame lie apart from
each other and from the calls' write region. -/
namespace OCaml.Vm.Gc.RootLoops
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable ChainScan

variable {Loaded : Std.ExtHashMap Nat (BitVec 8) → Prop} (L : ChainLoop Loaded)

theorem linked_eq (R : Nat → BitVec 64) (cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    (∀ n, n ≠ 1 → n ≠ 8 → n ≠ 10 → n ≠ 11 → L.site.linked (ChainLoop.calleeR R cell m) n = R n) ∧
    L.site.linked (ChainLoop.calleeR R cell m) 10 = bytesT m (key m cell).toNat 8 ∧
    L.site.linked (ChainLoop.calleeR R cell m) 11 = key m cell ∧
    L.site.linked (ChainLoop.calleeR R cell m) 1 = L.site.call.link := by
  refine ⟨fun n h1 h8 h10 h11 => ?_, ?_, ?_, ?_⟩ <;>
    simp_all [IndirectSlotSite.linked, ChainLoop.calleeR]

theorem frameSp_linked (R : Nat → BitVec 64) (cell : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    OldifyEntry.frameSp (L.site.linked (ChainLoop.calleeR R cell m)) = OldifyEntry.frameSp R := by
  simp [OldifyEntry.frameSp, IndirectSlotSite.linked, ChainLoop.calleeR]

/-- The caller's facts at a cell's call: the callee's frame below `R 2` and the
root slot `key cell`, writable and apart from that frame. -/
structure CallRoom (R : Nat → BitVec 64) (slot : BitVec 64) : Prop where
  windows : ∀ x ∈ OldifyEntry.saves, WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 x.2) 8
  slotWrite : WriteWindow slot 8
  slotApart : slot.toNat + 8 ≤ (OldifyEntry.frameSp R).toNat ∨ (R 2).toNat ≤ slot.toNat

theorem slotEntry {R : Nat → BitVec 64} {cell : BitVec 64} {c e : Config} (jumped : L.Jumped R cell c e)
    (room : CallRoom R (key c.σ.mem cell)) :
    SlotEntry (L.site.linked (ChainLoop.calleeR R cell c.σ.mem)) c.σ.mem e := by
  obtain ⟨other, v10, v11, v1⟩ := linked_eq L R cell c.σ.mem
  have sp2 : L.site.linked (ChainLoop.calleeR R cell c.σ.mem) 2 = R 2 := other 2 (by decide) (by decide) (by decide) (by decide)
  refine ⟨jumped.good, jumped.minstret, jumped.tick, jumped.memory, jumped.registers, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frameSp_linked]; exact room.windows
  · rw [v10, v11]
  · rw [v11]; exact room.slotWrite
  · rw [v11, frameSp_linked, sp2]; exact room.slotApart
  · rw [v1]; exact L.site.aligned

theorem byte_one (m : Std.ExtHashMap Nat (BitVec 8)) (x : Nat) : bytesT m x 1 = (m[x]?).getD 0 := by
  simp only [bytesT]
  change (0#0).append ((m[x]?).getD 0) = _
  rw [BitVec.append]
  simp

/-- A level-0 chain survives stores that keep its cells' link words. -/
theorem chain_congr {m m' : Std.ExtHashMap Nat (BitVec 8)} :
    ∀ (p : BitVec 64) (cells : List (BitVec 64)),
      (∀ x ∈ cells, ∀ k < 8, m'[(x + 16#64).toNat + k]? = m[(x + 16#64).toNat + k]?) →
      Skiplist.Chain m p cells → Skiplist.Chain m' p cells
  | _, [], _, h => h
  | p, x :: xs, same, ⟨hp, hx, rest⟩ => by
    have link : next m' x = next m x := by
      unfold next
      apply OCaml.Vm.Reloc.bytesT_congr (x := (x + 16#64).toNat) (x' := (x + 16#64).toNat)
      intro j hj
      rw [byte_one, byte_one, same x (List.mem_cons_self ..) j hj]
    refine ⟨hp, hx, ?_⟩
    rw [link]
    exact chain_congr _ xs (fun y hy => same y (List.mem_cons_of_mem _ hy)) rest

/-- The remaining chain's length from the walk register `s0`. -/
noncomputable def rank (c : Config) : Nat := by
  classical
  exact if h : ∃ cells, Skiplist.Chain c.σ.mem ((gprGet c.σ 8).getD 0) cells then (Classical.choose h).length else 0

theorem rank_eq {c : Config} {p : BitVec 64} {cells : List (BitVec 64)} (s0 : gprGet c.σ 8 = some p)
    (linked : Skiplist.Chain c.σ.mem p cells) : rank c = cells.length := by
  unfold rank
  have h : ∃ cells, Skiplist.Chain c.σ.mem ((gprGet c.σ 8).getD 0) cells := ⟨cells, by rw [s0]; exact linked⟩
  rw [dif_pos h]
  have spec := Classical.choose_spec h
  have first : (gprGet c.σ 8).getD 0 = p := by rw [s0]; rfl
  exact congrArg List.length (Skiplist.Chain.unique _ _ _ spec (first ▸ linked))

/-- The words a cell keeps for the walk (key, data, level-0 link). -/
def cellWord (x : BitVec 64) (a : Nat) : Prop := x.toNat ≤ a ∧ a < x.toNat + 24

/-- **The walk's invariant** at the head with `cells` left (`cell` first). -/
structure WalkInv (Ready : List PendingCopy → Std.ExtHashMap Nat (BitVec 8) → Prop)
    (Root : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop) (writes : Nat → Prop)
    (R : Nat → BitVec 64) (cells : List (BitVec 64)) (cell : BitVec 64) (copies : List PendingCopy) (c : Config) :
    Prop where
  head : L.HeadInput R cell c
  ready : Ready copies c.σ.mem
  linked : Skiplist.Chain c.σ.mem cell cells
  roots : ∀ x ∈ cells, Root c.σ.mem (key c.σ.mem x).toNat
  rooms : ∀ x ∈ cells, CallRoom R (key c.σ.mem x)
  reads : ∀ x ∈ cells, ReadWindow x 8 ∧ ReadWindow (x + 16#64) 8 ∧ ReadWindow (key c.σ.mem x) 8
  /-- the cells' words lie outside the calls' writes, the callee's frame and every root slot -/
  cellsApart : ∀ x ∈ cells, ∀ a, cellWord x a → ¬ writes a ∧
    (a < (OldifyEntry.frameSp R).toNat ∨ (R 2).toNat ≤ a) ∧
    ∀ y ∈ cells, a < (key c.σ.mem y).toNat ∨ (key c.σ.mem y).toNat + 8 ≤ a

/-- At the walk's exit. -/
structure WalkExit (Ready : List PendingCopy → Std.ExtHashMap Nat (BitVec 8) → Prop)
    (R : Nat → BitVec 64) (copies : List PendingCopy) (after : Config) : Prop where
  ready : Ready copies after.σ.mem
  pc : PCAt L.exitPc after
  registers : GHolds after.σ (ChainLoop.headRegs R 0#64)
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  code : Loaded after.σ.mem

/-- The end of the code (`.text`). -/
def textEnd : Nat := 0x80053180

theorem window_base {base : BitVec 64} {off : Nat} (small : off < 0x80000000) (w : WriteWindow (base + BitVec.ofNat 64 off) 8) :
    Layout.sym_tohost + 16 ≤ base.toNat + off ∧ base.toNat + off + 8 ≤ 0x100000000 := by
  have lower := w.lower
  have upper := w.upper
  have htif := w.htif
  have limit := base.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at lower upper htif
  constructor <;> omega

theorem frame_high {R : Nat → BitVec 64} {slot : BitVec 64} (room : CallRoom R slot) :
    textEnd ≤ (OldifyEntry.frameSp R).toNat := by
  obtain ⟨cell, member, small⟩ : ∃ cell ∈ OldifyEntry.saves, cell.2 ≤ 112 := ⟨_, List.head_mem (by decide), by decide⟩
  have w := room.windows cell member
  have h := window_base (by omega) w
  simp only [textEnd, Layout.sym_tohost] at h ⊢
  omega

theorem slot_high {R : Nat → BitVec 64} {slot : BitVec 64} (room : CallRoom R slot) : textEnd + 8 ≤ slot.toNat := by
  have h := window_base (off := 0) (by decide) (by simpa using room.slotWrite)
  simp only [textEnd, Layout.sym_tohost] at h ⊢
  omega

variable {Ready : List PendingCopy → Std.ExtHashMap Nat (BitVec 8) → Prop}
  {Root : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop} {pl : Place} {support writes : Nat → Prop}

theorem cons_of_head {R cells cell copies c} (inv : WalkInv L Ready Root writes R cells cell copies c) :
    ∃ rest, cells = cell :: rest := by
  cases cells with
  | nil =>
    have zero : cell = 0#64 := inv.linked
    have lower := inv.head.cellRead.lower
    rw [zero] at lower
    exact absurd lower (by decide)
  | cons x rest =>
    have : cell = x := inv.linked.1
    exact ⟨rest, by rw [this]⟩

/-- **One iteration keeps** the cells' words and the code. -/
theorem iteration_keeps (S : SlotSupply Ready Root pl support writes) {R cells cell copies c after}
    (inv : WalkInv L Ready Root writes R cells cell copies c) (post : L.Iterated R cell copies pl c after) :
    (∃ copies', Ready copies' after.σ.mem ∧ ∀ q, Root c.σ.mem q → Root after.σ.mem q) ∧
    ∀ a, ((∃ x ∈ cells, cellWord x a) ∨ a < textEnd) → after.σ.mem[a]? = c.σ.mem[a]? := by
  obtain ⟨rest, rfl⟩ := cons_of_head L inv
  obtain ⟨e, copies', mid, jumped, done, memory, -⟩ := post.slot
  have room := inv.rooms cell (List.mem_cons_self ..)
  have entry := slotEntry L jumped room
  have root : Root c.σ.mem ((L.site.linked (ChainLoop.calleeR R cell c.σ.mem)) 11).toNat := by
    rw [(linked_eq L R cell c.σ.mem).2.2.1]; exact inv.roots cell (List.mem_cons_self ..)
  obtain ⟨ready', roots'⟩ := S.preserve _ copies copies' c.σ.mem e mid inv.ready root entry done
  have sp2 : L.site.linked (ChainLoop.calleeR R cell c.σ.mem) 2 = R 2 :=
    (linked_eq L R cell c.σ.mem).1 2 (by decide) (by decide) (by decide) (by decide)
  have slot11 := (linked_eq L R cell c.σ.mem).2.2.1
  refine ⟨⟨copies', by rw [memory]; exact ready', fun q hq => by rw [memory]; exact roots' q hq⟩, ?_⟩
  intro a where_
  rw [memory]
  apply S.footprint _ copies copies' c.σ.mem e mid inv.ready root entry done a
  · rcases where_ with ⟨x, hx, word⟩ | low
    · exact (inv.cellsApart x hx a word).1
    · exact S.codeOutside a (by simp only [textEnd, tohostAddr, LibraryLayout.tohostAddr] at low ⊢; omega)
  · rw [frameSp_linked, sp2]
    rcases where_ with ⟨x, hx, word⟩ | low
    · exact (inv.cellsApart x hx a word).2.1
    · exact Or.inl (by have := frame_high room; omega)
  · rw [slot11]
    rcases where_ with ⟨x, hx, word⟩ | low
    · exact (inv.cellsApart x hx a word).2.2 cell (List.mem_cons_self ..)
    · exact Or.inl (by have := slot_high room; omega)

/-- **One call keeps** the cells' words and the code, and readiness. -/
theorem call_keeps (S : SlotSupply Ready Root pl support writes) {R cells cell copies copies' c e mid}
    (inv : WalkInv L Ready Root writes R cells cell copies c) (jumped : L.Jumped R cell c e)
    (done : SlotDone (L.site.linked (ChainLoop.calleeR R cell c.σ.mem)) copies copies' pl e mid) :
    (Ready copies' mid.σ.mem ∧ ∀ q, Root c.σ.mem q → Root mid.σ.mem q) ∧
    ∀ a, ((∃ x ∈ cells, cellWord x a) ∨ a < textEnd) → mid.σ.mem[a]? = c.σ.mem[a]? := by
  obtain ⟨rest, rfl⟩ := cons_of_head L inv
  have room := inv.rooms cell (List.mem_cons_self ..)
  have entry := slotEntry L jumped room
  have slot11 := (linked_eq L R cell c.σ.mem).2.2.1
  have root : Root c.σ.mem ((L.site.linked (ChainLoop.calleeR R cell c.σ.mem)) 11).toNat := by
    rw [slot11]; exact inv.roots cell (List.mem_cons_self ..)
  have sp2 : L.site.linked (ChainLoop.calleeR R cell c.σ.mem) 2 = R 2 :=
    (linked_eq L R cell c.σ.mem).1 2 (by decide) (by decide) (by decide) (by decide)
  refine ⟨S.preserve _ copies copies' c.σ.mem e mid inv.ready root entry done, ?_⟩
  intro a where_
  apply S.footprint _ copies copies' c.σ.mem e mid inv.ready root entry done a
  · rcases where_ with ⟨x, hx, word⟩ | low
    · exact (inv.cellsApart x hx a word).1
    · exact S.codeOutside a (by simp only [textEnd, tohostAddr, LibraryLayout.tohostAddr] at low ⊢; omega)
  · rw [frameSp_linked, sp2]
    rcases where_ with ⟨x, hx, word⟩ | low
    · exact (inv.cellsApart x hx a word).2.1
    · exact Or.inl (by have := frame_high room; omega)
  · rw [slot11]
    rcases where_ with ⟨x, hx, word⟩ | low
    · exact (inv.cellsApart x hx a word).2.2 cell (List.mem_cons_self ..)
    · exact Or.inl (by have := slot_high room; omega)

theorem word_kept {m m' : Std.ExtHashMap Nat (BitVec 8)} {x : BitVec 64} (off : Nat) (small : off + 8 ≤ 24)
    (same : ∀ a, cellWord x a → m'[a]? = m[a]?) : bytesT m' (x.toNat + off) 8 = bytesT m (x.toNat + off) 8 := by
  apply OCaml.Vm.Reloc.bytesT_congr
  intro j hj
  rw [byte_one, byte_one, same _ ⟨by omega, by omega⟩]

theorem key_kept {m m' : Std.ExtHashMap Nat (BitVec 8)} {x : BitVec 64} (same : ∀ a, cellWord x a → m'[a]? = m[a]?) :
    key m' x = key m x := by
  have h := word_kept 0 (by decide) same
  simpa only [key, Nat.add_zero] using h

theorem next_kept {m m' : Std.ExtHashMap Nat (BitVec 8)} {x : BitVec 64} (read : ReadWindow (x + 16#64) 8)
    (same : ∀ a, cellWord x a → m'[a]? = m[a]?) : next m' x = next m x := by
  have upper := read.upper
  have lower := read.lower
  have limit := x.isLt
  have addr : (x + 16#64).toNat = x.toNat + 16 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at upper lower ⊢; omega
  unfold next
  rw [addr]
  exact word_kept 16 (by decide) same

theorem link_word {x : BitVec 64} (read : ReadWindow (x + 16#64) 8) (k : Nat) (hk : k < 8) :
    cellWord x ((x + 16#64).toNat + k) := by
  have upper := read.upper
  have lower := read.lower
  have limit := x.isLt
  have addr : (x + 16#64).toNat = x.toNat + 16 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at upper lower ⊢; omega
  rw [addr]
  exact ⟨by omega, by omega⟩

/-- What one iteration leaves, for the walk's next state or its exit. -/
structure Stepped (Ready : List PendingCopy → Std.ExtHashMap Nat (BitVec 8) → Prop)
    (Root : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop) (cells : List (BitVec 64)) (c after : Config) : Prop where
  ready : ∃ copies', Ready copies' after.σ.mem
  roots : ∀ q, Root c.σ.mem q → Root after.σ.mem q
  same : ∀ a, ((∃ x ∈ cells, cellWord x a) ∨ a < textEnd) → after.σ.mem[a]? = c.σ.mem[a]?

theorem stepped (S : SlotSupply Ready Root pl support writes) {R cells cell copies c after}
    (inv : WalkInv L Ready Root writes R cells cell copies c) (post : L.Iterated R cell copies pl c after) :
    Stepped Ready Root cells c after ∧ PCAt (if next c.σ.mem cell != 0#64 then L.bodyPc else L.exitPc) after := by
  obtain ⟨e, copies', mid, jumped, done, memory, pcIf⟩ := post.slot
  obtain ⟨⟨ready', roots'⟩, keep⟩ := call_keeps L S inv jumped done
  refine ⟨⟨⟨copies', by rw [memory]; exact ready'⟩, fun q hq => by rw [memory]; exact roots' q hq,
    fun a h => by rw [memory]; exact keep a h⟩, pcIf⟩

theorem walk_next (S : SlotSupply Ready Root pl support writes)
    (transport : ∀ m m', Loaded m → (∀ a, a < textEnd → m'[a]? = m[a]?) → Loaded m')
    {R cells cell copies c after} (inv : WalkInv L Ready Root writes R cells cell copies c)
    (post : L.Iterated R cell copies pl c after) (pc : PCAt L.bodyPc after) :
    ∃ copies' cells', WalkInv L Ready Root writes R cells' (next c.σ.mem cell) copies' after := by
  obtain ⟨⟨⟨copies', ready'⟩, roots', same⟩, pcIf⟩ := stepped L S inv post
  obtain ⟨rest, rfl⟩ := cons_of_head L inv
  obtain ⟨-, -, chainRest⟩ := inv.linked
  have nonzero : (next c.σ.mem cell != 0#64) = true := by
    by_cases h : (next c.σ.mem cell != 0#64) = true
    · exact h
    · rw [if_neg h] at pcIf
      rw [PCAt] at pcIf pc
      rw [pcIf] at pc
      exact absurd (Option.some.inj pc) L.exit_ne_body
  cases rest with
  | nil =>
    have z : next c.σ.mem cell = 0#64 := chainRest
    rw [z] at nonzero
    exact absurd nonzero (by decide)
  | cons y ys =>
    have hy : y = next c.σ.mem cell := chainRest.1.symm
    subst hy
    have keepCell : ∀ x ∈ cell :: next c.σ.mem cell :: ys, ∀ a, cellWord x a → after.σ.mem[a]? = c.σ.mem[a]? :=
      fun x hx a w => same a (Or.inl ⟨x, hx, w⟩)
    have keyEq : ∀ x ∈ cell :: next c.σ.mem cell :: ys, key after.σ.mem x = key c.σ.mem x :=
      fun x hx => key_kept (keepCell x hx)
    have tail : ∀ x ∈ next c.σ.mem cell :: ys, x ∈ cell :: next c.σ.mem cell :: ys :=
      fun x hx => List.mem_cons_of_mem _ hx
    have here : next c.σ.mem cell ∈ cell :: next c.σ.mem cell :: ys := tail _ (List.mem_cons_self ..)
    refine ⟨copies', next c.σ.mem cell :: ys, ?_⟩
    exact
      { head :=
          { good := post.good, tick := post.tick, minstret := post.minstret
            code := transport _ _ inv.head.code (fun a ha => same a (Or.inr ha))
            pc := pc, registers := post.registers
            cellRead := (inv.reads _ here).1, linkRead := (inv.reads _ here).2.1
            rootRead := by rw [keyEq _ here]; exact (inv.reads _ here).2.2
            action := inv.head.action }
        ready := ready'
        linked := chain_congr _ _ (fun x hx k hk =>
          keepCell x (tail x hx) _ (link_word (inv.reads x (tail x hx)).2.1 k hk)) chainRest
        roots := fun x hx => by rw [keyEq x (tail x hx)]; exact roots' _ (inv.roots x (tail x hx))
        rooms := fun x hx => by rw [keyEq x (tail x hx)]; exact inv.rooms x (tail x hx)
        reads := fun x hx => by rw [keyEq x (tail x hx)]; exact inv.reads x (tail x hx)
        cellsApart := fun x hx a w => by
          obtain ⟨notW, frame, slots⟩ := inv.cellsApart x (tail x hx) a w
          refine ⟨notW, frame, fun z hz => ?_⟩
          rw [keyEq z (tail z hz)]
          exact slots z (tail z hz) }

theorem walk_done (S : SlotSupply Ready Root pl support writes)
    (transport : ∀ m m', Loaded m → (∀ a, a < textEnd → m'[a]? = m[a]?) → Loaded m')
    {R cells cell copies c after} (inv : WalkInv L Ready Root writes R cells cell copies c)
    (post : L.Iterated R cell copies pl c after) (pc : PCAt L.exitPc after) :
    ∃ copies', WalkExit L Ready R copies' after := by
  obtain ⟨⟨⟨copies', ready'⟩, -, same⟩, pcIf⟩ := stepped L S inv post
  have zero : next c.σ.mem cell = 0#64 := by
    by_cases more : (next c.σ.mem cell != 0#64) = true
    · rw [if_pos more] at pcIf
      rw [PCAt] at pcIf pc
      rw [pcIf] at pc
      exact absurd (Option.some.inj pc).symm L.exit_ne_body
    · simpa using more
  have regs := post.registers
  rw [zero] at regs
  exact ⟨copies', ready', pc, regs, post.good, post.tick, post.minstret,
    transport _ _ inv.head.code (fun a ha => same a (Or.inr ha))⟩

theorem walk_progress (S : SlotSupply Ready Root pl support writes)
    {R cells cell copies c after} (inv : WalkInv L Ready Root writes R cells cell copies c)
    (post : L.Iterated R cell copies pl c after) : rank after < rank c := by
  obtain ⟨⟨-, -, same⟩, -⟩ := stepped L S inv post
  obtain ⟨rest, rfl⟩ := cons_of_head L inv
  obtain ⟨-, -, chainRest⟩ := inv.linked
  have s0c : gprGet c.σ 8 = some cell := gholds_lookup _ inv.head.registers rfl
  have s0a : gprGet after.σ 8 = some (next c.σ.mem cell) := gholds_lookup _ post.registers rfl
  have chainAfter : Skiplist.Chain after.σ.mem (next c.σ.mem cell) rest :=
    chain_congr _ _ (fun x hx k hk => same _ (Or.inl ⟨x, List.mem_cons_of_mem _ hx,
      link_word (inv.reads x (List.mem_cons_of_mem _ hx)).2.1 k hk⟩)) chainRest
  rw [rank_eq s0c inv.linked, rank_eq s0a chainAfter]
  simp

/-- **The walk's obligations from the collection in progress.** -/
theorem walkStep (S : SlotSupply Ready Root pl support writes)
    (transport : ∀ m m', Loaded m → (∀ a, a < textEnd → m'[a]? = m[a]?) → Loaded m') (R : Nat → BitVec 64) :
    L.WalkStep R pl (fun cell copies c => ∃ cells, WalkInv L Ready Root writes R cells cell copies c)
      (fun after => ∃ copies, WalkExit L Ready R copies after) rank where
  head := fun _ _ _ ⟨_, inv⟩ => inv.head
  supply := fun cell copies c ⟨cells, inv⟩ e jumped => by
    obtain ⟨rest, rfl⟩ := cons_of_head L inv
    have room := inv.rooms cell (List.mem_cons_self ..)
    apply S.supply _ copies c.σ.mem e inv.ready _ (slotEntry L jumped room)
    rw [(linked_eq L R cell c.σ.mem).2.2.1]
    exact inv.roots cell (List.mem_cons_self ..)
  frame := fun _ _ c ⟨_, inv⟩ e _ mid jumped done =>
    transport _ _ inv.head.code (fun a ha => (call_keeps L S inv jumped done).2 a (Or.inr ha))
  next := fun _ _ _ _ ⟨_, inv⟩ post pc => by
    obtain ⟨copies', cells', inv'⟩ := walk_next L S transport inv post pc
    exact ⟨copies', cells', inv'⟩
  done := fun _ _ _ _ ⟨_, inv⟩ post pc => walk_done L S transport inv post pc
  donePc := fun _ ⟨_, exit⟩ => exit.pc
  progress := fun _ _ _ _ ⟨_, inv⟩ post => walk_progress L S inv post

/-! ## The VM-stack loop -/

namespace Stack
open StackScan

/-- `q` is one of the slots `p, p + 8, …` below `high`. -/
def Slot (p high : BitVec 64) (q : Nat) : Prop := p.toNat ≤ q ∧ q + 8 ≤ high.toNat ∧ (q - p.toNat) % 8 = 0

/-- The two words the bound test reads: `Caml_state` and the domain's `stack_high`. -/
def Watched (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : Prop :=
  (Layout.sym_Caml_state ≤ a ∧ a < Layout.sym_Caml_state + 8) ∨
  ((bytesT m Layout.sym_Caml_state 8 + BitVec.ofNat 64 Layout.off_stack_high).toNat ≤ a ∧
    a < (bytesT m Layout.sym_Caml_state 8 + BitVec.ofNat 64 Layout.off_stack_high).toNat + 8)

/-- **The VM-stack loop's invariant** at slot `p`. -/
structure Inv (Ready : List PendingCopy → Std.ExtHashMap Nat (BitVec 8) → Prop)
    (Root : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop) (writes : Nat → Prop) (Extra : Std.ExtHashMap Nat (BitVec 8) → Prop)
    (R : Nat → BitVec 64) (high p : BitVec 64) (copies : List PendingCopy) (c : Config) : Prop where
  head : HeadInput R p c
  /-- further code the caller needs afterwards (kept with `.text`) -/
  extra : Extra c.σ.mem
  room : p.toNat + 8 ≤ high.toNat
  aligned : (high.toNat - p.toNat) % 8 = 0
  ready : Ready copies c.σ.mem
  highWord : stackHigh c.σ.mem = high
  roots : ∀ q, Slot p high q → Root c.σ.mem q
  frameWindows : ∀ x ∈ OldifyEntry.saves, WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 x.2) 8
  slots : ∀ q, Slot p high q → WriteWindow (BitVec.ofNat 64 q) 8 ∧ ReadWindow (BitVec.ofNat 64 q) 8 ∧
    (q + 8 ≤ (OldifyEntry.frameSp R).toNat ∨ (R 2).toNat ≤ q)
  stateRead : ReadWindow statePtr 8
  highRead : ReadWindow (bytesT c.σ.mem Layout.sym_Caml_state 8 + BitVec.ofNat 64 Layout.off_stack_high) 8
  watched : ∀ a, Watched c.σ.mem a → ¬ writes a ∧ (a < (OldifyEntry.frameSp R).toNat ∨ (R 2).toNat ≤ a) ∧
    ∀ q, Slot p high q → a < q ∨ q + 8 ≤ a

/-- At the loop's exit. -/
structure Exit (Ready : List PendingCopy → Std.ExtHashMap Nat (BitVec 8) → Prop) (Extra : Std.ExtHashMap Nat (BitVec 8) → Prop)
    (R : Nat → BitVec 64) (copies : List PendingCopy) (after : Config) : Prop where
  extra : Extra after.σ.mem
  ready : Ready copies after.σ.mem
  pc : PCAt exitPc after
  registers : ∃ p, GHolds after.σ (headRegs R p)
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  code : Code.Caml_oldify_local_rootsLoaded after.σ.mem
  domain : gprGet after.σ 15 = some (bytesT after.σ.mem Layout.sym_Caml_state 8)

theorem linked_eq (R : Nat → BitVec 64) (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    LocalRootsSites.stackSite.linked (calleeR R p m) 2 = R 2 ∧
    LocalRootsSites.stackSite.linked (calleeR R p m) 10 = bytesT m p.toNat 8 ∧
    LocalRootsSites.stackSite.linked (calleeR R p m) 11 = p ∧
    LocalRootsSites.stackSite.linked (calleeR R p m) 1 = LocalRootsSites.stackSite.call.link := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [SlotSite.linked, calleeR]

theorem frameSp_linked (R : Nat → BitVec 64) (p : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    OldifyEntry.frameSp (LocalRootsSites.stackSite.linked (calleeR R p m)) = OldifyEntry.frameSp R := by
  simp [OldifyEntry.frameSp, SlotSite.linked, calleeR]

theorem slot_self {p high : BitVec 64} (room : p.toNat + 8 ≤ high.toNat) : Slot p high p.toNat :=
  ⟨Nat.le_refl _, room, by simp⟩

variable {Ready : List PendingCopy → Std.ExtHashMap Nat (BitVec 8) → Prop}
  {Root : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop} {pl : Place} {support writes : Nat → Prop}
  {Extra : Std.ExtHashMap Nat (BitVec 8) → Prop}

theorem room_of {R high p copies c} (inv : Inv Ready Root writes Extra R high p copies c) : CallRoom R p := by
  obtain ⟨w, -, apart⟩ := inv.slots p.toNat (slot_self inv.room)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at w
  exact ⟨inv.frameWindows, w, apart⟩

theorem slotEntry {R high p copies c e} (inv : Inv Ready Root writes Extra R high p copies c) (jumped : Jumped R p c e) :
    SlotEntry (LocalRootsSites.stackSite.linked (calleeR R p c.σ.mem)) c.σ.mem e := by
  obtain ⟨sp2, v10, v11, v1⟩ := linked_eq R p c.σ.mem
  have room := room_of inv
  refine ⟨jumped.good, jumped.minstret, jumped.tick, jumped.memory, jumped.registers, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frameSp_linked]; exact room.windows
  · rw [v10, v11]
  · rw [v11]; exact room.slotWrite
  · rw [v11, frameSp_linked, sp2]; exact room.slotApart
  · rw [v1]; exact LocalRootsSites.stackSite.aligned

/-- **One call keeps** the bound test's words and the code, and readiness. -/
theorem call_keeps (S : SlotSupply Ready Root pl support writes) {R high p copies copies' c e mid}
    (inv : Inv Ready Root writes Extra R high p copies c) (jumped : Jumped R p c e)
    (done : SlotDone (LocalRootsSites.stackSite.linked (calleeR R p c.σ.mem)) copies copies' pl e mid) :
    (Ready copies' mid.σ.mem ∧ ∀ q, Root c.σ.mem q → Root mid.σ.mem q) ∧
    ∀ a, (Watched c.σ.mem a ∨ a < textEnd) → mid.σ.mem[a]? = c.σ.mem[a]? := by
  have room := room_of inv
  have entry := slotEntry inv jumped
  obtain ⟨sp2, -, v11, -⟩ := linked_eq R p c.σ.mem
  have root : Root c.σ.mem ((LocalRootsSites.stackSite.linked (calleeR R p c.σ.mem)) 11).toNat := by
    rw [v11]; exact inv.roots _ (slot_self inv.room)
  refine ⟨S.preserve _ copies copies' c.σ.mem e mid inv.ready root entry done, ?_⟩
  intro a where_
  apply S.footprint _ copies copies' c.σ.mem e mid inv.ready root entry done a
  · rcases where_ with w | low
    · exact (inv.watched a w).1
    · exact S.codeOutside a (by simp only [textEnd, tohostAddr, LibraryLayout.tohostAddr] at low ⊢; omega)
  · rw [frameSp_linked, sp2]
    rcases where_ with w | low
    · exact (inv.watched a w).2.1
    · exact Or.inl (by have := frame_high room; omega)
  · rw [v11]
    rcases where_ with w | low
    · exact (inv.watched a w).2.2 p.toNat (slot_self inv.room)
    · exact Or.inl (by have := slot_high room; omega)

theorem state_kept {m m' : Std.ExtHashMap Nat (BitVec 8)} (same : ∀ a, Watched m a → m'[a]? = m[a]?) :
    bytesT m' Layout.sym_Caml_state 8 = bytesT m Layout.sym_Caml_state 8 := by
  apply OCaml.Vm.Reloc.bytesT_congr (x := Layout.sym_Caml_state) (x' := Layout.sym_Caml_state)
  intro j hj
  rw [byte_one, byte_one, same _ (Or.inl ⟨by omega, by omega⟩)]

theorem high_kept {m m' : Std.ExtHashMap Nat (BitVec 8)} (same : ∀ a, Watched m a → m'[a]? = m[a]?) :
    stackHigh m' = stackHigh m := by
  unfold stackHigh
  rw [state_kept same]
  apply OCaml.Vm.Reloc.bytesT_congr
  intro j hj
  rw [byte_one, byte_one, same _ (Or.inr ⟨by omega, by omega⟩)]

theorem watched_kept {m m' : Std.ExtHashMap Nat (BitVec 8)} (same : ∀ a, Watched m a → m'[a]? = m[a]?) (a : Nat) :
    Watched m' a ↔ Watched m a := by
  unfold Watched
  rw [state_kept same]

/-- `caml_oldify_local_roots`' code survives memory that keeps `.text`. -/
theorem image_transport {m m' : Std.ExtHashMap Nat (BitVec 8)} (code : Code.Caml_oldify_local_rootsLoaded m)
    (same : ∀ a, a < textEnd → m'[a]? = m[a]?) : Code.Caml_oldify_local_rootsLoaded m' :=
  Code.caml_oldify_local_roots_transport code (fun a _ hi => same a (by simp only [textEnd]; omega))

theorem slot_next {p high : BitVec 64} {q : Nat} (h : Slot (p + 8#64) high q) (room : p.toNat + 8 ≤ high.toNat) :
    Slot p high q := by
  have limit := high.isLt
  have addr : (p + 8#64).toNat = p.toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨lo, hi, al⟩ := h
  rw [addr] at lo al
  exact ⟨by omega, hi, by omega⟩

theorem stack_next (S : SlotSupply Ready Root pl support writes)
    (transport : ∀ m m', Extra m → (∀ a, a < textEnd → m'[a]? = m[a]?) → Extra m') {R high p copies c after}
    (inv : Inv Ready Root writes Extra R high p copies c) (post : Iterated R p copies pl c after) (pc : PCAt bodyPc after) :
    ∃ copies', Inv Ready Root writes Extra R high (p + 8#64) copies' after := by
  obtain ⟨e, copies', mid, jumped, done, memory, pcIf⟩ := post.slot
  obtain ⟨⟨ready', roots'⟩, keep⟩ := call_keeps S inv jumped done
  have sameW : ∀ a, Watched c.σ.mem a → after.σ.mem[a]? = c.σ.mem[a]? := fun a w => by
    rw [memory]; exact keep a (Or.inl w)
  have highEq : stackHigh after.σ.mem = high := by rw [high_kept sameW, inv.highWord]
  have midHigh : stackHigh mid.σ.mem = high := by rw [← memory]; exact highEq
  have more : continues (p + 8#64) mid.σ.mem = true := by
    by_cases h : continues (p + 8#64) mid.σ.mem = true
    · exact h
    · rw [if_neg h] at pcIf
      rw [PCAt] at pcIf pc
      rw [pcIf] at pc
      exact absurd (Option.some.inj pc) exit_ne_body
  have below : (p + 8#64).toNat < high.toNat := by
    have := of_decide_eq_true more
    rwa [midHigh] at this
  have limit := high.isLt
  have addr : (p + 8#64).toNat = p.toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := inv.room; omega
  have room' : (p + 8#64).toNat + 8 ≤ high.toNat := by have := inv.aligned; omega
  have slotNext : Slot p high (p.toNat + 8) := ⟨by omega, by omega, by simp⟩
  have win := (inv.slots _ slotNext).2.1
  have pAddr : BitVec.ofNat 64 (p.toNat + 8) = p + 8#64 := by
    apply BitVec.eq_of_toNat_eq; rw [addr]; simp only [BitVec.toNat_ofNat]; omega
  rw [pAddr] at win
  have stateEq := state_kept sameW
  refine ⟨copies', ?_⟩
  exact
    { head := { good := post.good, tick := post.tick, minstret := post.minstret
                code := image_transport inv.head.code (fun a ha => by rw [memory]; exact keep a (Or.inr ha))
                pc := pc, registers := post.registers, window := win }
      extra := transport _ _ inv.extra (fun a ha => by rw [memory]; exact keep a (Or.inr ha))
      room := room'
      aligned := by have := inv.aligned; omega
      ready := by rw [memory]; exact ready'
      highWord := highEq
      roots := fun q hq => by rw [memory]; exact roots' q (inv.roots q (slot_next hq inv.room))
      frameWindows := inv.frameWindows
      slots := fun q hq => inv.slots q (slot_next hq inv.room)
      stateRead := inv.stateRead
      highRead := by rw [stateEq]; exact inv.highRead
      watched := fun a w => by
        rw [watched_kept sameW] at w
        obtain ⟨notW, frame, slots⟩ := inv.watched a w
        exact ⟨notW, frame, fun q hq => slots q (slot_next hq inv.room)⟩ }

theorem stack_done (S : SlotSupply Ready Root pl support writes)
    (transport : ∀ m m', Extra m → (∀ a, a < textEnd → m'[a]? = m[a]?) → Extra m') {R high p copies c after}
    (inv : Inv Ready Root writes Extra R high p copies c) (post : Iterated R p copies pl c after) (pc : PCAt exitPc after) :
    ∃ copies', Exit Ready Extra R copies' after := by
  obtain ⟨e, copies', mid, jumped, done, memory, -⟩ := post.slot
  obtain ⟨⟨ready', -⟩, keep⟩ := call_keeps S inv jumped done
  exact ⟨copies', transport _ _ inv.extra (fun a ha => by rw [memory]; exact keep a (Or.inr ha)),
    by rw [memory]; exact ready', pc, ⟨_, post.registers⟩, post.good, post.tick, post.minstret,
    image_transport inv.head.code (fun a ha => by rw [memory]; exact keep a (Or.inr ha)), post.domain⟩

theorem callee_frame (S : SlotSupply Ready Root pl support writes) {R high p copies copies' c e mid}
    (inv : Inv Ready Root writes Extra R high p copies c) (jumped : Jumped R p c e)
    (done : SlotDone (LocalRootsSites.stackSite.linked (calleeR R p c.σ.mem)) copies copies' pl e mid) :
    CalleeFrame c mid := by
  obtain ⟨-, keep⟩ := call_keeps S inv jumped done
  refine ⟨image_transport inv.head.code (fun a ha => keep a (Or.inr ha)), inv.stateRead, ?_⟩
  rw [state_kept (fun a w => keep a (Or.inl w))]
  exact inv.highRead

/-- **The VM-stack loop's obligations from the collection in progress.** -/
theorem scanStep (S : SlotSupply Ready Root pl support writes)
    (transport : ∀ m m', Extra m → (∀ a, a < textEnd → m'[a]? = m[a]?) → Extra m')
    (R : Nat → BitVec 64) (high : BitVec 64) :
    ScanStep R high pl (Inv Ready Root writes Extra R high) (fun after => ∃ copies, Exit Ready Extra R copies after) where
  head := fun _ _ _ inv => ⟨inv.head, inv.room⟩
  supply := fun p copies c inv e jumped => by
    apply S.supply _ copies c.σ.mem e inv.ready _ (slotEntry inv jumped)
    rw [(linked_eq R p c.σ.mem).2.2.1]
    exact inv.roots _ (slot_self inv.room)
  frame := fun _ _ _ inv _ _ _ jumped done => callee_frame S inv jumped done
  next := fun _ _ _ _ inv post pc => stack_next S transport inv post pc
  done := fun _ _ _ _ inv post pc => stack_done S transport inv post pc
  donePc := fun _ ⟨_, exit⟩ => exit.pc

end Stack

end OCaml.Vm.Gc.RootLoops
