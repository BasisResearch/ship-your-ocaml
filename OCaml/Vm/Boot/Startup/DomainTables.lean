import OCaml.Vm.Boot.Startup.DomainReady
import OCaml.Vm.Boot.Startup.DomainRecord
import OCaml.Vm.Boot.Startup.MemsetReadback
import OCaml.Vm.Boot.Startup.NativeFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-! caml_init_domain's record and caml_alloc_minor_tables' three ref tables:
the fields caml_init_gc reads (`DomainCore`) and one published, cleared table
(`TableKept`), carried by one table round (`RoundMem`: allocate, publish,
clear), used three times. -/

theorem slot_address_nat (slot : MinorTableSlot) : slot.address.toNat = domainField slot.offset := by
  cases slot <;> decide

theorem slot_offset_bounds (slot : MinorTableSlot) : 104 ≤ slot.offset ∧ slot.offset + 8 ≤ 128 := by
  cases slot <;> decide

theorem domain_arena : heapStart ≤ firstDomainPtr.toNat ∧ firstDomainPtr.toNat + 928 ≤ heapEnd := by decide

/-- The minor-heap fields caml_init_domain clears and caml_init_gc reads. -/
structure DomainCore (H : List (Nat × Nat)) (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  owned : (firstDomainPtr.toNat, 928) ∈ H
  young : bytesT m (domainField 8) 8 = 0#64
  start : bytesT m (domainField 32) 8 = 0#64
  trigger : bytesT m (domainField 56) 8 = 0#64

/-- A ref table published at `slot` and cleared: its pointer, its empty
`base` word, its block and its separation from the domain record. -/
structure TableKept (H : List (Nat × Nat)) (m : Std.ExtHashMap Nat (BitVec 8)) (slot : MinorTableSlot)
    (t : BitVec 64) : Prop where
  ptr : bytesT m slot.address.toNat 8 = t
  spot : RefTableSpot t
  empty : bytesT m t.toNat 8 = 0#64
  owned : (t.toNat, 56) ∈ H
  domain : t.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t.toNat

/-- One table round's memory effect over the owned blocks `H`: every owned
byte outside the slot word and the new block is kept; the slot holds `t`;
`t`'s block is cleared, fresh and in the arena. -/
structure RoundMem (H : List (Nat × Nat)) (slot : MinorTableSlot) (t : BitVec 64)
    (m m' : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  keep : ∀ e ∈ H, heapStart ≤ e.1 → e.1 + e.2 ≤ heapEnd → ∀ x, InExt e x →
    (x < slot.address.toNat ∨ slot.address.toNat + 8 ≤ x) → (m'[x]?).getD 0 = (m[x]?).getD 0
  ptr : bytesT m' slot.address.toNat 8 = t
  empty : bytesT m' t.toNat 8 = 0#64
  region : Memset56Region t.toNat
  fresh : FreshBlock vsaLayoutP H t.toNat 56

/-- A round from an allocator frame over `H`, the slot store and the memset. -/
theorem roundMem_of {H : List (Nat × Nat)} {slot : MinorTableSlot} {t : BitVec 64}
    {m0 m1 : Std.ExtHashMap Nat (BitVec 8)}
    (alloc : ∀ e ∈ H, heapStart ≤ e.1 → e.1 + e.2 ≤ heapEnd → ∀ x, InExt e x → (m1[x]?).getD 0 = (m0[x]?).getD 0)
    (fresh : FreshBlock vsaLayoutP H t.toNat 56) (region : Memset56Region t.toNat)
    (domain : (firstDomainPtr.toNat, 928) ∈ H) :
    RoundMem H slot t m0 (memset56Memory (writeLog m1 (tablePublishLog slot t)) t.toNat) := by
  have apartD := FreshBlock.apart fresh domain (by decide) (by decide)
  have addr := slot_address_nat slot
  have bounds := slot_offset_bounds slot
  have outside (x : Nat) (e : Nat × Nat) (he : e ∈ H) (hx : InExt e x) : x < t.toNat ∨ t.toNat + 56 ≤ x := by
    have a := FreshBlock.apart fresh (q := e.1) (m := e.2) he (by decide) (by
      unfold InExt at hx; omega)
    unfold InExt at hx
    omega
  refine ⟨fun e he lo hi x hx slotOut => ?_, ?_, ?_, region, fresh⟩
  · rw [show ((memset56Memory _ t.toNat)[x]?).getD 0 = ((writeLog m1 (tablePublishLog slot t))[x]?).getD 0 by
      rw [memset56Memory_out region _ x (outside x e he hx)],
      writeLog_out _ _ _ (show OutL (tablePublishLog slot t) x by
        simp only [tablePublishLog, OutL]; exact ⟨slotOut, trivial⟩)]
    exact alloc e he lo hi x hx
  · rw [word_observed (m := writeLog m1 (tablePublishLog slot t)) _ fun i hi => by
      rw [memset56Memory_out region _ _ (by unfold domainField at addr; omega)]]
    exact word_writeLog _ _ _
  · rw [← read8_value]
    have z (i : Nat) (hi : i < 8) : ((memset56Memory (writeLog m1 (tablePublishLog slot t)) t.toNat)[t.toNat + i]?).getD 0 = 0#8 := by
      rw [memset56Memory_inside region _ _ (by omega) (by omega)]; rfl
    have z0 := z 0 (by decide)
    simp only [Nat.add_zero] at z0
    simp only [Primitives.read8, z0, z 1 (by decide), z 2 (by decide), z 3 (by decide), z 4 (by decide),
      z 5 (by decide), z 6 (by decide), z 7 (by decide)]
    rfl

theorem DomainCore.round {H : List (Nat × Nat)} {slot : MinorTableSlot} {t : BitVec 64}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} (h : DomainCore H m) (R : RoundMem H slot t m m') :
    DomainCore ((t.toNat, 56) :: H) m' := by
  have addr := slot_address_nat slot
  have bounds := slot_offset_bounds slot
  have field (off : Nat) (hoff : off + 8 ≤ 104) : bytesT m' (domainField off) 8 = bytesT m (domainField off) 8 :=
    word_observed _ fun i hi => R.keep _ h.owned domain_arena.1 domain_arena.2 _
      (by unfold InExt domainField; dsimp only; omega) (by unfold domainField at addr ⊢; omega)
  exact ⟨List.mem_cons_of_mem _ h.owned, (field 8 (by decide)).trans h.young, (field 32 (by decide)).trans h.start,
    (field 56 (by decide)).trans h.trigger⟩

theorem TableKept.round {H : List (Nat × Nat)} {slot slot' : MinorTableSlot} {t t' : BitVec 64}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} (h : TableKept H m slot t) (R : RoundMem H slot' t' m m')
    (domain : (firstDomainPtr.toNat, 928) ∈ H) (other : slot.offset + 8 ≤ slot'.offset ∨ slot'.offset + 8 ≤ slot.offset) :
    TableKept ((t'.toNat, 56) :: H) m' slot t := by
  have a := slot_address_nat slot
  have a' := slot_address_nat slot'
  have b := slot_offset_bounds slot
  have b' := slot_offset_bounds slot'
  have spot := h.spot
  have apart := h.domain
  have sl := spot.low
  have sh := spot.high
  refine ⟨?_, h.spot, ?_, List.mem_cons_of_mem _ h.owned, h.domain⟩
  · rw [word_observed (m := m) _ fun i hi => R.keep _ domain domain_arena.1 domain_arena.2 _
      (by unfold InExt; dsimp only; unfold domainField at a; omega) (by unfold domainField at a a'; omega)]
    exact h.ptr
  · rw [word_observed (m := m) _ fun i hi => R.keep _ h.owned sl sh _
      (by unfold InExt; dsimp only; omega) (by unfold domainField at a'; omega)]
    exact h.empty

theorem TableKept.of_round {H : List (Nat × Nat)} {slot : MinorTableSlot} {t : BitVec 64}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} (R : RoundMem H slot t m m') (domain : (firstDomainPtr.toNat, 928) ∈ H) :
    TableKept ((t.toNat, 56) :: H) m' slot t where
  ptr := R.ptr
  spot := ⟨R.region.lower, R.region.upper, by have := R.region.aligned; omega⟩
  empty := R.empty
  owned := List.mem_cons_self ..
  domain := FreshBlock.apart R.fresh domain (by decide) (by decide)

/-- Two tables of successive rounds are apart. -/
theorem TableKept.apart_round {H : List (Nat × Nat)} {slot slot' : MinorTableSlot} {t t' : BitVec 64}
    {m m' : Std.ExtHashMap Nat (BitVec 8)} (h : TableKept H m slot t) (R : RoundMem H slot' t' m m') :
    t.toNat + 56 ≤ t'.toNat ∨ t'.toNat + 56 ≤ t.toNat :=
  (FreshBlock.apart R.fresh h.owned (by decide) (by decide)).symm

/-- Memory equal on the owned arena bytes keeps the core and the tables. -/
theorem DomainCore.of_arena {H : List (Nat × Nat)} {m m' : Std.ExtHashMap Nat (BitVec 8)} (h : DomainCore H m)
    (f : ∀ x, heapStart ≤ x → x < heapEnd → (m'[x]?).getD 0 = (m[x]?).getD 0) : DomainCore H m' := by
  have field (off : Nat) (hoff : off + 8 ≤ 928) : bytesT m' (domainField off) 8 = bytesT m (domainField off) 8 :=
    word_observed _ fun i hi => f _ (by have := domain_arena; unfold domainField; omega)
      (by have := domain_arena; unfold domainField; omega)
  exact ⟨h.owned, (field 8 (by decide)).trans h.young, (field 32 (by decide)).trans h.start,
    (field 56 (by decide)).trans h.trigger⟩
/-- A malloc run's frame keeps every byte of its owned arena blocks. -/
theorem local_owned {live : Nat → Prop} {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)} {rs : List Nat}
    {H : List (Nat × Nat)} {s : BitVec 64} {before after : Config}
    (post : LocalFrame live ro text rs (mS H s) before after) (high : heapEnd + allocHeadroom ≤ s.toNat) :
    ∀ e ∈ H, heapStart ≤ e.1 → e.1 + e.2 ≤ heapEnd → ∀ x, InExt e x →
      (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := by
  intro e he lo hi x hx
  have hx' := hx
  unfold InExt at hx'
  refine post.memory x ?_
  change ¬ (stackWin s allocHeadroom x ∨ vsaFoot H x)
  rintro (w | foot)
  · unfold stackWin InExt at w; omega
  · exact owned_not_foot (by omega) ⟨e, he, hx⟩ foot

theorem TableNextAllocated.owned {H : List (Nat × Nat)} {capacity : Nat} {last : Bool} {before after : Config}
    (w : TableNextAllocated H capacity last before after) :
    ∀ e ∈ H, heapStart ≤ e.1 → e.1 + e.2 ≤ heapEnd → ∀ x, InExt e x →
      (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := by
  intro e he lo hi x hx
  rw [local_owned w.allocation.toLocalFrame (by decide) e he lo hi x hx, w.dispatch.memory, w.setup.memory]
  rfl

theorem TableNextInitialized.round {H : List (Nat × Nat)} {capacity : Nat} {before after : Config}
    (w : TableNextInitialized H capacity before after) (domain : (firstDomainPtr.toNat, 928) ∈ H) :
    RoundMem H .ephemerons (vsaReg w.allocated 10) before.σ.mem after.σ.mem := by
  rw [w.zeroing.memory, w.publication.memory]
  exact roundMem_of w.allocation.owned w.allocation.allocation.result.fresh w.allocation.region domain

/-- The domain record and its three published, cleared tables. -/
structure DomainTablesAt (H : List (Nat × Nat)) (m : Std.ExtHashMap Nat (BitVec 8)) (t1 t2 t3 : BitVec 64) : Prop where
  core : DomainCore H m
  refs : TableKept H m .refs t1
  ephemerons : TableKept H m .ephemerons t2
  customs : TableKept H m .customs t3
  apart12 : t1.toNat + 56 ≤ t2.toNat ∨ t2.toNat + 56 ≤ t1.toNat
  apart13 : t1.toNat + 56 ≤ t3.toNat ∨ t3.toNat + 56 ≤ t1.toNat
  apart23 : t2.toNat + 56 ≤ t3.toNat ∨ t3.toNat + 56 ≤ t2.toNat

/-- caml_init_domain's field stores (`domainFieldsLog`, inside the record)
complete `DomainKept`: `stat_heap_wsz` is cleared, everything else read is kept. -/
theorem DomainTablesAt.fields {H : List (Nat × Nat)} {m : Std.ExtHashMap Nat (BitVec 8)} {t1 t2 t3 : BitVec 64}
    (h : DomainTablesAt H m t1 t2 t3) : DomainKept H (writeLog m domainFieldsLog) t1 t2 t3 := by
  have out (off : Nat) (hoff : off = 8 ∨ off = 32 ∨ off = 56 ∨ off = 104 ∨ off = 112 ∨ off = 120) :
      bytesT (writeLog m domainFieldsLog) (domainField off) 8 = bytesT m (domainField off) 8 :=
    bytesT_writeLog_out _ (domainFields_out off hoff)
  have table {slot : MinorTableSlot} {t : BitVec 64} (k : TableKept H m slot t) :
      bytesT (writeLog m domainFieldsLog) t.toNat 8 = bytesT m t.toNat 8 :=
    word_observed _ fun i hi => by
      have d := k.domain
      rw [frameOn_writeLog _ _ _ domainFields_log_inside _ (by
        simp only [OutW, domainFieldsWindows, and_true]; omega)]
  have addr (slot : MinorTableSlot) : slot.address.toNat = domainField slot.offset := slot_address_nat slot
  exact {
    owned := h.core.owned
    idle := by rw [out 8 (by decide), out 56 (by decide), h.core.young, h.core.trigger]
    noYoung := (out 32 (by decide)).trans h.core.start
    noHeap := domainFields_heap_word m
    refs := {
      ptr1 := (out 104 (by decide)).trans (by rw [← show MinorTableSlot.refs.address.toNat = domainField 104 from addr _]; exact h.refs.ptr)
      ptr2 := (out 112 (by decide)).trans (by rw [← show MinorTableSlot.ephemerons.address.toNat = domainField 112 from addr _]; exact h.ephemerons.ptr)
      ptr3 := (out 120 (by decide)).trans (by rw [← show MinorTableSlot.customs.address.toNat = domainField 120 from addr _]; exact h.customs.ptr)
      spot1 := h.refs.spot
      spot2 := h.ephemerons.spot
      spot3 := h.customs.spot
      empty1 := (table h.refs).trans h.refs.empty
      empty2 := (table h.ephemerons).trans h.ephemerons.empty
      empty3 := (table h.customs).trans h.customs.empty
      apart12 := h.apart12
      apart23 := h.apart23
      domain1 := h.refs.domain
      apart13 := h.apart13
      domain2 := h.ephemerons.domain
      domain3 := h.customs.domain
      owned1 := h.refs.owned
      owned2 := h.ephemerons.owned
      owned3 := h.customs.owned } }
/-- Startup readiness and the domain record over the same owned blocks. -/
structure ReadyAt (H : List (Nat × Nat)) (t1 t2 t3 : BitVec 64) (capacity : Nat) (sp ra : BitVec 64) (c : Config) :
    Prop where
  ready : RuntimeReady H capacity sp ra c
  kept : DomainKept H c.σ.mem t1 t2 t3

/-- Some owned blocks carry readiness and the domain record. -/
def ReadyKept (capacity : Nat) (sp ra : BitVec 64) (c : Config) : Prop :=
  ∃ H t1 t2 t3, ReadyAt H t1 t2 t3 capacity sp ra c

theorem ReadyKept.ready {capacity : Nat} {sp ra : BitVec 64} {c : Config} (h : ReadyKept capacity sp ra c) :
    ∃ H, (firstDomainPtr.toNat, 928) ∈ H ∧ RuntimeReady H capacity sp ra c := by
  obtain ⟨H, _, _, _, r⟩ := h
  exact ⟨H, r.kept.owned, r.ready⟩

/-- A step that re-establishes readiness and keeps the arena keeps the record. -/
theorem ReadyAt.step {H : List (Nat × Nat)} {t1 t2 t3 : BitVec 64} {capacity capacity' : Nat} {sp ra sp' ra' : BitVec 64}
    {before after : Config} (h : ReadyAt H t1 t2 t3 capacity sp ra before)
    (ready : RuntimeReady H capacity' sp' ra' after)
    (f : ∀ x, heapStart ≤ x → x < heapEnd → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0) :
    ReadyAt H t1 t2 t3 capacity' sp' ra' after :=
  ⟨ready, h.kept.of_arena f⟩

/-- A store log confined to a native frame above the arena keeps the arena. -/
theorem arena_of_stack {before after : Config} {log : List WEntry} {sp : BitVec 64} {size : Nat}
    (memory : after.σ.mem = writeLog before.σ.mem log) (inside : LogInW [⟨nativeFrameBase sp size, sp.toNat⟩] log)
    (deep : heapEnd ≤ nativeFrameBase sp size) :
    ∀ x, heapStart ≤ x → x < heapEnd → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := fun x _ hx => by
  rw [memory, frameOn_writeLog _ _ _ inside x ⟨Or.inl (show x < nativeFrameBase sp size by omega), trivial⟩]

theorem ReadyAt.kept' {H : List (Nat × Nat)} {t1 t2 t3 : BitVec 64} {capacity : Nat} {sp ra : BitVec 64} {c : Config}
    (h : ReadyAt H t1 t2 t3 capacity sp ra c) : ReadyKept capacity sp ra c := ⟨H, t1, t2, t3, h⟩
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives Startup
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone : Config}

/-- caml_init_domain clears `young_limit`, `young_start` and `young_trigger`; the
table prologue's stack saves and dispatch keep them. -/
theorem ResetTableMalloc.core
    (w : ResetTableMalloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc) :
    DomainCore firstDomainHeap atTableMalloc.σ.mem := by
  have init : DomainCore firstDomainHeap atTables.σ.mem := by
    rw [w.request.tables.post.memory]
    exact ⟨by simp [firstDomainHeap], domainInit_zero_field _ 8 (by decide),
      domainInit_zero_field _ 32 (by decide), domainInit_zero_field _ 56 (by decide)⟩
  rw [w.post.memory, w.request.post.memory]
  refine init.of_arena fun x lo hi => ?_
  have stack : heapEnd + 24 ≤ firstMallocStack.toNat := by decide
  rw [writeLog_out _ _ _ (by
    simp only [minorTablesLog, OutL]
    exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), trivial⟩)]

/-- The first table round. -/
theorem ResetTableZeroed.round
    (w : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero) :
    RoundMem firstDomainHeap .refs (vsaReg afterTable 10) atTableMalloc.σ.mem afterZero.σ.mem := by
  rw [w.post.memory, w.published.post.memory]
  exact roundMem_of (local_owned w.published.allocation.post.toLocalFrame (by decide))
    w.published.allocation.post.result.fresh w.published.allocation.region (by simp [firstDomainHeap])

/-- The domain record and the three tables after caml_alloc_minor_tables, with
readiness over the same blocks. -/
theorem ResetTablesReturn.tables
    (w : ResetTablesReturn initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned) :
    ∃ t2 : BitVec 64,
      RuntimeReady (((vsaReg afterThird 10).toNat, 56) :: (t2.toNat, 56) :: firstTableHeap (vsaReg afterTable 10))
        (startupAllocatorCredits - 192) firstMallocStack jal_8002a934_call.link returned ∧
      DomainTablesAt (((vsaReg afterThird 10).toNat, 56) :: (t2.toNat, 56) :: firstTableHeap (vsaReg afterTable 10))
        returned.σ.mem (vsaReg afterTable 10) t2 (vsaReg afterThird 10) := by
  obtain ⟨a⟩ := w.third.allocation
  have d0 : (firstDomainPtr.toNat, 928) ∈ firstDomainHeap := by simp [firstDomainHeap]
  have R1 := w.third.first.round
  have c1 := w.third.first.published.allocation.before.core.round R1
  have k1 := TableKept.of_round R1 d0
  have d1 : (firstDomainPtr.toNat, 928) ∈ firstTableHeap (vsaReg afterTable 10) := c1.owned
  have R2 := a.initialized.round d1
  have c2 := c1.round R2
  have k1' := k1.round R2 d1 (by decide)
  have k2 := TableKept.of_round R2 d1
  have d2 := c2.owned
  have R3 : RoundMem (((vsaReg a.initialized.allocated 10).toNat, 56) :: firstTableHeap (vsaReg afterTable 10))
      .customs (vsaReg afterThird 10) a.middle.σ.mem returned.σ.mem := by
    rw [w.post.memory, w.publication.memory]
    exact roundMem_of a.allocation.owned a.allocation.allocation.result.fresh w.third.region d2
  exact ⟨_, w.ready_of a, {
    core := c2.round R3
    refs := k1'.round R3 d2 (by decide)
    ephemerons := k2.round R3 d2 (by decide)
    customs := TableKept.of_round R3 d2
    apart12 := k1.apart_round R2
    apart13 := k1'.apart_round R3
    apart23 := k2.apart_round R3 }⟩

/-- caml_init_domain returns with readiness and `DomainKept` over the same blocks. -/
theorem ResetDomainReturned.kept
    (w : ResetDomainReturned initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone) :
    ReadyKept (startupAllocatorCredits - 192) (firstMallocStack + 16#64) jal_80004d94_call.link domainDone := by
  obtain ⟨t2, ready, tables⟩ := w.tables.tables
  refine ⟨_, vsaReg afterTable 10, t2, vsaReg afterThird 10, w.ready_of tables.core.owned ready, ?_⟩
  rw [w.post.memory, show writeLog fieldsDone.σ.mem [] = fieldsDone.σ.mem from rfl, w.fields.memory]
  exact tables.fields
end OCaml.Vm.Boot.WhileMinElfParse
