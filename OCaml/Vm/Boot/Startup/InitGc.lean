import OCaml.Vm.Boot.Startup.InitGcSteps
import OCaml.Vm.Boot.Startup.GcMessageReady
import OCaml.Vm.Boot.Startup.PageTable
import OCaml.Vm.Gc.ReadyCalls

/-! caml_init_gc, composed with its callees, at the default parameters. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  OCaml.Vm.Gc LeanRV64DExecutable

/-- The ref tables' facts that do not mention the page table. -/
structure RefTablesPre (H : List (Nat × Nat)) (m : Std.ExtHashMap Nat (BitVec 8)) (t1 t2 t3 : BitVec 64) : Prop where
  ptr1 : bytesT m (domainField 104) 8 = t1
  ptr2 : bytesT m (domainField 112) 8 = t2
  ptr3 : bytesT m (domainField 120) 8 = t3
  spot1 : RefTableSpot t1
  spot2 : RefTableSpot t2
  spot3 : RefTableSpot t3
  empty1 : bytesT m t1.toNat 8 = 0#64
  empty2 : bytesT m t2.toNat 8 = 0#64
  empty3 : bytesT m t3.toNat 8 = 0#64
  apart12 : t1.toNat + 56 ≤ t2.toNat ∨ t2.toNat + 56 ≤ t1.toNat
  apart23 : t2.toNat + 56 ≤ t3.toNat ∨ t3.toNat + 56 ≤ t2.toNat
  domain1 : t1.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t1.toNat
  apart13 : t1.toNat + 56 ≤ t3.toNat ∨ t3.toNat + 56 ≤ t1.toNat
  domain2 : t2.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t2.toNat
  domain3 : t3.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t3.toNat
  owned1 : (t1.toNat, 56) ∈ H
  owned2 : (t2.toNat, 56) ∈ H
  owned3 : (t3.toNat, 56) ∈ H

/-- A fresh page table's slots are apart from the ref tables. -/
theorem RefTablesPre.at {H : List (Nat × Nat)} {m : Std.ExtHashMap Nat (BitVec 8)} {t1 t2 t3 ent : BitVec 64}
    (R : RefTablesPre H m t1 t2 t3) (fresh : FreshBlock vsaLayoutP H ent.toNat 16384) :
    RefTablesAt ((ent.toNat, 16384) :: H) ent m t1 t2 t3 := by
  have apart (t : BitVec 64) (owned : (t.toNat, 56) ∈ H) : t.toNat + 56 ≤ ent.toNat ∨ ent.toNat + 16384 ≤ t.toNat := by
    have a := fresh.2.2.2 _ owned
    rcases Nat.lt_or_ge t.toNat ent.toNat with h | h
    · rcases Nat.lt_or_ge (t.toNat + 55) ent.toNat with h' | h'
      · exact Or.inl (by omega)
      · exact absurd (show InExt (t.toNat, 56) ent.toNat by unfold InExt; dsimp only; omega)
          (a ent.toNat (by unfold InExt; dsimp only; omega))
    · rcases Nat.lt_or_ge t.toNat (ent.toNat + 16384) with h' | h'
      · exact absurd (show InExt (t.toNat, 56) t.toNat by unfold InExt; dsimp only; omega)
          (a t.toNat (by unfold InExt; dsimp only; omega))
      · exact Or.inr h'
  exact ⟨R.ptr1, R.ptr2, R.ptr3, R.spot1, R.spot2, R.spot3, R.empty1, R.empty2, R.empty3, R.apart12, R.apart23,
    R.domain1, R.apart13, R.domain2, R.domain3, apart _ R.owned1, apart _ R.owned2, apart _ R.owned3,
    List.mem_cons_of_mem _ R.owned1, List.mem_cons_of_mem _ R.owned2, List.mem_cons_of_mem _ R.owned3⟩

/-- caml_init_gc is called with the default parameters (`OCAMLRUNPARAM`
unset): minor 262144 words, major 126976 words, increment 15, percent free
120, max 500, window 1, custom ratios 44/100, minor max 8192 bytes, policy 2. -/
structure InitGcCall (H : List (Nat × Nat)) (cap c1 c2 cA cM cP : Nat)
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur : BitVec 64) (c : Config) : Prop where
  pc : PCAt 0x8001f2c4#64 c
  regs : GHolds c.σ [(2, sp), (9, s1), (18, s2), (19, s3), (20, s4), (21, s5), (22, s6), (23, s7), (24, s8),
    (25, s9), (1, ra), (8, s0), (10, 262144#64), (12, 15#64), (13, 120#64), (14, 500#64), (15, 1#64), (16, 44#64),
    (17, 100#64), (11, 126976#64)]
  ready : RuntimeReady H (cap + c2 + c1 + cA + cM + cP) sp ra c
  frame : NativeFrame sp (96 + (64 + (32 + allocHeadroom)))
  argWindow0 : ReadWindow sp 8
  argWindow8 : ReadWindow (sp + 8#64) 8
  arg0 : bytesT c.σ.mem sp.toNat 8 = 8192#64
  arg1 : bytesT c.σ.mem (sp + 8#64).toNat 8 = 2#64
  chargedP : vsaChg 16384 cP
  chargedM : vsaChg (0x200000#64 + 4096#64).toNat cM
  chargedA : vsaChg (heapChunkSize ((0xf8000#64 >>> 3) <<< 3) + 4152#64).toNat cA
  charged1 : vsaChg (24#64).toNat c1
  charged2 : vsaChg (32768#64).toNat c2
  domainOwned : (firstDomainPtr.toNat, 928) ∈ H
  idle : bytesT c.σ.mem (domainField 8) 8 = bytesT c.σ.mem (domainField 56) 8
  noYoung : bytesT c.σ.mem (domainField 32) 8 = 0#64
  noHeap : bytesT c.σ.mem (domainField 336) 8 = 0#64
  refs : RefTablesPre H c.σ.mem t1 t2 t3
  lambdaOff : bytesT c.σ.mem 0x80064cf0 8 = 0#64
  memprofIdle : bytesVal .lw (read8 c.σ.mem 0x80064b30) = 0#64
  huge : bytesT c.σ.mem 0x80064b08 8 = 0#64
  lists : ∀ j, j < 16 → bytesT c.σ.mem (smallList j).toNat 8 = 0#64
  tree : bytesT c.σ.mem largeTreeAddr 8 = 0#64
  least : bytesT c.σ.mem largeLeastAddr 8 = 0#64
  curWsz : bytesT c.σ.mem flCurWszAddr 8 = cur
  quiet : LPins8 c.σ.mem Layout.sym_caml_verb_gc (List.replicate 8 0#8)

/-- caml_page_table_initialize returned into caml_init_gc. -/
structure InitGcTabled (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 blk : BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt jal_8001f344_call.link after
  regs : GHolds after.σ [(2, nativeStack sp 96), (10, 0#64), (9, 262144#64), (18, 8192#64), (19, 2#64), (20, 15#64),
    (21, 120#64), (22, 500#64), (23, 1#64), (24, 44#64), (25, 100#64), (8, 0xf8000#64)]
  ready : RuntimeReady ((blk.toNat, 16384) :: H) capacity (nativeStack sp 96) jal_8001f344_call.link after
  fresh : FreshBlock vsaLayoutP H blk.toNat 16384
  table : PageTableAt after.σ.mem blk
  aligned : blk.toNat % 16 = 0
  slots : ∀ off value, (off, value) ∈ initGcSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 →
    bytesT after.σ.mem (nativeFrameBase sp 96 + off) 8 = value
  kept : ∀ x, x < heapEnd → ¬ vsaFoot H x → OutW pageTableWindows x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem init_gc_to_table (c : Config) (H : List (Nat × Nat)) (cap c1 c2 cA cM cP : Nat)
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur : BitVec 64)
    (A : InitGcCall H cap c1 c2 cA cM cP sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur c) :
    ∃ blk after, Steps c after ∧
      InitGcTabled H (cap + c2 + c1 + cA + cM) sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 blk c after := by
  have regs := A.regs
  have frame96 : NativeFrame sp 96 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have frameIn : NativeFrame (nativeStack sp 96) (64 + (32 + allocHeadroom)) := A.frame.nested (front := 96) (by decide)
  have frameP : NativeFrame (nativeStack sp 96) (32 + allocHeadroom) := frameIn.resize (by omega) (by decide)
  have slots : ∀ off value, (off, value) ∈ initGcSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 → off + 8 ≤ 96 :=
    fun off value member => by simp [initGcSlots] at member; omega
  have inside := frame96.word_log_inside slots
  -- save s0–s9, ra
  obtain ⟨d1, run1, p1⟩ := (init_gc_save c sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 262144#64 A.ready.toLeafInput frame96
    ⟨gholds_lookup (n := 2) _ regs rfl, gholds_lookup (n := 9) _ regs rfl, gholds_lookup (n := 18) _ regs rfl,
      gholds_lookup (n := 19) _ regs rfl, gholds_lookup (n := 20) _ regs rfl, gholds_lookup (n := 21) _ regs rfl,
      gholds_lookup (n := 22) _ regs rfl, gholds_lookup (n := 23) _ regs rfl, gholds_lookup (n := 24) _ regs rfl,
      gholds_lookup (n := 25) _ regs rfl, gholds_lookup (n := 1) _ regs rfl, gholds_lookup (n := 8) _ regs rfl,
      gholds_lookup (n := 10) _ regs rfl, trivial⟩).run c ⟨A.pc, rfl⟩
  have g1 := GprsSame.of_post p1 (by decide)
  have ready1 := A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p1.regs rfl) (g1.get (by decide) (by decide) (by decide) A.ready.raReg) A.ready.aligned
    frame96 inside
  have above (a : Nat) (h : sp.toNat ≤ a) : (d1.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := by
    rw [p1.memory, frameOn_writeLog _ _ _ inside a ⟨Or.inr h, trivial⟩]
  have r96 : nativeStack sp 96 + 96#64 = sp := nativeStack_restore sp 96
  have r104 : nativeStack sp 96 + 104#64 = sp + 8#64 := by
    rw [nativeStack, BitVec.add_assoc]; congr 1
  have spHigh : sp.toNat + 16 ≤ 2 ^ 64 := by
    have := frame96.upper; have : Layout.sym_stack_top + 16 ≤ 2 ^ 64 := by decide
    omega
  have sp8 : (sp + 8#64).toNat = sp.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, Nat.reducePow] at *; omega
  -- the stack arguments; the page table's size
  obtain ⟨d2, run2, p2⟩ := (init_gc_args d1 (nativeStack sp 96) ra 262144#64 126976#64 15#64 120#64 500#64 1#64 44#64
    100#64 8192#64 2#64 ready1.toLeafInput
    ⟨gholds_lookup (n := 2) _ p1.regs rfl, gholds_lookup (n := 10) _ p1.regs rfl,
      g1.get (by decide) (by decide) (by decide) (gholds_lookup (n := 12) _ regs rfl),
      g1.get (by decide) (by decide) (by decide) (gholds_lookup (n := 13) _ regs rfl),
      g1.get (by decide) (by decide) (by decide) (gholds_lookup (n := 14) _ regs rfl),
      g1.get (by decide) (by decide) (by decide) (gholds_lookup (n := 15) _ regs rfl),
      g1.get (by decide) (by decide) (by decide) (gholds_lookup (n := 16) _ regs rfl),
      g1.get (by decide) (by decide) (by decide) (gholds_lookup (n := 17) _ regs rfl),
      g1.get (by decide) (by decide) (by decide) (gholds_lookup (n := 11) _ regs rfl),
      gholds_lookup (n := 6) _ p1.regs rfl, trivial⟩
    (by rw [r96]; exact A.argWindow0) (by rw [r104]; exact A.argWindow8)
    (by rw [r96, word_observed (m := c.σ.mem) _ fun i hi => above (sp.toNat + i) (by omega)]; exact A.arg0)
    (by rw [r104, word_observed (m := c.σ.mem) _ fun i hi => above ((sp + 8#64).toNat + i) (by rw [sp8]; omega)]; exact A.arg1)
    (by decide)).run d1 ⟨p1.pc, rfl⟩
  have g2 := GprsSame.of_post p2 (by decide)
  have ready2 := ready1.stack_log p2 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p2.regs rfl) (g2.get (by decide) (by decide) (by decide) ready1.raReg) A.ready.aligned
    frame96 (by simp only [LogInW])
  have size : (262144#64 <<< 3) + initGcMajorBytes 126976#64 = 0x2f8000#64 := by decide
  obtain ⟨d3, run3, C⟩ := (ready_call jal_8001f344_call_shape jal_8001f344_call_decode (jal_8001f344_call_pins p2.image)
    ready2 [(10, 0x2f8000#64)] ⟨by rw [← size]; exact gholds_lookup (n := 10) _ p2.regs rfl, trivial⟩
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) _ rfl (by decide)).run d2 ⟨p2.pc, rfl⟩
  have gC : GprsSame d2 d3 [1] := ⟨fun n lo hi out => C.frame n lo hi (by simpa using out)⟩
  -- caml_page_table_initialize(0x2f8000)
  obtain ⟨blk, d4, run4, PT⟩ := page_table_initialize d3 H _ cP (nativeStack sp 96) jal_8001f344_call.link {
    pc := by rw [← jal_8001f344_call_target]; exact C.pc
    regs := ⟨C.ready.stack, C.ready.raReg, C.regs.1, trivial⟩
    ready := C.ready
    frame := frameP
    charged := A.chargedP }
  have saved (k : Nat) (member : k ∈ abiSaved) {v : BitVec 64} (h : gprGet d2.σ k = some v) : gprGet d4.σ k = some v := by
    rw [PT.saved k member]
    exact gC.get (by simp [abiSaved] at member; omega) (by simp [abiSaved] at member; omega)
      (by simp [abiSaved] at member; simp; omega) h
  refine ⟨blk, d4, run1.trans (run2.trans (run3.trans run4)), {
    pc := PT.pc
    regs := ⟨PT.ready.stack, gholds_lookup (n := 10) _ PT.regs rfl,
      saved 9 (by decide) (gholds_lookup (n := 9) _ p2.regs rfl), saved 18 (by decide) (gholds_lookup (n := 18) _ p2.regs rfl),
      saved 19 (by decide) (gholds_lookup (n := 19) _ p2.regs rfl), saved 20 (by decide) (gholds_lookup (n := 20) _ p2.regs rfl),
      saved 21 (by decide) (gholds_lookup (n := 21) _ p2.regs rfl), saved 22 (by decide) (gholds_lookup (n := 22) _ p2.regs rfl),
      saved 23 (by decide) (gholds_lookup (n := 23) _ p2.regs rfl), saved 24 (by decide) (gholds_lookup (n := 24) _ p2.regs rfl),
      saved 25 (by decide) (gholds_lookup (n := 25) _ p2.regs rfl),
      saved 8 (by decide) (by rw [gholds_lookup (n := 8) _ p2.regs rfl]; decide), trivial⟩
    ready := PT.ready
    fresh := PT.fresh
    table := PT.table
    aligned := PT.aligned
    slots := fun off value member => by
      have bound := slots off value member
      have stackNat : (nativeStack sp 96).toNat = sp.toNat - 96 := frame96.stack_nat
      rw [word_observed (m := d1.σ.mem) _ fun i hi => by
        rw [PT.caller _ (by rw [stackNat]; unfold nativeFrameBase; omega), C.memory, p2.memory]; rfl, p1.memory]
      exact frame96.word_log_read slots (by simp [initGcSlots]) _ member
    kept := fun x low foot out => by
      have fI := frameIn.lower
      have f96 := frame96.lower
      have xb : x < nativeFrameBase sp 96 := by unfold nativeFrameBase; omega
      rw [PT.kept x (by omega) foot out, C.memory, p2.memory,
        show writeLog d1.σ.mem [] = d1.σ.mem from rfl, p1.memory,
        frameOn_writeLog _ _ _ inside x ⟨Or.inl xb, trivial⟩] }⟩

/-- caml_set_minor_heap_size returned into caml_init_gc. -/
structure InitGcMinored (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 blk raw : BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt jal_8001f36c_call.link after
  regs : GHolds after.σ [(2, nativeStack sp 96), (10, 0#64), (8, 0xf8000#64), (9, 262144#64), (18, 8192#64),
    (19, 2#64), (20, 15#64), (21, 120#64), (22, 500#64), (23, 1#64), (24, 44#64), (25, 100#64)]
  ready : RuntimeReady ((raw.toNat, (0x200000#64 + 4096#64).toNat) :: (blk.toNat, 16384) :: H) capacity
    (nativeStack sp 96) jal_8001f36c_call.link after
  tableFresh : FreshBlock vsaLayoutP H blk.toNat 16384
  tableAligned : blk.toNat % 16 = 0
  minorFresh : FreshBlock vsaLayoutP ((blk.toNat, 16384) :: H) raw.toNat (0x200000#64 + 4096#64).toNat
  young : YoungAt after.σ.mem (pageAbove raw) 0x200000#64 raw
  table : PageTableFields after.σ.mem (BitVec.ofNat 64 512) blk
  count : pageCount after.σ.mem blk.toNat = 512
  only : ∀ i, i < 2048 → slotWord after.σ.mem blk i ≠ 0#64 →
    ∃ j, j < 512 ∧ slotWord after.σ.mem blk i = 2#64 ||| blockPage (pageAbove raw) j
  slots : ∀ off value, (off, value) ∈ initGcSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 →
    bytesT after.σ.mem (nativeFrameBase sp 96 + off) 8 = value
  lowKept : ∀ x, x < heapStart → ¬ allocGlobal x → (x < pageTable ∨ pageTable + 0x28 ≤ x) →
    (x < 0x80064cc8 ∨ 0x80064cc8 + 8 ≤ x) → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  domainHigh : ∀ off, 128 ≤ off → off + 8 ≤ 928 →
    bytesT after.σ.mem (domainField off) 8 = bytesT before.σ.mem (domainField off) 8

/-- A fresh block lies apart from every live block. -/
theorem FreshBlock.apart {L : DlLayout} {H : List (Nat × Nat)} {p n : Nat} (fresh : FreshBlock L H p n)
    {q m : Nat} (owned : (q, m) ∈ H) (pos : 0 < n) (qpos : 0 < m) : p + n ≤ q ∨ q + m ≤ p := by
  have a := fresh.2.2.2 _ owned
  rcases Nat.lt_or_ge p q with h | h
  · rcases Nat.lt_or_ge (p + n) (q + 1) with h' | h'
    · exact Or.inl (by omega)
    · exact absurd (show InExt (q, m) q by unfold InExt; dsimp only; omega) (a q (by unfold InExt; dsimp only; omega))
  · rcases Nat.lt_or_ge p (q + m) with h' | h'
    · exact absurd (show InExt (q, m) p by unfold InExt; dsimp only; omega) (a p (by unfold InExt; dsimp only; omega))
    · exact Or.inr h'

theorem init_gc_to_minor (c d4 : Config) (H : List (Nat × Nat)) (cap c1 c2 cA cM cP : Nat)
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur blk : BitVec 64)
    (A : InitGcCall H cap c1 c2 cA cM cP sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur c)
    (T : InitGcTabled H (cap + c2 + c1 + cA + cM) sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 blk c d4) :
    ∃ raw after, Steps d4 after ∧
      InitGcMinored H (cap + c2 + c1 + cA) sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 blk raw c after := by
  have frame96 : NativeFrame sp 96 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have frameIn : NativeFrame (nativeStack sp 96) (64 + (32 + allocHeadroom)) := A.frame.nested (front := 96) (by decide)
  have hS : heapStart = 0x8007d140 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  have hP : pageTable = 0x800684b8 := rfl
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  have bLow : 0x8007d140 ≤ blk.toNat := T.fresh.2.1
  have bHigh : blk.toNat + 16384 ≤ 0x86800000 := T.fresh.2.2.1
  -- the minor heap's size
  obtain ⟨d5, run5, p5⟩ := (init_gc_minor_front d4 jal_8001f344_call.link T.ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ T.regs rfl, gholds_lookup (n := 9) _ T.regs rfl, trivial⟩).run d4 ⟨T.pc, rfl⟩
  have g5 := GprsSame.of_post p5 (by decide)
  have ready5 := T.ready.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
    (g5.get (by decide) (by decide) (by decide) T.ready.stack) (g5.get (by decide) (by decide) (by decide) T.ready.raReg)
    (by decide) frameIn (by simp only [LogInW])
  obtain ⟨d6, run6, C⟩ := (ready_call jal_8001f36c_call_shape jal_8001f36c_call_decode (jal_8001f36c_call_pins p5.image)
    ready5 [(10, 0x200000#64)] ⟨gholds_lookup (n := 10) _ p5.regs rfl, trivial⟩
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) _ rfl (by decide)).run d5 ⟨p5.pc, rfl⟩
  have gC : GprsSame d5 d6 [1] := ⟨fun n lo hi out => C.frame n lo hi (by simpa using out)⟩
  have g46 := (g5.trans gC).mono (vs := [15, 10, 1]) (by decide)
  have mem6 : d6.σ.mem = d4.σ.mem := C.memory.trans p5.memory
  -- d6's memory against the caller's
  have back (x : Nat) (low : x < heapEnd) (foot : ¬ vsaFoot H x) (out : OutW pageTableWindows x) :
      (d6.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [mem6, T.kept x low foot out]
  have domainOwned := A.domainOwned
  have domainWord (off : Nat) (h : off + 8 ≤ 928) :
      bytesT d6.σ.mem (domainField off) 8 = bytesT c.σ.mem (domainField off) 8 :=
    word_observed _ fun i hi => back _ (InDomain.field h hi).below ((InDomain.field h hi).not_foot domainOwned)
      (by simp only [OutW, pageTableWindows, domainField, dom, hP, and_true]; omega)
  have heapWord (t : BitVec 64) (spot : RefTableSpot t) (owned : (t.toNat, 56) ∈ H) :
      bytesT d6.σ.mem t.toNat 8 = bytesT c.σ.mem t.toNat 8 := by
    have lo := spot.low
    have hi := spot.high
    exact word_observed _ fun i hi8 => back _ (by omega) (owned_not_foot' lo owned (by omega) (by omega))
      (by simp only [OutW, pageTableWindows, and_true]; rw [hP]; rw [hS] at lo; omega)
  have lowAgree (a : Nat) (ha : a + 8 ≤ 0x8007d140) (alloc : ∀ i, i < 8 → ¬ allocGlobal (a + i))
      (rec : a + 8 ≤ pageTable ∨ pageTable + 0x28 ≤ a) : ∀ i, i < 8 → (d6.σ.mem[a + i]?).getD 0 = (c.σ.mem[a + i]?).getD 0 :=
    fun i hi => back _ (by rw [hE]; omega) (fun f => f.elim (alloc i hi) fun h => by rw [hS] at h; omega)
      (by simp only [OutW, pageTableWindows, and_true]; omega)
  have R := A.refs
  have refs6 : RefTablesPre H d6.σ.mem t1 t2 t3 := {
    R with
    ptr1 := by rw [domainWord 104 (by decide)]; exact R.ptr1
    ptr2 := by rw [domainWord 112 (by decide)]; exact R.ptr2
    ptr3 := by rw [domainWord 120 (by decide)]; exact R.ptr3
    empty1 := by rw [heapWord t1 R.spot1 R.owned1]; exact R.empty1
    empty2 := by rw [heapWord t2 R.spot2 R.owned2]; exact R.empty2
    empty3 := by rw [heapWord t3 R.spot3 R.owned3]; exact R.empty3 }
  have fits : blk.toNat + 16384 ≤ 2 ^ 64 := by omega
  -- caml_set_minor_heap_size(0x200000)
  obtain ⟨raw, d7, run7, M⟩ := minor_heap_set d6 ((blk.toNat, 16384) :: H) (cap + c2 + c1 + cA) cM (nativeStack sp 96)
    jal_8001f36c_call.link 0x200000#64 0xf8000#64 262144#64 8192#64 2#64 blk t1 t2 t3 512 {
      pc := by rw [← jal_8001f36c_call_target]; exact C.pc
      regs := ⟨C.ready.stack, C.ready.raReg, C.regs.1,
        g46.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ T.regs rfl),
        g46.get (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ T.regs rfl),
        g46.get (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ T.regs rfl),
        g46.get (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ T.regs rfl), trivial⟩
      ready := C.ready
      frame := frameIn
      sizeAt := by decide
      pages := by decide
      halfFull := by decide
      charged := A.chargedM
      idle := by rw [domainWord 8 (by decide), domainWord 56 (by decide)]; exact A.idle
      noYoung := by rw [domainWord 32 (by decide)]; exact A.noYoung
      domainOwned := List.mem_cons_of_mem _ domainOwned
      table := by rw [mem6]; exact T.table
      tableLow := by rw [hE]; exact bHigh
      tableHigh := by rw [hS]; exact bLow
      tableOwned := by simp
      tableWindows := fun i hi => by
        have n := slotAddr_nat blk i hi fits
        exact window_of_heap (by rw [n, hS]; omega) (by rw [n, hE]; omega) (by rw [n]; have := T.aligned; omega)
      tableDomain := by
        have a := FreshBlock.apart T.fresh domainOwned (by decide) (by decide)
        exact a
      refs := refs6.at T.fresh
      lambdaOff := by
        rw [word_observed (m := c.σ.mem) _ (lowAgree _ (by decide) (fun i hi => by unfold allocGlobal InRange; omega)
          (by rw [hP]; decide))]
        exact A.lambdaOff
      memprofIdle := by
        rw [read8_agree (lowAgree _ (by decide) (fun i hi => by unfold allocGlobal InRange; omega) (by rw [hP]; decide))]
        exact A.memprofIdle }
  have saved7 (k : Nat) (lo : 20 ≤ k) (hi : k ≤ 27) {v : BitVec 64} (h : gprGet d4.σ k = some v) : gprGet d7.σ k = some v := by
    rw [M.saved k lo hi]; exact g46.get (by omega) (by omega) (by simp; omega) h
  have stackNat : (nativeStack sp 96).toNat = sp.toNat - 96 := frame96.stack_nat
  refine ⟨raw, d7, run5.trans (run6.trans run7), {
    pc := M.pc
    regs := ⟨gholds_lookup (n := 2) _ M.regs rfl, gholds_lookup (n := 10) _ M.regs rfl,
      gholds_lookup (n := 8) _ M.regs rfl, gholds_lookup (n := 9) _ M.regs rfl, gholds_lookup (n := 18) _ M.regs rfl,
      gholds_lookup (n := 19) _ M.regs rfl,
      saved7 20 (by decide) (by decide) (gholds_lookup (n := 20) _ T.regs rfl),
      saved7 21 (by decide) (by decide) (gholds_lookup (n := 21) _ T.regs rfl),
      saved7 22 (by decide) (by decide) (gholds_lookup (n := 22) _ T.regs rfl),
      saved7 23 (by decide) (by decide) (gholds_lookup (n := 23) _ T.regs rfl),
      saved7 24 (by decide) (by decide) (gholds_lookup (n := 24) _ T.regs rfl),
      saved7 25 (by decide) (by decide) (gholds_lookup (n := 25) _ T.regs rfl), trivial⟩
    ready := M.ready
    tableFresh := T.fresh
    tableAligned := T.aligned
    minorFresh := M.fresh
    young := M.young
    table := M.table
    count := M.count
    only := M.only
    slots := fun off value member => by
      have bound : off + 8 ≤ 96 := by simp [initGcSlots] at member; omega
      rw [word_observed (m := d6.σ.mem) _ fun i hi => M.caller _ (by rw [stackNat]; unfold nativeFrameBase; omega), mem6]
      exact T.slots off value member
    lowKept := fun x low alloc rec trig => by
      rw [M.lowKept x low alloc (by rw [hP] at rec ⊢; omega) trig]
      exact back x (by rw [hS] at low; rw [hE]; omega) (fun f => f.elim alloc fun h => by omega)
        (by simp only [OutW, pageTableWindows, and_true]; exact rec)
    domainHigh := fun off lo hi => by rw [M.domainHigh off lo hi, domainWord off hi] }⟩

end OCaml.Vm.Boot.Startup
