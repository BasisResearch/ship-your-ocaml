import OCaml.Vm.Boot.Startup.InitGcSteps
import OCaml.Vm.Boot.Startup.GcMessageReady
import OCaml.Vm.Boot.Startup.PageTable
import OCaml.Vm.Gc.ReadyCalls
import OCaml.Vm.Boot.Startup.PageApart
import OCaml.Vm.Boot.Startup.StatAligned
import OCaml.Vm.Boot.Startup.PolicySteps
import Vsa.Sim.FrameComposition
import OCaml.Vm.Boot.Startup.MemSame
import OCaml.Vm.Boot.Startup.CallerFrame

/-! caml_init_gc, composed with its callees, at the default parameters. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  OCaml.Vm.Gc LeanRV64DExecutable

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
  lastExn : bytesT c.σ.mem (domainField backtrace_last_exnOffset) 8 = 1#64
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
  caller : CallerFrame sp before after
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
    caller := ⟨fun x hx => by
      rw [PT.caller x (by rw [frame96.stack_nat]; unfold nativeFrameBase; omega), C.memory, p2.memory,
        show writeLog d1.σ.mem [] = d1.σ.mem from rfl]
      exact above x hx⟩
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
  caller : CallerFrame sp before after
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
    caller := ⟨fun x hx => by
      rw [M.caller x (by rw [stackNat]; omega), mem6]
      exact T.caller.byte x hx⟩
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

/-- A minor-heap page in the table names a page of the minor heap's block. -/
theorem minor_slot_inBlock {H : List (Nat × Nat)} {raw w : BitVec 64} {j : Nat} (hj : j < 512)
    (fits : raw.toNat + (4096 * 512 + 4096) ≤ 0x86800000)
    (owned : (raw.toNat, (0x200000#64 + 4096#64).toNat) ∈ H) (eq : w = 2#64 ||| blockPage (pageAbove raw) j) :
    SlotInBlock H w := by
  obtain ⟨lo, hi, al⟩ := pageAbove_inside raw (4096 * 512) (by omega)
  have page : (blockPage (pageAbove raw) j).toNat = (pageAbove raw).toNat + 4096 * j := by
    unfold blockPage
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Nat.reducePow]
    rw [Nat.mod_eq_of_lt (a := 4096 * j) (by omega), Nat.mod_eq_of_lt (by omega)]
  have size : (0x200000#64 + 4096#64).toNat = 4096 * 512 + 4096 := by decide
  exact ⟨2#64, blockPage (pageAbove raw) j, (raw.toNat, (0x200000#64 + 4096#64).toNat), {
    owned := owned
    inBlock := by unfold InExt; dsimp only; rw [page, size]; omega
    aligned := by rw [page]; omega
    small := by decide
    word := eq }⟩

/-- The parameters, the policy and `caml_verb_gc` are apart from caml_init_major_heap's writes. -/
theorem initLow_out (x : Nat) (h : (0x80064848 ≤ x ∧ x < 0x80064850) ∨ (0x80064930 ≤ x ∧ x < 0x80064938) ∨
    (0x80064ad8 ≤ x ∧ x < 0x80064ae0) ∨ (0x80064af0 ≤ x ∧ x < 0x80064af8) ∨ (0x80064c60 ≤ x ∧ x < 0x80064c68)) :
    OutW majorInitLowWindows x := by
  unfold majorInitLowWindows majorFreeWindows
  simp only [outW_append, majorLowWindows, OutW, heapStartAddr, pageTable, Layout.sym_caml_page_table, smallListsWindow, flMergeAddr, smallMapAddr,
    largeTreeAddr, flCurWszAddr, gcPhaseAddr, extraResourcesAddr, allocatedWordsAddr, majorRingWindow, BitVec.toNat_ofNat,
    majorRingAddr, and_true]
  omega

/-- The live list after the minor heap. -/
abbrev initGcH2 (H : List (Nat × Nat)) (blk raw : BitVec 64) : List (Nat × Nat) :=
  (raw.toNat, (0x200000#64 + 4096#64).toNat) :: (blk.toNat, 16384) :: H

/-- The GC parameters caml_init_gc stores after the major heap. -/
def gcStoreWindows : List W :=
  [⟨majorWindowAddr, majorWindowAddr + 4⟩, ⟨customMajorAddr, customMajorAddr + 8⟩,
    ⟨customMinorAddr, customMinorAddr + 8⟩, ⟨customMaxAddr, customMaxAddr + 8⟩]

/-- A low global caml_init_gc leaves alone: below the arena, outside the
allocator's globals, the page table header, memprof's young trigger, the
parameter and policy stores, caml_init_major_heap's globals and the final
parameter stores. -/
structure GcLowKeep (x : Nat) : Prop where
  low : x < heapStart
  notAlloc : ¬ allocGlobal x
  table : x < pageTable ∨ pageTable + 0x28 ≤ x
  trigger : x < 0x80064cc8 ∨ 0x80064cc8 + 8 ≤ x
  policy : OutL policyLog x
  percent : OutL [(percentFreeAddr, 8, 120#64), (percentMaxAddr, 8, 500#64)] x
  increment : OutL [(majorIncrementAddr, 8, 15#64)] x
  major : OutW majorInitLowWindows x
  stores : OutW gcStoreWindows x

/-- caml_init_gc's parameter words, `caml_verb_gc` and `Caml_state` are among
the low globals it keeps. -/
theorem GcLowKeep.of_range {x : Nat} (h : (0x800647f0 ≤ x ∧ x < 0x80064848) ∨ (0x80064930 ≤ x ∧ x < 0x80064938) ∨
    (Layout.sym_Caml_state ≤ x ∧ x < Layout.sym_Caml_state + 8)) : GcLowKeep x := by
  unfold Layout.sym_Caml_state at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold heapStart; omega
  · unfold allocGlobal InRange; omega
  · unfold pageTable Layout.sym_caml_page_table; omega
  · omega
  · simp only [policyLog, OutL, and_true]; omega
  · simp only [OutL, percentFreeAddr, percentMaxAddr, and_true]; omega
  · simp only [OutL, majorIncrementAddr, and_true]; omega
  · unfold majorInitLowWindows majorFreeWindows
    simp only [outW_append, majorLowWindows, OutW, heapStartAddr, pageTable, Layout.sym_caml_page_table,
      smallListsWindow, flMergeAddr, smallMapAddr, largeTreeAddr, flCurWszAddr, gcPhaseAddr, extraResourcesAddr,
      allocatedWordsAddr, majorRingWindow, BitVec.toNat_ofNat, majorRingAddr, and_true]
    omega
  · simp only [gcStoreWindows, OutW, majorWindowAddr, customMajorAddr, customMinorAddr, customMaxAddr, and_true]
    omega

/-- caml_init_major_heap returned into caml_init_gc. -/
structure InitGcMajored (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 blk raw : BitVec 64)
    (mem stack entries cur : BitVec 64) (before after : Config) : Prop where
  caller : CallerFrame sp before after
  lastExn : bytesT after.σ.mem (domainField backtrace_last_exnOffset) 8 = 1#64
  pc : PCAt jal_8001f3a4_call.link after
  regs : GHolds after.σ [(2, nativeStack sp 96), (8, 0xf8000#64), (9, BitVec.ofNat 64 percentFreeAddr), (18, 8192#64),
    (19, BitVec.ofNat 64 percentMaxAddr), (20, 15#64), (21, 120#64), (22, 500#64), (23, 1#64), (24, 44#64),
    (25, 100#64)]
  ready : RuntimeReady ((entries.toNat, (32768#64).toNat) :: (stack.toNat, (24#64).toNat) ::
    (mem.toNat, (majorChunkSize 0xf8000#64 + 4152#64).toNat) :: initGcH2 H blk raw) capacity (nativeStack sp 96)
    jal_8001f3a4_call.link after
  major : ∃ mid, MajorHeapInit (initGcH2 H blk raw) capacity (nativeStack sp 96) jal_8001f3a4_call.link 0xf8000#64
    0xf8000#64 (BitVec.ofNat 64 percentFreeAddr) 8192#64 mem stack entries cur blk mid after
  minorFresh : FreshBlock vsaLayoutP ((blk.toNat, 16384) :: H) raw.toNat (0x200000#64 + 4096#64).toNat
  tableFresh : FreshBlock vsaLayoutP H blk.toNat 16384
  slots : ∀ off value, (off, value) ∈ initGcSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 →
    bytesT after.σ.mem (nativeFrameBase sp 96 + off) 8 = value
  incrWord : bytesT after.σ.mem majorIncrementAddr 8 = 15#64
  freeWord : bytesT after.σ.mem percentFreeAddr 8 = 120#64
  maxWord : bytesT after.σ.mem percentMaxAddr 8 = 500#64
  policyWord : bytesT after.σ.mem allocationPolicyAddr 8 = 2#64
  quiet : LPins8 after.σ.mem Layout.sym_caml_verb_gc (List.replicate 8 0#8)
  /-- Low globals outside caml_init_gc's stores are kept from its entry. -/
  low : ∀ x, GcLowKeep x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  /-- The page table over the live list. -/
  table : MajorTableAt ((entries.toNat, (32768#64).toNat) :: (stack.toNat, (24#64).toNat) ::
    (mem.toNat, (majorChunkSize 0xf8000#64 + 4152#64).toNat) :: initGcH2 H blk raw) after.σ.mem blk
  /-- The minor heap's 512 pages and the major chunk's. -/
  count : pageCount after.σ.mem blk.toNat = 512 + majorPages 0xf8000#64

theorem init_gc_to_major (c d7 : Config) (H : List (Nat × Nat)) (cap c1 c2 cA cM cP : Nat)
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur blk raw : BitVec 64)
    (A : InitGcCall H cap c1 c2 cA cM cP sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur c)
    (Mi : InitGcMinored H (cap + c2 + c1 + cA) sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 blk raw c d7) :
    ∃ mem stack entries after, Steps d7 after ∧
      InitGcMajored H cap sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 blk raw mem stack entries cur c after := by
  have frame96 : NativeFrame sp 96 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have frameIn : NativeFrame (nativeStack sp 96) (64 + (32 + allocHeadroom)) := A.frame.nested (front := 96) (by decide)
  have hS : heapStart = 0x8007d140 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  have hP : pageTable = 0x800684b8 := rfl
  have dom : firstDomainPtr.toNat = 0x8007d150 := rfl
  have regs7 := Mi.regs
  -- caml_major_heap_increment = 15
  obtain ⟨d8, run8, p8⟩ := (init_gc_increment d7 jal_8001f36c_call.link Mi.ready.toLeafInput
    ⟨gholds_lookup (n := 20) _ regs7 rfl, gholds_lookup (n := 21) _ regs7 rfl, gholds_lookup (n := 10) _ regs7 rfl,
      trivial⟩).run d7 ⟨Mi.pc, rfl⟩
  have g8 := GprsSame.of_post p8 (by decide)
  have incrW := globalWindow_ok (H := initGcH2 H blk raw) (lo := majorIncrementAddr) (hi := majorIncrementAddr + 8)
    (by decide) (by decide) (by decide) (fun a lo hi => by unfold majorIncrementAddr at lo hi; unfold allocGlobal InRange; omega)
    (by decide) (by decide)
  have ready8 := Mi.ready.window_log p8 (by decide) (by simp only [keysG]; decide) (by decide)
    (g8.get (by decide) (by decide) (by decide) Mi.ready.stack) (g8.get (by decide) (by decide) (by decide) Mi.ready.raReg)
    (by decide) (by simp only [LogInW, InsideW, majorIncrementAddr]; decide) incrW.pins incrW.domain incrW.pool incrW.heap
  -- caml_percent_free = 120, caml_percent_max = 500
  obtain ⟨d9, run9, p9⟩ := (init_gc_percent d8 jal_8001f36c_call.link ready8.toLeafInput
    ⟨g8.get (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ regs7 rfl), gholds_lookup (n := 15) _ p8.regs rfl,
      gholds_lookup (n := 9) _ p8.regs rfl, g8.get (by decide) (by decide) (by decide) (gholds_lookup (n := 22) _ regs7 rfl),
      trivial⟩).run d8 ⟨p8.pc, rfl⟩
  have g9 := GprsSame.of_post p9 (by decide)
  have freeW := globalWindow_ok (H := initGcH2 H blk raw) (lo := percentFreeAddr) (hi := percentFreeAddr + 8)
    (by decide) (by decide) (by decide) (fun a lo hi => by unfold percentFreeAddr at lo hi; unfold allocGlobal InRange; omega)
    (by decide) (by decide)
  have maxW := globalWindow_ok (H := initGcH2 H blk raw) (lo := percentMaxAddr) (hi := percentMaxAddr + 8)
    (by decide) (by decide) (by decide) (fun a lo hi => by unfold percentMaxAddr at lo hi; unfold allocGlobal InRange; omega)
    (by decide) (by decide)
  have pW := freeW.cons maxW
  have ready9 := ready8.window_log p9 (by decide) (by simp only [keysG]; decide) (by decide)
    (g9.get (by decide) (by decide) (by decide) ready8.stack) (g9.get (by decide) (by decide) (by decide) ready8.raReg)
    (by decide) (by simp only [LogInW, InsideW, percentFreeAddr, percentMaxAddr]; decide) pW.pins pW.domain pW.pool pW.heap
  -- caml_set_allocation_policy(2)
  obtain ⟨d10, run10, C10⟩ := (ready_call jal_8001f39c_call_shape jal_8001f39c_call_decode (jal_8001f39c_call_pins p9.image)
    ready9 [(10, 2#64)] ⟨gholds_lookup (n := 10) _ p9.regs rfl, trivial⟩
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) _ rfl (by decide)).run d9 ⟨p9.pc, rfl⟩
  obtain ⟨d11, run11, P11⟩ := set_allocation_policy d10 (initGcH2 H blk raw) _ (nativeStack sp 96) jal_8001f39c_call.link
    (by rw [← jal_8001f39c_call_target]; exact C10.pc) C10.ready C10.regs.1
  have g10 : GprsSame d9 d10 [1] := ⟨fun n lo hi out => C10.frame n lo hi (by simpa using out)⟩
  have g11 := GprsSame.of_saved P11.saved
  have g711 := ((g8.trans g9).trans g10).trans g11
  -- caml_init_major_heap(Bsize_wsize(major))
  obtain ⟨d12, run12, p12⟩ := (init_gc_major_front d11 jal_8001f39c_call.link 0xf8000#64 (vsaReg d11 10)
    P11.ready.toLeafInput ⟨g711.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ regs7 rfl),
      OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready P11.ready 10 (by decide) (by decide), trivial⟩).run d11 ⟨P11.pc, rfl⟩
  have g12 := GprsSame.of_post p12 (by decide)
  have ready12 := P11.ready.stack_log p12 (by decide) (by simp only [keysG]; decide) (by decide)
    (g12.get (by decide) (by decide) (by decide) P11.ready.stack) (g12.get (by decide) (by decide) (by decide) P11.ready.raReg)
    (by decide) frameIn (by simp only [LogInW])
  obtain ⟨d13, run13, C13⟩ := (ready_call jal_8001f3a4_call_shape jal_8001f3a4_call_decode (jal_8001f3a4_call_pins p12.image)
    ready12 [(10, 0xf8000#64)] ⟨gholds_lookup (n := 10) _ p12.regs rfl, trivial⟩
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) _ rfl (by decide)).run d12 ⟨p12.pc, rfl⟩
  have g13 : GprsSame d12 d13 [1] := ⟨fun n lo hi out => C13.frame n lo hi (by simpa using out)⟩
  have g713 := (g711.trans g12).trans g13
  -- d13's memory: three logs over the minor heap's return
  have back13 (x : Nat) (o1 : OutL policyLog x) (o2 : OutL [(percentFreeAddr, 8, 120#64), (percentMaxAddr, 8, 500#64)] x)
      (o3 : OutL [(majorIncrementAddr, 8, 15#64)] x) : (d13.σ.mem[x]?).getD 0 = (d7.σ.mem[x]?).getD 0 := by
    rw [C13.memory, p12.memory, show writeLog d11.σ.mem [] = d11.σ.mem from rfl, P11.memory, writeLog_out _ _ _ o1,
      C10.memory, p9.memory, writeLog_out _ _ _ o2, p8.memory, writeLog_out _ _ _ o3]
  have mem13 : d13.σ.mem = writeLog (writeLog (writeLog d7.σ.mem [(majorIncrementAddr, 8, 15#64)])
      [(percentFreeAddr, 8, 120#64), (percentMaxAddr, 8, 500#64)]) policyLog := by
    rw [C13.memory, p12.memory, show writeLog d11.σ.mem [] = d11.σ.mem from rfl, P11.memory, C10.memory, p9.memory,
      p8.memory]
  -- a low global the parameters, the policy and the minor heap leave alone
  have glob (x : Nat) (low : x < 0x8007d140) (alloc : ¬ allocGlobal x) (rec : x < pageTable ∨ pageTable + 0x28 ≤ x)
      (trig : x < 0x80064cc8 ∨ 0x80064cc8 + 8 ≤ x) (o1 : OutL policyLog x)
      (o2 : OutL [(percentFreeAddr, 8, 120#64), (percentMaxAddr, 8, 500#64)] x)
      (o3 : OutL [(majorIncrementAddr, 8, 15#64)] x) : (d13.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [back13 x o1 o2 o3, Mi.lowKept x (by rw [hS]; exact low) alloc rec trig]
  have globWord (a : Nat) (low : a + 8 ≤ 0x80064848) (alloc : ∀ i, i < 8 → ¬ allocGlobal (a + i)) :
      ∀ i, i < 8 → (d13.σ.mem[a + i]?).getD 0 = (c.σ.mem[a + i]?).getD 0 := fun i hi =>
    glob _ (by omega) (alloc i hi) (by rw [hP]; omega) (by omega)
      (by simp only [OutL, policyLog, and_true]; omega)
      (by simp only [OutL, percentFreeAddr, percentMaxAddr, and_true]; omega)
      (by simp only [OutL, majorIncrementAddr, and_true]; omega)
  have globWord2 (a : Nat) (low : 0x800649f0 ≤ a) (high : a + 8 ≤ 0x80064ad8 ∨ (0x80064ae0 ≤ a ∧ a + 8 ≤ 0x80064af0) ∨
        (0x80064af8 ≤ a ∧ a + 8 ≤ 0x80064c60) ∨ (0x80064c68 ≤ a ∧ a + 8 ≤ 0x80064cc8) ∨ (0x80064cd0 ≤ a ∧ a + 8 ≤ 0x800684b8))
      (alloc : ∀ i, i < 8 → ¬ allocGlobal (a + i)) :
      ∀ i, i < 8 → (d13.σ.mem[a + i]?).getD 0 = (c.σ.mem[a + i]?).getD 0 := fun i hi =>
    glob _ (by omega) (alloc i hi) (by rw [hP]; omega) (by omega)
      (by simp only [OutL, policyLog, and_true]; omega)
      (by simp only [OutL, percentFreeAddr, percentMaxAddr, and_true]; omega)
      (by simp only [OutL, majorIncrementAddr, and_true]; omega)
  have bLow : 0x8007d140 ≤ blk.toNat := Mi.tableFresh.2.1
  have bHigh : blk.toNat + 16384 ≤ 0x86800000 := Mi.tableFresh.2.2.1
  have fits : blk.toNat + 16384 ≤ 2 ^ 64 := by omega
  have tblSame (x : Nat) (h : InTable blk x) : (d13.σ.mem[x]?).getD 0 = (d7.σ.mem[x]?).getD 0 := by
    have hx : 0x800684b8 ≤ x := by
      rcases h with ⟨lo, _⟩ | ⟨lo, _⟩
      · rw [hP] at lo; omega
      · omega
    exact back13 x (by simp only [OutL, policyLog, and_true]; omega)
      (by simp only [OutL, percentFreeAddr, percentMaxAddr, and_true]; omega)
      (by simp only [OutL, majorIncrementAddr, and_true]; omega)
  have congr : pageCount d13.σ.mem blk.toNat = pageCount d7.σ.mem blk.toNat := pageCount_congr fun i hi => by
    rw [← slotWord_pageSlot _ _ i hi fits, ← slotWord_pageSlot _ _ i hi fits]
    exact slotWord_window_agree fits tblSame i hi
  have count13 : pageCount d13.σ.mem blk.toNat = 512 := by rw [congr]; exact Mi.count
  have incr13 : bytesT d13.σ.mem majorIncrementAddr 8 = 15#64 := by
    rw [mem13, bytesT_writeLog_out _ (by simp only [policyLog, OutLRange, majorIncrementAddr, and_true]; decide),
      bytesT_writeLog_out _ (by simp only [OutLRange, percentFreeAddr, percentMaxAddr, majorIncrementAddr, and_true]; decide)]
    exact word_writeLog_at _ _ 0 _ _ rfl trivial
  have mFits : raw.toNat + (4096 * 512 + 4096) ≤ 0x86800000 := by
    have := Mi.minorFresh.2.2.1
    rw [show (0x200000#64 + 4096#64).toNat = 4096 * 512 + 4096 by decide] at this
    exact this
  obtain ⟨mem, stack, entries, d14, run14, MH⟩ := caml_init_major_heap d13 (initGcH2 H blk raw) cap c1 c2 cA
    (nativeStack sp 96) jal_8001f3a4_call.link 0xf8000#64 0xf8000#64 (BitVec.ofNat 64 percentFreeAddr) 8192#64
    (BitVec.ofNat 64 percentMaxAddr) 15#64 120#64 500#64 1#64 44#64 15#64 blk cur {
      pc := by rw [← jal_8001f3a4_call_target]; exact C13.pc
      regs := ⟨C13.ready.stack, C13.ready.raReg, C13.regs.1,
        g713.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ regs7 rfl),
        (((g10.trans g11).trans g12).trans g13).get (by decide) (by decide) (by decide)
          (g9.get (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ p8.regs rfl)),
        g713.get (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ regs7 rfl), trivial⟩
      ready := C13.ready
      frame := frameIn.resize (by unfold allocHeadroom; omega) (by decide)
      domainOwned := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ A.domainOwned)
      increment := incr13
      percent := by decide
      noHeap := by
        rw [word_observed (m := d7.σ.mem) _ fun i hi => back13 _
          (by simp only [OutL, policyLog, domainField, dom, and_true]; omega)
          (by simp only [OutL, percentFreeAddr, percentMaxAddr, domainField, dom, and_true]; omega)
          (by simp only [OutL, majorIncrementAddr, domainField, dom, and_true]; omega),
          Mi.domainHigh 336 (by decide) (by decide)]
        exact A.noHeap
      lastExn := by
        rw [word_observed (m := d7.σ.mem) _ fun i hi => back13 _
          (by simp only [OutL, policyLog, domainField, backtrace_last_exnOffset, dom, and_true]; omega)
          (by simp only [OutL, percentFreeAddr, percentMaxAddr, domainField, backtrace_last_exnOffset, dom, and_true]; omega)
          (by simp only [OutL, majorIncrementAddr, domainField, backtrace_last_exnOffset, dom, and_true]; omega),
          Mi.domainHigh backtrace_last_exnOffset (by decide) (by decide)]
        exact A.lastExn
      chunkMin := by decide
      huge := by
        rw [word_observed (m := c.σ.mem) _ (globWord2 _ (by decide) (by decide)
          (fun i hi => by unfold allocGlobal InRange; omega))]
        exact A.huge
      charged := A.chargedA
      small := by decide
      request := by decide }
    {
      fields := by rw [count13]; exact Mi.table.window_agree tblSame
      low := by rw [hE]; exact bHigh
      high := by rw [hS]; exact bLow
      owned := by simp
      windows := fun i hi => by
        have n := slotAddr_nat blk i hi fits
        exact window_of_heap (by rw [n, hS]; omega) (by rw [n, hE]; omega) (by rw [n]; have := Mi.tableAligned; omega)
      apartDomain := FreshBlock.apart Mi.tableFresh A.domainOwned (by decide) (by decide)
      occupied := fun i hi occ => by
        rw [slotWord_window_agree fits tblSame i hi] at occ ⊢
        obtain ⟨j, hj, eq⟩ := Mi.only i hi occ
        exact minor_slot_inBlock hj mFits (by simp) eq }
    ((((g10.trans g11).trans g12).trans g13).get (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ p9.regs rfl))
    (by rw [count13]; decide)
    {
      initMerge := by
        rw [mem13]
        exact word_writeLog_at _ _ 4 _ _ rfl (by simp only [policyLog, List.drop, OutLRange, and_true]; decide)
      makeFree := by rw [mem13]; exact word_writeLog_at _ _ 7 _ _ rfl trivial
      lists := fun j hj => by
        have n0 := smallList_nat j hj 0 (by decide)
        rw [BitVec.add_zero] at n0
        rw [n0, word_observed (m := c.σ.mem) _ (globWord2 _ (by omega) (by omega)
          (fun i hi => by unfold allocGlobal InRange; omega)), ← n0]
        exact A.lists j hj
      tree := by
        rw [word_observed (m := c.σ.mem) _ (globWord2 _ (by decide) (by decide)
          (fun i hi => by unfold largeTreeAddr allocGlobal InRange; omega))]
        exact A.tree
      least := by
        rw [word_observed (m := c.σ.mem) _ (globWord2 _ (by decide) (by decide)
          (fun i hi => by unfold largeLeastAddr allocGlobal InRange; omega))]
        exact A.least
      curWsz := by
        rw [word_observed (m := c.σ.mem) _ (globWord2 _ (by decide) (by decide)
          (fun i hi => by unfold flCurWszAddr allocGlobal InRange; omega))]
        exact A.curWsz }
    ⟨g713.get (by decide) (by decide) (by decide) (gholds_lookup (n := 20) _ regs7 rfl),
      g713.get (by decide) (by decide) (by decide) (gholds_lookup (n := 21) _ regs7 rfl),
      g713.get (by decide) (by decide) (by decide) (gholds_lookup (n := 22) _ regs7 rfl),
      g713.get (by decide) (by decide) (by decide) (gholds_lookup (n := 23) _ regs7 rfl),
      g713.get (by decide) (by decide) (by decide) (gholds_lookup (n := 24) _ regs7 rfl), trivial⟩
    A.charged1 A.charged2
  have stack96 : (nativeStack sp 96).toNat = sp.toNat - 96 := frame96.stack_nat
  have f96 := frame96.lower
  rw [hE] at f96
  have fromMajor (a : Nat) (hlow : a + 8 ≤ 0x8007d140) (alloc : ∀ i, i < 8 → ¬ allocGlobal (a + i))
      (out : ∀ i, i < 8 → OutW majorInitLowWindows (a + i)) :
      bytesT d14.σ.mem a 8 = bytesT d13.σ.mem a 8 :=
    word_observed _ fun i hi => MH.lowKept _ (by rw [hS]; omega) (alloc i hi) (out i hi)
  have free13 : bytesT d13.σ.mem percentFreeAddr 8 = 120#64 := by
    rw [mem13, bytesT_writeLog_out _ (by simp only [policyLog, OutLRange, percentFreeAddr, and_true]; decide)]
    exact word_writeLog_at _ _ 0 _ _ rfl (by simp only [List.drop, OutLRange, percentFreeAddr, percentMaxAddr, and_true]; decide)
  have max13 : bytesT d13.σ.mem percentMaxAddr 8 = 500#64 := by
    rw [mem13, bytesT_writeLog_out _ (by simp only [policyLog, OutLRange, percentMaxAddr, and_true]; decide)]
    exact word_writeLog_at _ _ 1 _ _ rfl trivial
  have policy13 : bytesT d13.σ.mem allocationPolicyAddr 8 = 2#64 := by
    rw [mem13]
    exact word_writeLog_at _ _ 0 _ _ rfl (by simp only [policyLog, List.drop, OutLRange, allocationPolicyAddr, and_true]; decide)
  have s19 : gprGet d13.σ 19 = some (BitVec.ofNat 64 percentMaxAddr) :=
    (((g10.trans g11).trans g12).trans g13).get (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ p9.regs rfl)
  have saved14 (k : Nat) (lo : 20 ≤ k) (hi : k ≤ 27) {v : BitVec 64} (h : gprGet d7.σ k = some v) : gprGet d14.σ k = some v := by
    rw [MH.saved k lo hi]; exact g713.get (by omega) (by omega) (by simp [abiClobbered]; omega) h
  refine ⟨mem, stack, entries, d14,
    run8.trans (run9.trans (run10.trans (run11.trans (run12.trans (run13.trans run14))))), {
    caller := ⟨fun x hx => by
      rw [MH.caller x (by rw [stack96]; omega)]
      have high := frame96.lower
      rw [hE] at high
      rw [back13 x
        (by simp only [OutL, policyLog, and_true]; omega)
        (by simp only [OutL, percentFreeAddr, percentMaxAddr, and_true]; omega)
        (by simp only [OutL, majorIncrementAddr, and_true]; omega)]
      exact Mi.caller.byte x hx⟩
    lastExn := MH.lastExn
    pc := MH.pc
    regs := ⟨gholds_lookup (n := 2) _ MH.regs rfl, gholds_lookup (n := 8) _ MH.regs rfl,
      gholds_lookup (n := 9) _ MH.regs rfl, gholds_lookup (n := 18) _ MH.regs rfl, by rw [MH.s3]; exact s19,
      saved14 20 (by decide) (by decide) (gholds_lookup (n := 20) _ regs7 rfl),
      saved14 21 (by decide) (by decide) (gholds_lookup (n := 21) _ regs7 rfl),
      saved14 22 (by decide) (by decide) (gholds_lookup (n := 22) _ regs7 rfl),
      saved14 23 (by decide) (by decide) (gholds_lookup (n := 23) _ regs7 rfl),
      saved14 24 (by decide) (by decide) (gholds_lookup (n := 24) _ regs7 rfl),
      saved14 25 (by decide) (by decide) (gholds_lookup (n := 25) _ regs7 rfl), trivial⟩
    ready := MH.ready
    major := ⟨d13, MH⟩
    minorFresh := Mi.minorFresh
    tableFresh := Mi.tableFresh
    slots := fun off value member => by
      have bound : off + 8 ≤ 96 := by simp [initGcSlots] at member; omega
      rw [word_observed (m := d7.σ.mem) _ fun i hi => by
        rw [MH.caller _ (by rw [stack96]; unfold nativeFrameBase; omega)]
        exact back13 _ (by simp only [OutL, policyLog, and_true]; unfold nativeFrameBase; omega)
          (by simp only [OutL, percentFreeAddr, percentMaxAddr, and_true]; unfold nativeFrameBase; omega)
          (by simp only [OutL, majorIncrementAddr, and_true]; unfold nativeFrameBase; omega)]
      exact Mi.slots off value member
    incrWord := by
      rw [fromMajor _ (by decide) (fun i hi => by unfold majorIncrementAddr allocGlobal InRange; omega)
        (fun i hi => initLow_out _ (by unfold majorIncrementAddr; omega))]
      exact incr13
    freeWord := by
      rw [fromMajor _ (by decide) (fun i hi => by unfold percentFreeAddr allocGlobal InRange; omega)
        (fun i hi => initLow_out _ (by unfold percentFreeAddr; omega))]
      exact free13
    maxWord := by
      rw [fromMajor _ (by decide) (fun i hi => by unfold percentMaxAddr allocGlobal InRange; omega)
        (fun i hi => initLow_out _ (by unfold percentMaxAddr; omega))]
      exact max13
    policyWord := by
      rw [fromMajor _ (by decide) (fun i hi => by unfold allocationPolicyAddr allocGlobal InRange; omega)
        (fun i hi => initLow_out _ (by unfold allocationPolicyAddr; omega))]
      exact policy13
    quiet := lpins8_observed A.quiet fun i hi => by
      rw [MH.lowKept _ (by rw [hS]; unfold Layout.sym_caml_verb_gc; omega)
        (by unfold Layout.sym_caml_verb_gc allocGlobal InRange; omega)
        (initLow_out _ (by unfold Layout.sym_caml_verb_gc; omega))]
      exact glob _ (by unfold Layout.sym_caml_verb_gc; omega) (by unfold Layout.sym_caml_verb_gc allocGlobal InRange; omega)
        (by rw [hP]; unfold Layout.sym_caml_verb_gc; omega) (by unfold Layout.sym_caml_verb_gc; omega)
        (by simp only [OutL, policyLog, Layout.sym_caml_verb_gc, and_true]; omega)
        (by simp only [OutL, percentFreeAddr, percentMaxAddr, Layout.sym_caml_verb_gc, and_true]; omega)
        (by simp only [OutL, majorIncrementAddr, Layout.sym_caml_verb_gc, and_true]; omega)
    low := fun x k => by
      rw [MH.lowKept x k.low k.notAlloc k.major]
      exact glob x k.low k.notAlloc k.table k.trigger k.policy k.percent k.increment
    table := MH.table
    count := by rw [MH.count, count13] }⟩

/-- Bytes the end of caml_init_gc leaves alone: low memory outside the stored
parameters, and the caller's side of caml_init_gc's frame pointer. -/
def GcTailKeep (fsp : BitVec 64) (x : Nat) : Prop := (x < heapEnd ∧ OutW gcStoreWindows x) ∨ fsp.toNat ≤ x

theorem MemSame.chain {c d e : Config} {K : Nat → Prop} (a : MemSame c d K) (b : MemSame d e K) : MemSame c e K :=
  (a.trans b).mono fun _ h => ⟨h, h⟩

/-- The page table caml_init_gc leaves: the live-list invariant and its occupancy. -/
structure GcTableAt (H : List (Nat × Nat)) (m : Std.ExtHashMap Nat (BitVec 8)) (ent : BitVec 64) : Prop where
  table : MajorTableAt H m ent
  count : pageCount m ent.toNat = 512 + majorPages 0xf8000#64

theorem GcTableAt.agree {H : List (Nat × Nat)} {m m' : Std.ExtHashMap Nat (BitVec 8)} {ent : BitVec 64}
    (T : GcTableAt H m ent) (same : ∀ x, InTable ent x → (m'[x]?).getD 0 = (m[x]?).getD 0) : GcTableAt H m' ent :=
  ⟨T.table.agree same, by rw [pageCount_agree (Nat.le_trans T.table.low (by decide)) same]; exact T.count⟩

theorem GcTableAt.cons {H : List (Nat × Nat)} {m : Std.ExtHashMap Nat (BitVec 8)} {ent : BitVec 64}
    (T : GcTableAt H m ent) (e : Nat × Nat) : GcTableAt (e :: H) m ent :=
  ⟨T.table.cons e, T.count⟩

/-- caml_init_gc returned. -/
structure InitGcDone (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64)
    (Hfinal : List (Nat × Nat)) (before after : Config) : Prop where
  caller : CallerFrame sp before after
  lastExn : bytesT after.σ.mem (domainField backtrace_last_exnOffset) 8 = 1#64
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (1, ra), (8, s0), (9, s1), (18, s2), (19, s3), (20, s4), (21, s5), (22, s6),
    (23, s7), (24, s8), (25, s9)]
  ready : RuntimeReady Hfinal capacity sp ra after
  /-- The runtime's new blocks sit in front of the caller's live list. -/
  extends_ : ∃ pre, Hfinal = pre ++ H
  /-- Low globals outside caml_init_gc's stores are kept. -/
  low : ∀ x, GcLowKeep x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  /-- The page table over the final live list. -/
  table : ∃ ent, GcTableAt Hfinal after.σ.mem ent

/-- A global store window misses everything `GcTailKeep` keeps. -/
theorem gcTail_out {fsp : BitVec 64} (high : heapEnd ≤ fsp.toNat) {a w : Nat} (v : BitVec 64)
    (store : ⟨a, a + w⟩ ∈ gcStoreWindows) {x : Nat} (h : GcTailKeep fsp x) : OutL [(a, w, v)] x := by
  have hE : heapEnd = 0x86800000 := rfl
  simp only [gcStoreWindows, majorWindowAddr, customMajorAddr, customMinorAddr, customMaxAddr, List.mem_cons,
    W.mk.injEq, List.not_mem_nil, or_false] at store
  rcases h with ⟨low, out⟩ | above
  · simp only [gcStoreWindows, OutW, majorWindowAddr, customMajorAddr, customMinorAddr, customMaxAddr, and_true] at out
    simp only [OutL, and_true]
    omega
  · simp only [OutL, and_true]
    rw [hE] at high
    omega

/-- A quiet message's spill misses everything `GcTailKeep` keeps. -/
theorem gcTail_spill {fsp : BitVec 64} (frame : NativeFrame fsp 80) {x : Nat} (h : GcTailKeep fsp x) :
    OutW [⟨nativeFrameBase fsp 80, fsp.toNat⟩] x := by
  have := frame.lower
  simp only [OutW, and_true]
  rcases h with ⟨low, _⟩ | above
  · left; unfold nativeFrameBase; omega
  · right; exact above

/-- The live list when caml_init_gc returns. -/
abbrev initGcFinal (H : List (Nat × Nat)) (blk raw mem stack entries : BitVec 64) : List (Nat × Nat) :=
  (entries.toNat, (32768#64).toNat) :: (stack.toNat, (24#64).toNat) ::
    (mem.toNat, (majorChunkSize 0xf8000#64 + 4152#64).toNat) :: initGcH2 H blk raw

theorem init_gc_finish (c d14 : Config) (H : List (Nat × Nat)) (cap c1 c2 cA cM cP : Nat)
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur blk raw mem stack entries : BitVec 64)
    (A : InitGcCall H cap c1 c2 cA cM cP sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur c)
    (Mj : InitGcMajored H cap sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 blk raw mem stack entries cur c d14) :
    ∃ after, Steps d14 after ∧
      InitGcDone H cap sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 (initGcFinal H blk raw mem stack entries) c after := by
  have frame96 : NativeFrame sp 96 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have frameIn : NativeFrame (nativeStack sp 96) (64 + (32 + allocHeadroom)) := A.frame.nested (front := 96) (by decide)
  have frameMsg : NativeFrame (nativeStack sp 96) 80 := frameIn.resize (by unfold allocHeadroom; omega) (by decide)
  have frameTail : NativeFrame sp 80 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have fspHigh : heapEnd ≤ (nativeStack sp 96).toNat := by have := frameIn.lower; omega
  have stack96 : (nativeStack sp 96).toNat = sp.toNat - 96 := frame96.stack_nat
  have keepLog (a w : Nat) (v : BitVec 64) (store : ⟨a, a + w⟩ ∈ gcStoreWindows) {c' d' : Config}
      (h : d'.σ.mem = writeLog c'.σ.mem [(a, w, v)]) : MemSame c' d' (GcTailKeep (nativeStack sp 96)) :=
    (MemSame.of_log h).mono fun x k => gcTail_out fspHigh v store k
  have keepEq {c' d' : Config} (h : d'.σ.mem = c'.σ.mem) : MemSame c' d' (GcTailKeep (nativeStack sp 96)) :=
    (MemSame.of_eq h).mono fun _ _ => trivial
  have keepCall {c' d' : Config} {l : BitVec 64} (h : GcCallDone (initGcFinal H blk raw mem stack entries) cap
      (nativeStack sp 96) l c' d') : MemSame c' d' (GcTailKeep (nativeStack sp 96)) :=
    ⟨fun x k => h.memory x (gcTail_spill frameMsg k)⟩
  have quietAt {d' : Config} (k : MemSame d14 d' (GcTailKeep (nativeStack sp 96))) :
      LPins8 d'.σ.mem Layout.sym_caml_verb_gc (List.replicate 8 0#8) :=
    lpins8_observed Mj.quiet fun i hi => k.same _ (Or.inl ⟨by unfold Layout.sym_caml_verb_gc heapEnd; omega, by
      simp only [gcStoreWindows, OutW, majorWindowAddr, customMajorAddr, customMinorAddr, customMaxAddr,
        Layout.sym_caml_verb_gc, and_true]; omega⟩)
  have wordAt {d' : Config} (k : MemSame d14 d' (GcTailKeep (nativeStack sp 96))) (a : Nat)
      (apart : a + 8 ≤ 0x80064858 ∨ (0x8006485c ≤ a ∧ a + 8 ≤ 0x800648b0) ∨ (0x800648c8 ≤ a ∧ a + 8 ≤ 0x86800000)) :
      bytesT d'.σ.mem a 8 = bytesT d14.σ.mem a 8 :=
    k.word fun i hi => Or.inl ⟨by unfold heapEnd; omega, by
      simp only [gcStoreWindows, OutW, majorWindowAddr, customMajorAddr, customMinorAddr, customMaxAddr, and_true]
      omega⟩
  have regs14 := Mj.regs
  have link14 : jal_8001f3a4_call.link.toNat % 4 = 0 := by decide
  -- Max_major_window check
  obtain ⟨e1, run1, p1⟩ := (init_gc_window_check d14 jal_8001f3a4_call.link (vsaReg d14 10) Mj.ready.toLeafInput
    ⟨gholds_lookup (n := 23) _ regs14 rfl, OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready Mj.ready 10 (by decide) (by decide), trivial⟩).run d14
    ⟨Mj.pc, rfl⟩
  have g1 := GprsSame.of_post p1 (by decide)
  have r1 := Mj.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    (g1.get (by decide) (by decide) (by decide) Mj.ready.stack) (g1.get (by decide) (by decide) (by decide) Mj.ready.raReg)
    link14 frameIn (by simp only [LogInW])
  have k1 := keepEq p1.memory
  have win := globalWindow_ok (H := initGcFinal H blk raw mem stack entries) (lo := majorWindowAddr) (hi := majorWindowAddr + 4)
    (by decide) (by decide) (by decide) (fun a lo hi => by unfold majorWindowAddr at lo hi; unfold allocGlobal InRange; omega)
    (by decide) (by decide)
  have cmaj := globalWindow_ok (H := initGcFinal H blk raw mem stack entries) (lo := customMajorAddr) (hi := customMajorAddr + 8)
    (by decide) (by decide) (by decide) (fun a lo hi => by unfold customMajorAddr at lo hi; unfold allocGlobal InRange; omega)
    (by decide) (by decide)
  have cmin := globalWindow_ok (H := initGcFinal H blk raw mem stack entries) (lo := customMinorAddr) (hi := customMinorAddr + 8)
    (by decide) (by decide) (by decide) (fun a lo hi => by unfold customMinorAddr at lo hi; unfold allocGlobal InRange; omega)
    (by decide) (by decide)
  have cmax := globalWindow_ok (H := initGcFinal H blk raw mem stack entries) (lo := customMaxAddr) (hi := customMaxAddr + 8)
    (by decide) (by decide) (by decide) (fun a lo hi => by unfold customMaxAddr at lo hi; unfold allocGlobal InRange; omega)
    (by decide) (by decide)
  have cW := cmin.cons cmax
  -- caml_major_window = 1
  obtain ⟨e2, run2, p2⟩ := (init_gc_window_store e1 jal_8001f3a4_call.link (vsaReg d14 10) r1.toLeafInput
    ⟨gholds_lookup (n := 15) _ p1.regs rfl, g1.get (by decide) (by decide) (by decide) (gholds_lookup (n := 24) _ regs14 rfl),
      gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩).run e1 ⟨p1.pc, rfl⟩
  have g2 := GprsSame.of_post p2 (by decide)
  have r2 := r1.window_log p2 (by decide) (by simp only [keysG]; decide) (by decide)
    (g2.get (by decide) (by decide) (by decide) r1.stack) (g2.get (by decide) (by decide) (by decide) r1.raReg) link14
    (by simp only [LogInW, InsideW, majorWindowAddr]; decide) win.pins win.domain win.pool win.heap
  have k2 := keepLog _ _ _ (by simp [gcStoreWindows]) p2.memory
  -- caml_custom_major_ratio = 44
  obtain ⟨e3, run3, p3⟩ := (init_gc_custom_major e2 jal_8001f3a4_call.link (vsaReg d14 10) r2.toLeafInput
    ⟨gholds_lookup (n := 15) _ p2.regs rfl, (g1.trans g2).get (by decide) (by decide) (by decide)
      (gholds_lookup (n := 25) _ regs14 rfl), gholds_lookup (n := 10) _ p2.regs rfl, trivial⟩).run e2 ⟨p2.pc, rfl⟩
  have g3 := GprsSame.of_post p3 (by decide)
  have r3 := r2.window_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
    (g3.get (by decide) (by decide) (by decide) r2.stack) (g3.get (by decide) (by decide) (by decide) r2.raReg) link14
    (by simp only [LogInW, InsideW, customMajorAddr]; decide) cmaj.pins cmaj.domain cmaj.pool cmaj.heap
  have k3 := keepLog _ _ _ (by simp [gcStoreWindows]) p3.memory
  -- the custom minor parameters; the first message's arguments
  obtain ⟨e4, run4, p4⟩ := (init_gc_custom_minor e3 jal_8001f3a4_call.link (vsaReg d14 10)
    (bytesT e3.σ.mem (domainField 80) 8) r3.toLeafInput
    ⟨gholds_lookup (n := 15) _ p3.regs rfl, ((g1.trans g2).trans g3).get (by decide) (by decide) (by decide)
      (gholds_lookup (n := 18) _ regs14 rfl), gholds_lookup (n := 10) _ p3.regs rfl, trivial⟩ r3.domainWord rfl).run e3
    ⟨p3.pc, rfl⟩
  have g4 := GprsSame.of_post p4 (by decide)
  have r4 := r3.window_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
    (g4.get (by decide) (by decide) (by decide) r3.stack) (g4.get (by decide) (by decide) (by decide) r3.raReg) link14
    (by simp only [initGcCustomLog, LogInW, InsideW, customMinorAddr, customMaxAddr]; decide) cW.pins cW.domain cW.pool
    cW.heap
  have k4 : MemSame e3 e4 (GcTailKeep (nativeStack sp 96)) := (MemSame.of_log p4.memory).mono fun x k => by
    have a := gcTail_out fspHigh 100#64 (a := customMinorAddr) (w := 8) (by simp [gcStoreWindows]) k
    have b := gcTail_out fspHigh 8192#64 (a := customMaxAddr) (w := 8) (by simp [gcStoreWindows]) k
    simp only [OutL, and_true] at a b
    simp only [initGcCustomLog, OutL, and_true]
    exact ⟨a, b⟩
  have k04 := ((k1.chain k2).chain k3).chain k4
  have g04 := ((g1.trans g2).trans g3).trans g4
  -- caml_gc_message(…, minor heap size)
  obtain ⟨m1, runm1, M1⟩ := (ready_gc_message_call jal_8001f408_call_shape jal_8001f408_call_decode
    jal_8001f408_call_target (jal_8001f408_call_pins p4.image) r4 frameMsg (gholds_lookup (n := 10) _ p4.regs rfl)
    (quietAt k04) (by decide)).run e4 ⟨p4.pc, rfl⟩
  have km1 := keepCall M1
  -- message 2: the major heap size
  obtain ⟨e5, run5, p5⟩ := (init_gc_msg_heap m1 jal_8001f408_call.link (vsaReg m1 10) 0xf8000#64 M1.ready.toLeafInput
    ⟨(g04.trans M1.same).get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ regs14 rfl),
      OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready M1.ready 10 (by decide) (by decide), trivial⟩).run m1 ⟨M1.pc, rfl⟩
  have g5 := GprsSame.of_post p5 (by decide)
  have r5 := M1.ready.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
    (g5.get (by decide) (by decide) (by decide) M1.ready.stack) (g5.get (by decide) (by decide) (by decide) M1.ready.raReg)
    (by decide) frameIn (by simp only [LogInW])
  have k05 := (k04.chain km1).chain (keepEq p5.memory)
  obtain ⟨m2, runm2, M2⟩ := (ready_gc_message_call jal_8001f41c_call_shape jal_8001f41c_call_decode
    jal_8001f41c_call_target (jal_8001f41c_call_pins p5.image) r5 frameMsg (gholds_lookup (n := 10) _ p5.regs rfl)
    (quietAt k05) (by decide)).run e5 ⟨p5.pc, rfl⟩
  have k06 := k05.chain (keepCall M2)
  have g06 := ((g04.trans M1.same).trans g5).trans M2.same
  -- message 3: caml_percent_free
  obtain ⟨e6, run6, p6⟩ := (init_gc_msg_free m2 jal_8001f41c_call.link (vsaReg m2 10) 120#64
    (by rw [wordAt k06 _ (by unfold percentFreeAddr; omega)]; exact Mj.freeWord) M2.ready.toLeafInput
    ⟨g06.get (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ regs14 rfl),
      OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready M2.ready 10 (by decide) (by decide), trivial⟩).run m2 ⟨M2.pc, rfl⟩
  have g7' := GprsSame.of_post p6 (by decide)
  have r6 := M2.ready.stack_log p6 (by decide) (by simp only [keysG]; decide) (by decide)
    (g7'.get (by decide) (by decide) (by decide) M2.ready.stack) (g7'.get (by decide) (by decide) (by decide) M2.ready.raReg)
    (by decide) frameIn (by simp only [LogInW])
  have k07 := k06.chain (keepEq p6.memory)
  obtain ⟨m3, runm3, M3⟩ := (ready_gc_message_call jal_8001f430_call_shape jal_8001f430_call_decode
    jal_8001f430_call_target (jal_8001f430_call_pins p6.image) r6 frameMsg (gholds_lookup (n := 10) _ p6.regs rfl)
    (quietAt k07) (by decide)).run e6 ⟨p6.pc, rfl⟩
  have k08 := k07.chain (keepCall M3)
  have g08 := (g06.trans g7').trans M3.same
  -- message 4: caml_percent_max
  obtain ⟨e7, run7, p7⟩ := (init_gc_msg_max m3 jal_8001f430_call.link (vsaReg m3 10) 500#64
    (by rw [wordAt k08 _ (by unfold percentMaxAddr; omega)]; exact Mj.maxWord) M3.ready.toLeafInput
    ⟨g08.get (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ regs14 rfl),
      OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready M3.ready 10 (by decide) (by decide), trivial⟩).run m3 ⟨M3.pc, rfl⟩
  have g9' := GprsSame.of_post p7 (by decide)
  have r7 := M3.ready.stack_log p7 (by decide) (by simp only [keysG]; decide) (by decide)
    (g9'.get (by decide) (by decide) (by decide) M3.ready.stack) (g9'.get (by decide) (by decide) (by decide) M3.ready.raReg)
    (by decide) frameIn (by simp only [LogInW])
  have k09 := k08.chain (keepEq p7.memory)
  obtain ⟨m4, runm4, M4⟩ := (ready_gc_message_call jal_8001f444_call_shape jal_8001f444_call_decode
    jal_8001f444_call_target (jal_8001f444_call_pins p7.image) r7 frameMsg (gholds_lookup (n := 10) _ p7.regs rfl)
    (quietAt k09) (by decide)).run e7 ⟨p7.pc, rfl⟩
  have k10 := k09.chain (keepCall M4)
  -- message 5: caml_major_heap_increment (a percentage)
  obtain ⟨e8, run8, p8⟩ := (init_gc_msg_incr m4 jal_8001f444_call.link (vsaReg m4 10) 15#64
    (by rw [wordAt k10 _ (by unfold majorIncrementAddr; omega)]; exact Mj.incrWord) (by decide) M4.ready.toLeafInput
    ⟨OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready M4.ready 10 (by decide) (by decide), trivial⟩).run m4 ⟨M4.pc, rfl⟩
  have g11' := GprsSame.of_post p8 (by decide)
  have r8 := M4.ready.stack_log p8 (by decide) (by simp only [keysG]; decide) (by decide)
    (g11'.get (by decide) (by decide) (by decide) M4.ready.stack) (g11'.get (by decide) (by decide) (by decide) M4.ready.raReg)
    (by decide) frameIn (by simp only [LogInW])
  have k11 := k10.chain (keepEq p8.memory)
  obtain ⟨m5, runm5, M5⟩ := (ready_gc_message_call jal_8001f464_call_shape jal_8001f464_call_decode
    jal_8001f464_call_target (jal_8001f464_call_pins p8.image) r8 frameMsg (gholds_lookup (n := 10) _ p8.regs rfl)
    (quietAt k11) (by decide)).run e8 ⟨p8.pc, rfl⟩
  have k12 := k11.chain (keepCall M5)
  -- message 6: caml_allocation_policy
  obtain ⟨e9, run9, p9⟩ := (init_gc_msg_policy m5 jal_8001f464_call.link (vsaReg m5 10) 2#64
    (by rw [wordAt k12 _ (by unfold allocationPolicyAddr; omega)]; exact Mj.policyWord) M5.ready.toLeafInput
    ⟨OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready M5.ready 10 (by decide) (by decide), trivial⟩).run m5 ⟨M5.pc, rfl⟩
  have g13' := GprsSame.of_post p9 (by decide)
  have r9 := M5.ready.stack_log p9 (by decide) (by simp only [keysG]; decide) (by decide)
    (g13'.get (by decide) (by decide) (by decide) M5.ready.stack) (g13'.get (by decide) (by decide) (by decide) M5.ready.raReg)
    (by decide) frameIn (by simp only [LogInW])
  have k13 := k12.chain (keepEq p9.memory)
  obtain ⟨m6, runm6, M6⟩ := (ready_gc_message_call jal_8001f47c_call_shape jal_8001f47c_call_decode
    jal_8001f47c_call_target (jal_8001f47c_call_pins p9.image) r9 frameMsg (gholds_lookup (n := 10) _ p9.regs rfl)
    (quietAt k13) (by decide)).run e9 ⟨p9.pc, rfl⟩
  have k14 := k13.chain (keepCall M6)
  -- restore; tail call caml_gc_message(…, caml_major_window)
  have slots6 (off : Nat) (value : BitVec 64) (member : (off, value) ∈ initGcSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) :
      bytesT m6.σ.mem (nativeFrameBase sp 96 + off) 8 = value := by
    have bound : off + 8 ≤ 96 := by simp [initGcSlots] at member; omega
    rw [k14.word fun i hi => Or.inr (by rw [stack96]; unfold nativeFrameBase; omega)]
    exact Mj.slots off value member
  obtain ⟨e10, run10, p10⟩ := (init_gc_return m6 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 (vsaReg m6 10) jal_8001f47c_call.link
    M6.ready.toLeafInput frame96 ⟨M6.ready.stack, OCaml.Vm.Boot.WhileMinElfParse.gpr_of_ready M6.ready 10 (by decide) (by decide), trivial⟩
    slots6).run m6 ⟨by have h := M6.pc; rwa [show jal_8001f47c_call.link = 0x8001f480#64 from by decide] at h, rfl⟩
  have g15 := GprsSame.of_post p10 (by decide)
  have r10 : RuntimeReady (initGcFinal H blk raw mem stack entries) cap sp ra e10 :=
    M6.ready.stack_log p10 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p10.regs rfl)
      (gholds_lookup (n := 1) _ p10.regs rfl) A.ready.aligned frame96 (by simp only [LogInW])
  have k15 := k14.chain (keepEq p10.memory)
  obtain ⟨fin, runf, Q⟩ := ready_gc_message e10 (initGcFinal H blk raw mem stack entries) cap sp ra 32#64 p10.pc r10
    frameTail (gholds_lookup (n := 10) _ p10.regs rfl) (quietAt k15)
  have regs10 := p10.regs
  have gQ := Q.same
  have sameT (x : Nat) (inT : InTable blk x) : (fin.σ.mem[x]?).getD 0 = (d14.σ.mem[x]?).getD 0 := by
    have lower := frameTail.lower
    have hS : heapStart = 0x8007d140 := rfl
    have hE : heapEnd = 0x86800000 := rfl
    have hP : pageTable = 0x800684b8 := rfl
    have th := Mj.table.high
    have tl := Mj.table.low
    have below : x < heapEnd := by
      rcases inT with ⟨_, hi⟩ | ⟨_, hi⟩
      · rw [hP] at hi; rw [hE]; omega
      · omega
    have base : x < nativeFrameBase sp 80 := by unfold nativeFrameBase; omega
    rw [Q.memory, frameOn_writeLog _ _ _ (gcMessageLog_inside frameTail) x ⟨Or.inl base, trivial⟩,
      k15.same x (Or.inl ⟨below, by
        simp only [gcStoreWindows, OutW, majorWindowAddr, customMajorAddr, customMinorAddr, customMaxAddr, and_true]
        rcases inT with ⟨lo, _⟩ | ⟨lo, _⟩
        · rw [hP] at lo; omega
        · rw [hS] at th; omega⟩)]
  refine ⟨fin, run1.trans (run2.trans (run3.trans (run4.trans (runm1.trans (run5.trans (runm2.trans (run6.trans
    (runm3.trans (run7.trans (runm4.trans (run8.trans (runm5.trans (run9.trans (runm6.trans (run10.trans
    runf))))))))))))))), {
    caller := ⟨fun x hx => by
      rw [Q.memory, frameOn_writeLog _ _ _ (gcMessageLog_inside frameTail) x ⟨Or.inr hx, trivial⟩,
        k15.same x (Or.inr (by rw [stack96]; omega))]
      exact Mj.caller.byte x hx⟩
    lastExn := by
      rw [Q.word frameTail _ (by decide), wordAt k15 _ (by decide)]
      exact Mj.lastExn
    pc := Q.pc
    regs := ⟨gholds_lookup (n := 2) _ Q.regs rfl, gholds_lookup (n := 1) _ Q.regs rfl,
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ regs10 rfl),
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ regs10 rfl),
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ regs10 rfl),
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ regs10 rfl),
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 20) _ regs10 rfl),
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 21) _ regs10 rfl),
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 22) _ regs10 rfl),
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 23) _ regs10 rfl),
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 24) _ regs10 rfl),
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 25) _ regs10 rfl), trivial⟩
    ready := Q.ready
    low := fun x k => by
      have lower := frameTail.lower
      have xl := k.low
      have hS : heapStart = 0x8007d140 := rfl
      have hE : heapEnd = 0x86800000 := rfl
      have below : x < nativeFrameBase sp 80 := by unfold nativeFrameBase; omega
      rw [Q.memory, frameOn_writeLog _ _ _ (gcMessageLog_inside frameTail) x ⟨Or.inl below, trivial⟩,
        k15.same x (Or.inl ⟨by omega, k.stores⟩)]
      exact Mj.low x k
    table := ⟨blk, Mj.table.agree sameT, by
      rw [pageCount_agree (Nat.le_trans Mj.table.low (by decide)) sameT]; exact Mj.count⟩
    extends_ := ⟨[(entries.toNat, (32768#64).toNat), (stack.toNat, (24#64).toNat),
      (mem.toNat, (majorChunkSize 0xf8000#64 + 4152#64).toNat), (raw.toNat, (0x200000#64 + 4096#64).toNat),
      (blk.toNat, 16384)], rfl⟩ }⟩

/-- **caml_init_gc** at the default parameters, from its entry to its return:
the page table, the minor heap, the allocation policy, the major heap and the
quiet parameter messages. -/
theorem caml_init_gc (c : Config) (H : List (Nat × Nat)) (cap c1 c2 cA cM cP : Nat)
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur : BitVec 64)
    (A : InitGcCall H cap c1 c2 cA cM cP sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur c) :
    ∃ Hfinal after, Steps c after ∧ InitGcDone H cap sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 Hfinal c after := by
  obtain ⟨blk, d4, run4, T⟩ := init_gc_to_table c H cap c1 c2 cA cM cP sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur A
  obtain ⟨raw, d7, run7, Mi⟩ := init_gc_to_minor c d4 H cap c1 c2 cA cM cP sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3
    cur blk A T
  obtain ⟨mem, stack, entries, d14, run14, Mj⟩ := init_gc_to_major c d7 H cap c1 c2 cA cM cP sp ra s0 s1 s2 s3 s4 s5 s6 s7
    s8 s9 t1 t2 t3 cur blk raw A Mi
  obtain ⟨fin, runf, D⟩ := init_gc_finish c d14 H cap c1 c2 cA cM cP sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur blk
    raw mem stack entries A Mj
  exact ⟨_, fin, run4.trans (run7.trans (run14.trans runf)), D⟩

end OCaml.Vm.Boot.Startup
