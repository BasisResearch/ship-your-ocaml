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

end OCaml.Vm.Boot.Startup
