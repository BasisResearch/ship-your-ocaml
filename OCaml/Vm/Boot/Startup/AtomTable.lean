import OCaml.Vm.Boot.Startup.AtomSteps
import OCaml.Vm.Boot.Startup.StatAligned
import OCaml.Vm.Boot.Startup.PageAdd
import OCaml.Vm.Boot.Startup.PageApart
import OCaml.Vm.Boot.Startup.MajorHeap
import OCaml.Vm.Boot.Startup.CallerFrame
import OCaml.Vm.Boot.Startup.GprsSame
import OCaml.Vm.Boot.Startup.MakeFree
import OCaml.Vm.Boot.Startup.InitMerge
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives LeanRV64DExecutable

/-! **caml_init_atom_table()**: one page from caml_stat_alloc_aligned_noexc,
published in `caml_atom_table`, the 256 black zero-size headers, and the page
registered `In_static_data`. -/

/-- The atoms' span: inside a live block above the arena's start. -/
structure AtomSpan (H : List (Nat × Nat)) (base : BitVec 64) (q n : Nat) : Prop where
  owned : (q, n) ∈ H
  blockLow : heapStart ≤ q
  start : q ≤ base.toNat
  stop : base.toNat + 2048 ≤ q + n
  high : base.toNat + 2048 ≤ heapEnd
  aligned : base.toNat % 8 = 0

theorem AtomSpan.low {H : List (Nat × Nat)} {base : BitVec 64} {q n : Nat} (S : AtomSpan H base q n) : heapStart ≤ base.toNat :=
  Nat.le_trans S.blockLow S.start

theorem AtomSpan.windows {H : List (Nat × Nat)} {base : BitVec 64} {q n : Nat} (S : AtomSpan H base q n) :
    WindowsOk H [⟨base.toNat, base.toNat + 2048⟩] :=
  ownedWindow_ok S.blockLow S.owned S.start S.stop

theorem atomEntry_nat {base : BitVec 64} {k : Nat} (hk : k < 256) (high : base.toNat + 2048 ≤ heapEnd) :
    (atomEntry base k).1 = base.toNat + 8 * k := by
  have hE : heapEnd = 0x86800000 := rfl
  rw [hE] at high
  simp only [atomEntry, atomCursor]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt (a := 8 * k) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The loop after `k` atoms. -/
structure AtomAt (H : List (Nat × Nat)) (capacity : Nat) (sp ra base a0 : BitVec 64)
    (start : Config) (k : Nat) (d : Config) : Prop where
  pc : PCAt (if k < 256 then 0x800044d4#64 else 0x800044f0#64) d
  regs : GHolds d.σ [(11, base), (15, atomCursor k), (14, atomHeader k), (12, BitVec.ofNat 64 atomTableAddr),
    (10, a0)]
  ready : RuntimeReady H capacity sp ra d
  bound : k ≤ 256
  published : bytesT d.σ.mem atomTableAddr 8 = base
  atoms : ∀ j, j < k → bytesT d.σ.mem (base.toNat + 8 * j) 8 = atomHeader j
  kept : ∀ x, x < base.toNat ∨ base.toNat + 2048 ≤ x → (d.σ.mem[x]?).getD 0 = (start.σ.mem[x]?).getD 0
  same : GprsSame start d [11, 15, 13, 14]

theorem AtomAt.index {H capacity sp ra base a0 start k d} (A : AtomAt H capacity sp ra base a0 start k d) :
    ((gprGet d.σ 15).getD 0).toNat / 8 = k := by
  have bound := A.bound
  rw [gholds_lookup (n := 15) _ A.regs rfl]
  simp only [Option.getD_some, atomCursor, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem atom_at_step {H capacity sp ra base a0 start q n} (S : AtomSpan H base q n) (k : Nat) (d : Config)
    (A : AtomAt H capacity sp ra base a0 start k d) (lt : k < 256) :
    ∃ e, Steps d e ∧ AtomAt H capacity sp ra base a0 start (k + 1) e := by
  have pc : PCAt 0x800044d4#64 d := by have := A.pc; simp only [lt, ite_true] at this; exact this
  have hS : heapStart = 0x8007d140 := rfl
  have low := S.low
  have high := S.high
  rw [hS] at low
  have entry := atomEntry_nat (base := base) lt S.high
  have tableApart : atomTableAddr + 8 ≤ base.toNat := by unfold atomTableAddr; omega
  have inside : LogInW [⟨base.toNat, base.toNat + 2048⟩] [atomEntry base k] := by
    simp only [LogInW, InsideW, and_true]
    rw [entry, show (atomEntry base k).2.1 = 8 from rfl]
    omega
  have go (exit : AtomExit k (if k + 1 < 256 then caml_init_atom_tableX44d4TSeg else caml_init_atom_tableX44d4FSeg)
      (if k + 1 < 256 then 0x800044d4#64 else 0x800044f0#64)) : ∃ e, Steps d e ∧ AtomAt H capacity sp ra base a0 start (k + 1) e := by
    obtain ⟨e, run, p⟩ := (atom_loop_step d ra base a0 k exit A.ready.toLeafInput A.regs S.low S.high S.aligned
      A.published).run d ⟨pc, rfl⟩
    have g := GprsSame.of_post p (by decide)
    have W := S.windows
    have mem : e.σ.mem = writeLog d.σ.mem [atomEntry base k] := p.memory
    refine ⟨e, run, {
      pc := by
        have := p.pc
        by_cases more : k + 1 < 256 <;> simp only [more, ite_true, ite_false] at this ⊢ <;> exact this
      regs := ⟨gholds_lookup (n := 11) _ p.regs rfl, gholds_lookup (n := 15) _ p.regs rfl,
        gholds_lookup (n := 14) _ p.regs rfl, gholds_lookup (n := 12) _ p.regs rfl, gholds_lookup (n := 10) _ p.regs rfl,
        trivial⟩
      ready := A.ready.window_log p (by decide) (by simp only [keysG]; decide) (by decide)
        (g.get (by decide) (by decide) (by decide) A.ready.stack) (g.get (by decide) (by decide) (by decide) A.ready.raReg)
        A.ready.aligned inside W.pins W.domain W.pool W.heap
      bound := by omega
      published := by
        rw [mem, bytesT_writeLog_out _ (by simp only [OutLRange, and_true]; rw [entry]; omega)]
        exact A.published
      atoms := fun j hj => by
        rw [mem]
        by_cases same : j = k
        · subst same
          exact word_writeLog_at _ _ 0 _ _ (by rw [← entry]; rfl) trivial
        · rw [bytesT_writeLog_out _ (by simp only [OutLRange, and_true]; rw [entry]; omega)]
          exact A.atoms j (by omega)
      kept := fun x out => by
        rw [mem, writeLog_out _ _ _ (by simp only [OutL, and_true]; rw [entry, show (atomEntry base k).2.1 = 8 from rfl]; omega)]
        exact A.kept x out
      same := (A.same.trans g).mono (by decide) }⟩
  by_cases more : k + 1 < 256
  · exact go (by simp only [more, ite_true]; exact .more more)
  · exact go (by simp only [more, ite_false]; exact .last (by omega))

theorem atom_loop {H capacity sp ra base a0 q n} (S : AtomSpan H base q n) {start : Config}
    (A : AtomAt H capacity sp ra base a0 start 0 start) :
    ∃ d, Steps start d ∧ AtomAt H capacity sp ra base a0 start 256 d :=
  indexedLoop (I := AtomAt H capacity sp ra base a0 start) (index := fun d => ((gprGet d.σ 15).getD 0).toNat / 8)
    (start := 0) (count := 256) (fun _ _ h => h.index) (fun _ _ h => h.bound)
    (fun k d ⟨h, lt⟩ => atom_at_step S k d h lt) start A

/-- caml_page_table_add's last page for a range shorter than a page. -/
theorem range_last (base : BitVec 64) (len : Nat) (aligned : base.toNat % 4096 = 0) (pos : 0 < len) (short : len ≤ 4096)
    (fits : base.toNat + 4096 < 2 ^ 64) :
    (base + BitVec.ofNat 64 len + Functions.sign_extend (m := 64) 4095#12) &&& 0xfffffffffffff000#64 =
      blockPage base (1 - 1) := by
  have p64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [p64] at fits
  rw [show Functions.sign_extend (m := 64) 4095#12 = 18446744073709551615#64 by decide]
  apply BitVec.eq_of_toNat_eq
  rw [page_mask_nat, blockPage_nat base 0 (by rw [p64]; omega), BitVec.toNat_add, BitVec.toNat_add,
    BitVec.toNat_ofNat, show (18446744073709551615#64).toNat = 18446744073709551615 from rfl, p64]
  generalize base.toNat = b at *
  rw [Nat.mod_eq_of_lt (a := len) (by omega), Nat.mod_eq_of_lt (a := b + len) (by omega)]
  have back : (b + len + 18446744073709551615) % 18446744073709551616 = b + len - 1 := by omega
  rw [back]
  omega

/-- caml_page_table_add keeps the ABI callee-saved registers. -/
theorem PageAdded.gprs {H capacity sp ra kind s0 s1 s2 s3 base ent n before after}
    (PA : PageAdded H capacity sp ra kind s0 s1 s2 s3 base ent n before after)
    (h8 : gprGet before.σ 8 = some s0) (h9 : gprGet before.σ 9 = some s1) (h18 : gprGet before.σ 18 = some s2)
    (h19 : gprGet before.σ 19 = some s3) : GprsSame before after abiClobbered :=
  ⟨fun k lo hi out => by
    have : k = 8 ∨ k = 9 ∨ k = 18 ∨ k = 19 ∨ (20 ≤ k ∧ k ≤ 27) := by
      simp only [abiClobbered, List.mem_cons, List.not_mem_nil, or_false] at out; omega
    rcases this with rfl | rfl | rfl | rfl | ⟨l, h⟩
    · rw [gholds_lookup (n := 8) _ PA.regs rfl, h8]
    · rw [gholds_lookup (n := 9) _ PA.regs rfl, h9]
    · rw [gholds_lookup (n := 18) _ PA.regs rfl, h18]
    · rw [gholds_lookup (n := 19) _ PA.regs rfl, h19]
    · exact PA.saved k l h⟩

/-- caml_init_atom_table's entry: the page table as caml_init_gc left it, with a slot to spare. -/
structure AtomTableCall (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra ent : BitVec 64) (c : Config) : Prop where
  pc : PCAt 0x800044a4#64 c
  regs : GHolds c.σ [(2, sp), (1, ra)]
  ready : RuntimeReady H (capacity + charge) sp ra c
  frame : NativeFrame sp (32 + (32 + allocHeadroom))
  charged : vsaChg 8192 charge
  table : MajorTableAt H c.σ.mem ent
  room : pageCount c.σ.mem ent.toNat + 1 ≤ 1024

/-- caml_init_atom_table returned: the atoms are in the fresh block's
aligned page, published, and the page is in the table. -/
structure AtomTableDone (H : List (Nat × Nat)) (capacity : Nat) (sp ra ent raw : BitVec 64) (before after : Config) :
    Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (1, ra)]
  ready : RuntimeReady ((raw.toNat, 8192) :: H) capacity sp ra after
  fresh : FreshBlock vsaLayoutP H raw.toNat 8192
  published : bytesT after.σ.mem atomTableAddr 8 = pageAbove raw
  atoms : ∀ j, j < 256 → bytesT after.σ.mem ((pageAbove raw).toNat + 8 * j) 8 = atomHeader j
  table : MajorTableAt ((raw.toNat, 8192) :: H) after.σ.mem ent
  count : pageCount after.σ.mem ent.toNat = pageCount before.σ.mem ent.toNat + 1
  /-- Below the arena's end, outside the allocator, the table word, the atoms and the page table. -/
  kept : ∀ x, x < heapEnd → ¬ vsaFoot H x → (x < atomTableAddr ∨ atomTableAddr + 8 ≤ x) →
    (x < (pageAbove raw).toNat ∨ (pageAbove raw).toNat + 2048 ≤ x) → ¬ InTable ent x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  caller : CallerFrame sp before after
  saved : ∀ k ∈ abiSaved, gprGet after.σ k = gprGet before.σ k

theorem caml_init_atom_table (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra ent : BitVec 64)
    (A : AtomTableCall H capacity charge sp ra ent c) :
    ∃ raw after, Steps c after ∧ AtomTableDone H capacity sp ra ent raw c after := by
  have frame32 : NativeFrame sp 32 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have frameIn : NativeFrame (nativeStack sp 32) (32 + allocHeadroom) := A.frame.nested (front := 32) (by decide)
  have frame144 : NativeFrame (nativeStack sp 32) 144 := frameIn.resize (by unfold allocHeadroom; omega) (by decide)
  have stackNat : (nativeStack sp 32).toNat = sp.toNat - 32 := frame32.stack_nat
  have spLow := A.frame.lower
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have hP : pageTable = 0x800684b8 := rfl
  unfold allocHeadroom at spLow
  rw [hE] at spLow
  -- save ra; caml_stat_alloc_aligned_noexc(Page_size, 0, &b)
  obtain ⟨c1, run1, p1⟩ := (atom_save_call c sp ra A.ready.toLeafInput frame32 A.regs).run c ⟨A.pc, rfl⟩
  have g1 := GprsSame.of_post p1 (by decide)
  have inside1 : LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (atomSaveLog sp ra) :=
    frame32.word_log_inside fun off value member => by simp at member; omega
  have ready1 := A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) (by decide) frame32 inside1
  have slot1 : bytesT c1.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra := by
    rw [p1.memory]
    exact frame32.word_log_read (fun off value member => by simp at member; omega) (by simp)
      _ (List.mem_singleton.mpr rfl)
  have low1 (x : Nat) (hx : x < nativeFrameBase sp 32) : (c1.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p1.memory, frameOn_writeLog _ _ _ inside1 x ⟨Or.inl hx, trivial⟩]
  have target1 : jal_800044b8_call.target = 0x8000ab80#64 := jal_800044b8_call_target
  obtain ⟨raw, c2, run2, D⟩ := stat_alloc_aligned c1 H capacity charge (nativeStack sp 32) jal_800044b8_call.link
    0x1000#64 (nativeStack sp 32 + 8#64) sp 32 8 {
      pc := by rw [← target1]; exact p1.pc
      regs := ⟨gholds_lookup (n := 2) _ p1.regs rfl, gholds_lookup (n := 1) _ p1.regs rfl,
        gholds_lookup (n := 10) _ p1.regs rfl, gholds_lookup (n := 11) _ p1.regs rfl,
        gholds_lookup (n := 12) _ p1.regs rfl, trivial⟩
      ready := ready1
      frame := frameIn
      charged := A.charged
      outFrame := frame32
      outAt := rfl
      outBound := by decide
      outAligned := by decide
      outAbove := by rw [stackNat]; exact Nat.le_refl _ }
  have size8 : (0x1000#64 + 4096#64).toNat = 8192 := by decide
  have fresh : FreshBlock vsaLayoutP H raw.toNat 8192 := by rw [← size8]; exact D.fresh
  have rawLo : heapStart ≤ raw.toNat := fresh.2.1
  have rawHi : raw.toNat + 8192 ≤ heapEnd := fresh.2.2.1
  rw [hS] at rawLo
  rw [hE] at rawHi
  have inside := pageAbove_inside raw 4096 (by omega)
  generalize hbase : pageAbove raw = base at inside
  have baseAligned : base.toNat % 4096 = 0 := inside.2.2
  have span : AtomSpan ((raw.toNat, 8192) :: H) base raw.toNat 8192 := {
    owned := List.mem_cons_self
    blockLow := by rw [hS]; exact rawLo
    start := Nat.le_of_lt inside.1
    stop := by omega
    high := by rw [hE]; omega
    aligned := by omega }
  have ready2 : RuntimeReady ((raw.toNat, 8192) :: H) capacity (nativeStack sp 32) jal_800044b8_call.link c2 := by
    rw [← size8]; exact D.ready
  have g2 := GprsSame.of_saved D.saved
  -- caml_atom_table = b; the loop's registers
  obtain ⟨c3, run3, p3⟩ := (atom_publish c2 jal_800044b8_call.link base ready2.toLeafInput
    ⟨by rw [← hbase]; exact gholds_lookup (n := 10) _ D.regs rfl, trivial⟩).run c2 ⟨D.pc, rfl⟩
  have g3 := GprsSame.of_post p3 (by decide)
  have publishInside : LogInW [⟨atomTableAddr, atomTableAddr + 8⟩] [(atomTableAddr, 8, base)] := by
    simp only [LogInW, InsideW, and_true]; omega
  have publishW : WindowsOk ((raw.toNat, 8192) :: H) [⟨atomTableAddr, atomTableAddr + 8⟩] :=
    globalWindow_ok (by decide) (by decide) (by decide)
      (fun a lo hi => by unfold atomTableAddr at lo hi; unfold allocGlobal InRange; omega) (by decide) (by decide)
  have ready3 := ready2.window_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
    (g3.get (by decide) (by decide) (by decide) ready2.stack) (g3.get (by decide) (by decide) (by decide) ready2.raReg)
    ready2.aligned publishInside publishW.pins publishW.domain publishW.pool publishW.heap
  -- the 256 headers
  obtain ⟨c4, run4, L⟩ := atom_loop span (start := c3) (a0 := base) (A := {
    pc := by simp only [show (0 : Nat) < 256 from by decide, ite_true]; exact p3.pc
    regs := ⟨gholds_lookup (n := 11) _ p3.regs rfl, gholds_lookup (n := 15) _ p3.regs rfl,
      gholds_lookup (n := 14) _ p3.regs rfl, gholds_lookup (n := 12) _ p3.regs rfl,
      gholds_lookup (n := 10) _ p3.regs rfl, trivial⟩
    ready := ready3
    bound := by decide
    published := by rw [p3.memory]; exact word_writeLog_at _ _ 0 _ _ rfl trivial
    atoms := fun j hj => absurd hj (Nat.not_lt_zero _)
    kept := fun _ _ => rfl
    same := (GprsSame.refl c3).mono (by decide) })
  -- memory below the arena's end, outside the allocator, the table word and the atoms
  have below (x : Nat) (hx : x < heapEnd) (foot : ¬ vsaFoot H x) (tw : x < atomTableAddr ∨ atomTableAddr + 8 ≤ x)
      (aw : x < base.toNat ∨ base.toNat + 2048 ≤ x) : (c4.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [hE] at hx
    rw [L.kept x aw, p3.memory, writeLog_out _ _ _ (by simp only [OutL, and_true]; omega),
      D.kept x (by rw [stackNat]; unfold allocHeadroom; omega) foot, low1 x (by unfold nativeFrameBase; omega)]
  have tableOut (x : Nat) (inT : InTable ent x) : x < heapEnd ∧ ¬ vsaFoot H x ∧
      (x < atomTableAddr ∨ atomTableAddr + 8 ≤ x) ∧ (x < base.toNat ∨ base.toNat + 2048 ≤ x) := by
    have tl := A.table.low
    have th := A.table.high
    rw [hE] at tl
    rw [hS] at th
    rcases inT with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · rw [hP] at lo hi
      exact ⟨by rw [hE]; omega, pageTable_record_not_foot (by rw [hP]; exact lo) (by rw [hP]; exact hi),
        by unfold atomTableAddr; omega, by omega⟩
    · have apart := fresh.2.2.2 _ A.table.owned x
      unfold InExt at apart
      dsimp only at apart
      refine ⟨by rw [hE]; omega, owned_not_foot' (by rw [hS]; exact th) A.table.owned lo hi,
        by unfold atomTableAddr; omega, ?_⟩
      by_cases inBlock : raw.toNat ≤ x ∧ x < raw.toNat + 8192
      · exact absurd ⟨lo, hi⟩ (apart inBlock)
      · omega
  -- caml_page_table_add(In_static_data, b, b + 257 words)
  obtain ⟨c5, run5, p5⟩ := (atom_page_add_call c4 jal_800044b8_call.link base L.ready.toLeafInput
    ⟨gholds_lookup (n := 11) _ L.regs rfl, trivial⟩).run c4 ⟨by simpa using L.pc, rfl⟩
  have g5 := GprsSame.of_post p5 (by decide)
  have mem5 : c5.σ.mem = c4.σ.mem := p5.memory
  have ready5 : RuntimeReady ((raw.toNat, 8192) :: H) capacity (nativeStack sp 32) jal_800044fc_call.link c5 :=
    L.ready.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
      (g5.get (by decide) (by decide) (by decide) L.ready.stack) (gholds_lookup (n := 1) _ p5.regs rfl) (by decide)
      frame32 (by simp only [LogInW])
  have tableSame (x : Nat) (inT : InTable ent x) : (c5.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    obtain ⟨hx, foot, tw, aw⟩ := tableOut x inT
    rw [mem5]; exact below x hx foot tw aw
  have fitsT : ent.toNat + 16384 ≤ 2 ^ 64 := Nat.le_trans A.table.low (by decide)
  have tableH := A.table.agree tableSame
  have table5 := tableH.cons (raw.toNat, 8192)
  have count5 := pageCount_agree fitsT tableSame
  obtain ⟨s0, hs0⟩ := Option.isSome_iff_exists.mp (ready5.gpr_some 8 (by decide) (by decide))
  obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.mp (ready5.gpr_some 9 (by decide) (by decide))
  obtain ⟨s2, hs2⟩ := Option.isSome_iff_exists.mp (ready5.gpr_some 18 (by decide) (by decide))
  obtain ⟨s3, hs3⟩ := Option.isSome_iff_exists.mp (ready5.gpr_some 19 (by decide) (by decide))
  have target5 : jal_800044fc_call.target = 0x8000b0ec#64 := jal_800044fc_call_target
  obtain ⟨c6, run6, PA⟩ := page_table_add c5 ((raw.toNat, 8192) :: H) capacity (nativeStack sp 32)
    jal_800044fc_call.link 4#64 base (base + 2056#64) s0 s1 s2 s3 base ent 1 {
      pc := by rw [← target5]; exact p5.pc
      regs := ⟨ready5.stack, ready5.raReg, gholds_lookup (n := 10) _ p5.regs rfl, gholds_lookup (n := 11) _ p5.regs rfl,
        gholds_lookup (n := 12) _ p5.regs rfl, hs0, hs1, hs2, hs3, trivial⟩
      ready := ready5
      first := block_first base baseAligned
      last := range_last base 2056 baseAligned (by decide) (by decide) (by omega)
      nonempty := by decide
      fields := table5.fields
      span := {
        frame := frame144
        aligned := baseAligned
        fits := by omega
        small := by decide
        kindNonzero := by decide
        room := by rw [count5]; exact A.room
        windows := table5.windows
        tableLow := table5.low
        tableHigh := table5.high
        tableOwned := table5.owned
        disjoint := fun i hi occ j hj => fresh_page_apart fresh baseAligned (by omega) (by omega) (by omega)
          (tableH.occupied i hi occ) } }
  have gPA := PA.gprs hs0 hs1 hs2 hs3
  -- caml_page_table_add returned 0
  have link5 : jal_800044fc_call.link = 0x80004500#64 := by decide
  obtain ⟨c7, run7, p7⟩ := (atom_test c6 jal_800044fc_call.link PA.ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ PA.regs rfl, trivial⟩).run c6 ⟨by rw [← link5]; exact PA.pc, rfl⟩
  have g7 := GprsSame.of_post p7 (by decide)
  have mem7 : c7.σ.mem = c6.σ.mem := p7.memory
  -- the caller's frame from the save on
  have outNat : (nativeStack sp 32 + 8#64).toNat = nativeFrameBase sp 32 + 8 := by
    rw [nativeStack, frame32.address _ (by decide)]; exact frame32.slot_nat (by decide)
  have upper (x : Nat) (hx : nativeFrameBase sp 32 ≤ x) (slot : x < nativeFrameBase sp 32 + 8 ∨ nativeFrameBase sp 32 + 16 ≤ x) :
      (c7.σ.mem[x]?).getD 0 = (c1.σ.mem[x]?).getD 0 := by
    have base32 : nativeFrameBase sp 32 = sp.toNat - 32 := rfl
    rw [mem7, PA.caller x (by rw [stackNat, ← base32]; exact hx), mem5,
      L.kept x (Or.inr (by have := span.high; rw [hE] at this; omega)), p3.memory,
      writeLog_out _ _ _ (by simp only [OutL, and_true]; unfold atomTableAddr; omega),
      D.caller x (by rw [stackNat, ← base32]; exact hx) (by rw [outNat]; omega)]
  have slot7 : bytesT c7.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra := by
    rw [word_observed (m := c1.σ.mem) _ fun i hi => upper _ (by omega) (by omega)]
    exact slot1
  have ready7 : RuntimeReady ((raw.toNat, 8192) :: H) capacity (nativeStack sp 32) jal_800044fc_call.link c7 :=
    PA.ready.stack_log p7 (by decide) (by simp only [keysG]; decide) (by decide)
      (g7.get (by decide) (by decide) (by decide) PA.ready.stack) (g7.get (by decide) (by decide) (by decide) PA.ready.raReg)
      PA.ready.aligned frame32 (by simp only [LogInW])
  -- restore ra, return
  obtain ⟨c8, run8, p8⟩ := (atom_return c7 sp ra jal_800044fc_call.link ready7.toLeafInput frame32
    ⟨ready7.stack, gholds_lookup (n := 10) _ p7.regs rfl, trivial⟩ slot7 A.ready.aligned).run c7 ⟨p7.pc, rfl⟩
  have g8 := GprsSame.of_post p8 (by decide)
  have mem8 : c8.σ.mem = c6.σ.mem := by rw [p8.memory, ← mem7]; rfl
  have ready8 : RuntimeReady ((raw.toNat, 8192) :: H) capacity sp ra c8 :=
    ready7.stack_log p8 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p8.regs rfl)
      (gholds_lookup (n := 1) _ p8.regs rfl) A.ready.aligned frame32 (by simp only [LogInW])
  -- from the loop's end to the return, only the page table changed
  have mid (x : Nat) (hx : x < heapEnd)
      (out : OutW [⟨pageTable + 0x18, pageTable + 0x20⟩, ⟨ent.toNat, ent.toNat + 16384⟩] x) :
      (c8.σ.mem[x]?).getD 0 = (c4.σ.mem[x]?).getD 0 := by
    rw [mem8, PA.kept x hx out, mem5]
  have atomOut (x : Nat) (lo : base.toNat ≤ x) (hi : x < base.toNat + 2048) :
      OutW [⟨pageTable + 0x18, pageTable + 0x20⟩, ⟨ent.toNat, ent.toNat + 16384⟩] x := by
    have th := A.table.high
    rw [hS] at th
    have apart := fresh.2.2.2 _ A.table.owned x
    unfold InExt at apart
    dsimp only at apart
    simp only [OutW, and_true]
    refine ⟨by rw [hP]; omega, ?_⟩
    by_cases inT : ent.toNat ≤ x ∧ x < ent.toNat + 16384
    · exact absurd inT (apart ⟨by omega, by omega⟩)
    · omega
  have t6 : MajorTableAt ((raw.toNat, 8192) :: H) c6.σ.mem ent := {
    fields := by rw [PA.count]; exact PA.fields
    low := table5.low
    high := table5.high
    owned := table5.owned
    windows := table5.windows
    apartDomain := table5.apartDomain
    occupied := fun i hi occ => by
      rcases PA.known i hi occ with same | ⟨j, hj, eq⟩
      · rw [same] at occ ⊢; exact table5.occupied i hi occ
      · have j0 : j = 0 := by omega
        subst j0
        have page := blockPage_nat base 0 (by omega)
        rw [eq]
        exact ⟨4#64, blockPage base 0, (raw.toNat, 8192), {
          owned := List.mem_cons_self
          inBlock := by unfold InExt; dsimp only; rw [page]; omega
          aligned := by rw [page]; omega
          small := by decide
          word := rfl }⟩ }
  have total := (((((((g1.trans g2).trans g3).trans L.same).trans g5).trans gPA).trans g7).trans g8).mono
    (vs := abiClobbered) (by decide)
  have savedRange : ∀ k ∈ abiSaved, 1 ≤ k ∧ k ≤ 31 ∧ k ∉ abiClobbered := by decide
  refine ⟨raw, c8, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans run8)))))), {
    pc := p8.pc
    regs := ⟨gholds_lookup (n := 2) _ p8.regs rfl, gholds_lookup (n := 1) _ p8.regs rfl, trivial⟩
    ready := ready8
    fresh := fresh
    published := by
      rw [hbase, word_observed (m := c4.σ.mem) _ fun i hi => mid _ (by unfold atomTableAddr; rw [hE]; omega)
        (by simp only [OutW, and_true]; rw [hP]; have := A.table.high; rw [hS] at this; unfold atomTableAddr; omega)]
      exact L.published
    atoms := fun j hj => by
      rw [hbase, word_observed (m := c4.σ.mem) _ fun i hi => mid _ (by have := span.high; omega)
        (atomOut _ (by omega) (by omega))]
      exact L.atoms j hj
    table := t6.agree fun x _ => by rw [mem8]
    count := by
      rw [show pageCount c8.σ.mem ent.toNat = pageCount c6.σ.mem ent.toNat by rw [mem8], PA.count, count5]
    kept := fun x hx foot tw aw notT => by
      rw [hbase] at aw
      simp only [InTable] at notT
      rw [hP] at notT
      rw [mid x hx (by simp only [OutW, and_true]; rw [hP]; omega), below x hx foot tw aw]
    caller := ⟨fun x hx => by
      have base32 : nativeFrameBase sp 32 = sp.toNat - 32 := rfl
      rw [p8.memory, show writeLog c7.σ.mem [] = c7.σ.mem from rfl, upper x (by omega) (by omega),
        p1.memory, frameOn_writeLog _ _ _ inside1 x ⟨Or.inr hx, trivial⟩]⟩
    saved := fun k hk => total.same k (savedRange k hk).1 (savedRange k hk).2.1 (savedRange k hk).2.2 }⟩

end OCaml.Vm.Boot.Startup
