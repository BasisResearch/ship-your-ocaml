import OCaml.Vm.Primitives.Named.ModifyRootFinish

/-!
# `caml_modify_generational_global_root(r, v)` as a machine run

The prologue saves the frame and branches on `v`'s low bit; a block `v` is
classified (`vClassify`), then `w = *r` on the path of `v`'s class:

* young `v` (`yPath`): a young `w` stores; an old one leaves the old list and
  joins the young one (`yRemoveTail`); any other joins the young one
  (`yInsertTail`);
* old `v` (`oPath`): a young or old `w` stores; any other joins the old list
  (`oInsertTail`);
* other `v` (`xPath`): a young `w` leaves the young list (`xRemoveYoungTail`),
  an old one both lists (`xRemoveOldTail`), any other stores.

Every tail ends in `Acting.finish`. `modify_root_run` is the whole function.
-/

namespace OCaml.Vm.Primitives.Named.ModifyRoot
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm OCaml.Vm.Primitives OCaml.Vm.Gc OCaml.Vm.Gc.Skiplist
open OCaml.Vm.Boot.Startup (NativeFrame HeapReady nativeFrameBase)
open NamedValue (regsAt regsAt_of gpr_some gpr_some_of gprReg_ne_htif wl_nil)
open RegisterRoot (Young Old rootValue YoungAt ListsFoot IsList lists_kept frame32)

variable {Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop}
  {foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop}
  {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop}
  {H : List (Nat × Nat)} {cap : Nat} {rs ys os : List (BitVec 64)} {cls : Nat → Nat}
  {D start stop sp ra r v : BitVec 64} {c : Config}

/-- The memory after the prologue's three saves. -/
abbrev mem1 (c : Config) (sp ra : BitVec 64) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog c.σ.mem (proLog sp (regsAt c 8) (regsAt c 9) ra)

/-! ### Placing the root -/

theorem RootAt.of_young {w : BitVec 64} {ys' os' : List (BitVec 64)} (yv : Young start stop w)
    (h : r ∈ ys' ∧ r ∉ os') : RootAt start stop cls w r ys' os' :=
  ⟨fun _ => h, fun _ => Or.inl h.1, fun ny => absurd yv ny⟩

theorem RootAt.of_old {w : BitVec 64} {ys' os' : List (BitVec 64)} (ov : Old start stop cls w)
    (h : r ∈ ys' ∨ r ∈ os') : RootAt start stop cls w r ys' os' :=
  ⟨fun yv => absurd ⟨yv.2.1, yv.2.2⟩ ov.2.1, fun _ => h, fun _ no => absurd ov no⟩

theorem RootAt.of_none {w : BitVec 64} {ys' os' : List (BitVec 64)} (ny : ¬ Young start stop w)
    (no : ¬ Old start stop cls w) (h : r ∉ ys' ∧ r ∉ os') : RootAt start stop cls w r ys' os' :=
  ⟨fun yv => absurd yv ny, fun ov => absurd ov no, fun _ _ => h⟩

/-- Unchanged lists keep their membership. -/
theorem memb_refl : ∀ k, k ≠ r → (k ∈ ys ↔ k ∈ ys) ∧ (k ∈ os ↔ k ∈ os) := fun _ _ => ⟨Iff.rfl, Iff.rfl⟩

/-! ### What the prologue keeps -/

/-- The prologue's saves keep everything below the native stack: the young
bounds, the page table and `*r`. -/
structure Kept1 (Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop) (m : Std.ExtHashMap Nat (BitVec 8))
    (cls : Nat → Nat) (D start stop r w : BitVec 64) : Prop where
  young : YoungAt m D start stop
  table : Table m cls
  value : bytesVal .ld (read8 m r.toNat) = w

theorem read8_low {m m' : Std.ExtHashMap Nat (BitVec 8)}
    (agree : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → (m'[a]?).getD 0 = (m[a]?).getD 0) {a : Nat}
    (ha : a + 8 ≤ Vsa.Sim.DlHeap.heapEnd) : read8 m' a = read8 m a := by
  simp only [read8, agree a (by omega), agree (a + 1) (by omega), agree (a + 2) (by omega), agree (a + 3) (by omega),
    agree (a + 4) (by omega), agree (a + 5) (by omega), agree (a + 6) (by omega), agree (a + 7) (by omega)]

theorem ModifyInput.kept1 (pt : PageTableLookup Table)
    (h : ModifyInput Shape foot Table H cap rs ys os cls D start stop sp ra r v c) :
    Kept1 Table (mem1 c sp ra) cls D start stop r (rootValue c r) := by
  have frame := h.frame
  have lower : Vsa.Sim.DlHeap.heapEnd + (32 + 768) ≤ sp.toNat := frame.lower
  have upper := frame.upper
  simp only [Layout.sym_stack_top] at upper
  have op := frame.resize (small := opStack) (by unfold opStack; omega) (by decide)
  have slot (k : Nat) (hk : k ≤ 32) : (sp - 32#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 32 + k := by
    rw [(frame32 op hk).1, BitVec.toNat_ofNat]; omega
  have log0 : LogInW [⟨sp.toNat - 32, sp.toNat⟩] (proLog sp (regsAt c 8) (regsAt c 9) ra) := by
    have e8 := slot 8 (by decide)
    have e16 := slot 16 (by decide)
    have e24 := slot 24 (by decide)
    simp only [proLog, LogInW, InsideW, e8, e16, e24, and_true]; omega
  have low : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → ((mem1 c sp ra)[a]?).getD 0 = (c.σ.mem[a]?).getD 0 :=
    fun a ha => by rw [frameOn_writeLog _ _ _ log0 a ⟨Or.inl (show a < sp.toNat - 32 by omega), trivial⟩]
  have y := h.young
  exact
    { young :=
        { state := by rw [read8_low low (by decide)]; exact y.state
          startWord := by rw [read8_low low h.startBelow]; exact y.startWord
          stopWord := by rw [read8_low low h.stopBelow]; exact y.stopWord
          startWin := y.startWin
          stopWin := y.stopWin }
      table := pt.frame _ _ cls h.table low
      value := by rw [read8_low low h.slotHigh]; rfl }

/-! ### The tails: list calls, then the store -/

/-- **`r` joins the young list, then the store** (from `0x8000cbc8`, a young
`v`). -/
theorem yInsertTail (ops : Ops Shape foot) (h : ModifyInput Shape foot Table H cap rs ys os cls D start stop sp ra r v c)
    {x : Config} {ys1 os1 : List (BitVec 64)} (run0 : Steps c x)
    (act : Acting Shape foot H (mem1 c sp ra) sp v r rs c x ys1 os1) (pc0 : PCAt 0x8000cbc8#64 x)
    (yv : Young start stop v) (notOld : r ∉ os1) (memb : ∀ k, k ≠ r → (k ∈ ys1 ↔ k ∈ ys) ∧ (k ∈ os1 ↔ k ∈ os)) :
    ∃ d, Steps c d ∧ RootModified Shape foot H rs ys os cls start stop sp ra r v c d := by
  obtain ⟨frame', spNat⟩ := inner_frame h.frame
  let R := regsAt x
  have r9 : R 9 = r := regsAt_of act.s1
  obtain ⟨l, hl, -⟩ := act.link
  obtain ⟨y, run1, p⟩ := (yInsert_fast x R act.leaf ⟨gpr_some (gpr_some_of hl), gpr_some (gpr_some_of act.s0),
    gpr_some (gpr_some_of act.s1), trivial⟩).run x ⟨pc0, rfl⟩
  obtain ⟨z, run2, entry, z12⟩ := act.enter (opPc := insertPc) (hdr := globalRootsYoung) yInsert_call_shape
    yInsert_call_decode (fun _ h => yInsert_call_pins h) yInsert_call_target (by decide) p (by decide) (by decide)
    (holds_at p.regs rfl rfl) (holds_at p.regs rfl r9)
  obtain ⟨d1, ys2, run3, pc3, act3, q⟩ := act.step_young ops entry (by decide) spNat frame'
    (Q := fun ks => ∀ k, k ∈ ks ↔ k = r ∨ k ∈ ys1)
    (fun ks q => young_apart act.roots fun k hk =>
      ((q k).1 hk).elim (fun e => Or.inr (e ▸ ⟨h.notGlobal, notOld⟩)) Or.inl)
    (entry.insert ops (z12.trans (holds_at p.regs rfl rfl)) frame')
  obtain ⟨d2, run4, act4, -, p4⟩ := act3.line (show PCAt 0x8000cbdc#64 d1 from pc3) (by decide) (by decide)
    (yJoin_fast d1 (regsAt d1) act3.leaf ⟨gpr_some act3.a0, trivial⟩)
  exact act4.finish ops h store_block (run0.trans (run1.trans (run2.trans (run3.trans run4)))) p4.pc
    (fun k ne => ⟨((q k).trans ⟨fun e => e.resolve_left ne, Or.inr⟩).trans (memb k ne).1, (memb k ne).2⟩)
    (RootAt.of_young yv ⟨(q r).2 (Or.inl rfl), notOld⟩)

/-- **`r` leaves the old list and joins the young one** (from `0x8000cbb8`, a
young `v` over an old `w`). -/
theorem yRemoveTail (ops : Ops Shape foot) (h : ModifyInput Shape foot Table H cap rs ys os cls D start stop sp ra r v c)
    {x : Config} (run0 : Steps c x) (act : Acting Shape foot H (mem1 c sp ra) sp v r rs c x ys os)
    (pc0 : PCAt 0x8000cbb8#64 x) (yv : Young start stop v) :
    ∃ d, Steps c d ∧ RootModified Shape foot H rs ys os cls start stop sp ra r v c d := by
  obtain ⟨frame', spNat⟩ := inner_frame h.frame
  let R := regsAt x
  have r9 : R 9 = r := regsAt_of act.s1
  obtain ⟨l, hl, -⟩ := act.link
  obtain ⟨y, run1, p⟩ := (yRemove_fast x R act.leaf ⟨gpr_some (gpr_some_of hl), gpr_some (gpr_some_of act.s0),
    gpr_some (gpr_some_of act.s1), trivial⟩).run x ⟨pc0, rfl⟩
  obtain ⟨z, run2, entry, -⟩ := act.enter (opPc := removePc) (hdr := globalRootsOld) yRemove_call_shape
    yRemove_call_decode (fun _ h => yRemove_call_pins h) yRemove_call_target (by decide) p (by decide) (by decide)
    (holds_at p.regs rfl rfl) (holds_at p.regs rfl r9)
  obtain ⟨d1, os2, run3, pc3, act3, q⟩ := act.step_old ops entry (by decide) spNat frame'
    (Q := fun ks => ∀ k, k ∈ ks ↔ k ≠ r ∧ k ∈ os)
    (fun ks q => old_apart act.roots fun k hk => Or.inl ((q k).1 hk).2) (entry.remove ops frame')
  obtain ⟨d, run, post⟩ := yInsertTail ops h (run0.trans (run1.trans (run2.trans run3))) act3
    (show PCAt 0x8000cbc8#64 d1 from pc3) yv (fun hr => ((q r).1 hr).1 rfl)
    (fun k ne => ⟨Iff.rfl, (q k).trans ⟨fun e => e.2, fun e => ⟨ne, e⟩⟩⟩)
  exact ⟨d, run, post⟩

/-- **`r` joins the old list, then the store** (from `0x8000cc48`, an old `v`
over an immediate or unboxed `w`). -/
theorem oInsertTail (ops : Ops Shape foot) (h : ModifyInput Shape foot Table H cap rs ys os cls D start stop sp ra r v c)
    {x : Config} (run0 : Steps c x) (act : Acting Shape foot H (mem1 c sp ra) sp v r rs c x ys os)
    (pc0 : PCAt 0x8000cc48#64 x) (ov : Old start stop cls v) (notYoung : r ∉ ys) :
    ∃ d, Steps c d ∧ RootModified Shape foot H rs ys os cls start stop sp ra r v c d := by
  obtain ⟨frame', spNat⟩ := inner_frame h.frame
  let R := regsAt x
  have r9 : R 9 = r := regsAt_of act.s1
  obtain ⟨l, hl, -⟩ := act.link
  obtain ⟨y, run1, p⟩ := (oInsert_fast x R act.leaf ⟨gpr_some (gpr_some_of hl), gpr_some (gpr_some_of act.s0),
    gpr_some (gpr_some_of act.s1), trivial⟩).run x ⟨pc0, rfl⟩
  obtain ⟨z, run2, entry, z12⟩ := act.enter (opPc := insertPc) (hdr := globalRootsOld) oInsert_call_shape
    oInsert_call_decode (fun _ h => oInsert_call_pins h) oInsert_call_target (by decide) p (by decide) (by decide)
    (holds_at p.regs rfl rfl) (holds_at p.regs rfl r9)
  obtain ⟨d1, os2, run3, pc3, act3, q⟩ := act.step_old ops entry (by decide) spNat frame'
    (Q := fun ks => ∀ k, k ∈ ks ↔ k = r ∨ k ∈ os)
    (fun ks q => old_apart act.roots fun k hk =>
      ((q k).1 hk).elim (fun e => Or.inr (e ▸ ⟨h.notGlobal, notYoung⟩)) Or.inl)
    (entry.insert ops (z12.trans (holds_at p.regs rfl rfl)) frame')
  exact act3.finish ops h oStore_block (run0.trans (run1.trans (run2.trans run3)))
    (show PCAt 0x8000cc5c#64 d1 from pc3)
    (fun k ne => ⟨Iff.rfl, (q k).trans ⟨fun e => e.resolve_left ne, Or.inr⟩⟩)
    (RootAt.of_old ov (Or.inr ((q r).2 (Or.inl rfl))))

/-- **`r` leaves the young list, then the store** (from `0x8000cc20`, an
immediate or unboxed `v`). -/
theorem xRemoveYoungTail (ops : Ops Shape foot)
    (h : ModifyInput Shape foot Table H cap rs ys os cls D start stop sp ra r v c)
    {x : Config} {os1 : List (BitVec 64)} (run0 : Steps c x)
    (act : Acting Shape foot H (mem1 c sp ra) sp v r rs c x ys os1) (pc0 : PCAt 0x8000cc20#64 x)
    (ny : ¬ Young start stop v) (no : ¬ Old start stop cls v) (notOld : r ∉ os1)
    (memb : ∀ k, k ≠ r → (k ∈ os1 ↔ k ∈ os)) :
    ∃ d, Steps c d ∧ RootModified Shape foot H rs ys os cls start stop sp ra r v c d := by
  obtain ⟨frame', spNat⟩ := inner_frame h.frame
  let R := regsAt x
  have r9 : R 9 = r := regsAt_of act.s1
  obtain ⟨l, hl, -⟩ := act.link
  obtain ⟨y, run1, p⟩ := (xRemoveYoung_fast x R act.leaf ⟨gpr_some (gpr_some_of hl),
    gpr_some (gpr_some_of act.s0), gpr_some (gpr_some_of act.s1), trivial⟩).run x ⟨pc0, rfl⟩
  obtain ⟨z, run2, entry, -⟩ := act.enter (opPc := removePc) (hdr := globalRootsYoung) xRemoveYoung_call_shape
    xRemoveYoung_call_decode (fun _ h => xRemoveYoung_call_pins h) xRemoveYoung_call_target (by decide) p
    (by decide) (by decide) (holds_at p.regs rfl rfl) (holds_at p.regs rfl r9)
  obtain ⟨d1, ys2, run3, pc3, act3, q⟩ := act.step_young ops entry (by decide) spNat frame'
    (Q := fun ks => ∀ k, k ∈ ks ↔ k ≠ r ∧ k ∈ ys)
    (fun ks q => young_apart act.roots fun k hk => Or.inl ((q k).1 hk).2) (entry.remove ops frame')
  exact act3.finish ops h xStore_block (run0.trans (run1.trans (run2.trans run3)))
    (show PCAt 0x8000cc30#64 d1 from pc3)
    (fun k ne => ⟨(q k).trans ⟨fun e => e.2, fun e => ⟨ne, e⟩⟩, memb k ne⟩)
    (RootAt.of_none ny no ⟨fun hr => ((q r).1 hr).1 rfl, notOld⟩)

/-- **`r` leaves the old list and the young one** (from `0x8000cc10`, an
immediate or unboxed `v` over an old `w`). -/
theorem xRemoveOldTail (ops : Ops Shape foot)
    (h : ModifyInput Shape foot Table H cap rs ys os cls D start stop sp ra r v c)
    {x : Config} (run0 : Steps c x) (act : Acting Shape foot H (mem1 c sp ra) sp v r rs c x ys os)
    (pc0 : PCAt 0x8000cc10#64 x) (ny : ¬ Young start stop v) (no : ¬ Old start stop cls v) :
    ∃ d, Steps c d ∧ RootModified Shape foot H rs ys os cls start stop sp ra r v c d := by
  obtain ⟨frame', spNat⟩ := inner_frame h.frame
  let R := regsAt x
  have r9 : R 9 = r := regsAt_of act.s1
  obtain ⟨l, hl, -⟩ := act.link
  obtain ⟨y, run1, p⟩ := (xRemoveOld_fast x R act.leaf ⟨gpr_some (gpr_some_of hl), gpr_some (gpr_some_of act.s0),
    gpr_some (gpr_some_of act.s1), trivial⟩).run x ⟨pc0, rfl⟩
  obtain ⟨z, run2, entry, -⟩ := act.enter (opPc := removePc) (hdr := globalRootsOld) xRemoveOld_call_shape
    xRemoveOld_call_decode (fun _ h => xRemoveOld_call_pins h) xRemoveOld_call_target (by decide) p (by decide)
    (by decide) (holds_at p.regs rfl rfl) (holds_at p.regs rfl r9)
  obtain ⟨d1, os2, run3, pc3, act3, q⟩ := act.step_old ops entry (by decide) spNat frame'
    (Q := fun ks => ∀ k, k ∈ ks ↔ k ≠ r ∧ k ∈ os)
    (fun ks q => old_apart act.roots fun k hk => Or.inl ((q k).1 hk).2) (entry.remove ops frame')
  exact xRemoveYoungTail ops h (run0.trans (run1.trans (run2.trans run3))) act3
    (show PCAt 0x8000cc20#64 d1 from pc3) ny no (fun hr => ((q r).1 hr).1 rfl)
    (fun k ne => (q k).trans ⟨fun e => e.2, fun e => ⟨ne, e⟩⟩)

/-! ### The three paths -/

/-- **An immediate or unboxed `v`** (from `0x8000cbe0`). -/
theorem xPath (ops : Ops Shape foot) (pt : PageTableLookup Table)
    (h : ModifyInput Shape foot Table H cap rs ys os cls D start stop sp ra r v c)
    {x : Config} (run0 : Steps c x) (s : Settled Shape foot H (mem1 c sp ra) sp v r rs c ys os x)
    (pc0 : PCAt 0x8000cbe0#64 x) (ny : ¬ Young start stop v) (no : ¬ Old start stop cls v) :
    ∃ d, Steps c d ∧ RootModified Shape foot H rs ys os cls start stop sp ra r v c d := by
  have k1 := h.kept1 pt
  obtain ⟨y, run, sy, lands⟩ := wClassify pt xBlocks k1.table k1.young h.slot.read k1.value s pc0
  rcases lands with ⟨yw, pc, -⟩ | ⟨ow, pc⟩ | ⟨nyw, now, pc⟩
  · exact xRemoveYoungTail ops h (run0.trans run) sy.acting pc ny no (h.root.young yw).2 fun _ _ => Iff.rfl
  · exact xRemoveOldTail ops h (run0.trans run) sy.acting pc ny no
  · exact sy.acting.finish ops h store_block (run0.trans run) pc memb_refl
      (RootAt.of_none ny no (h.root.none nyw now))

/-- **An old `v`** (from `0x8000cb50`). -/
theorem oPath (ops : Ops Shape foot) (pt : PageTableLookup Table)
    (h : ModifyInput Shape foot Table H cap rs ys os cls D start stop sp ra r v c)
    {x : Config} (run0 : Steps c x) (s : Settled Shape foot H (mem1 c sp ra) sp v r rs c ys os x)
    (pc0 : PCAt 0x8000cb50#64 x) (ov : Old start stop cls v) :
    ∃ d, Steps c d ∧ RootModified Shape foot H rs ys os cls start stop sp ra r v c d := by
  have k1 := h.kept1 pt
  obtain ⟨y, run, sy, lands⟩ := wClassify pt oBlocks k1.table k1.young h.slot.read k1.value s pc0
  rcases lands with ⟨yw, pc, -⟩ | ⟨ow, pc⟩ | ⟨nyw, now, pc⟩
  · exact sy.acting.finish ops h store_block (run0.trans run) pc memb_refl
      (RootAt.of_old ov (Or.inl (h.root.young yw).1))
  · exact sy.acting.finish ops h store_block (run0.trans run) pc memb_refl (RootAt.of_old ov (h.root.old ow))
  · exact oInsertTail ops h (run0.trans run) sy.acting pc ov (h.root.none nyw now).1

/-- **A young `v`** (from `0x8000cb98`, `v`'s young bounds in `a3`/`a5`). -/
theorem yPath (ops : Ops Shape foot) (pt : PageTableLookup Table)
    (h : ModifyInput Shape foot Table H cap rs ys os cls D start stop sp ra r v c)
    {x : Config} (run0 : Steps c x) (s : Settled Shape foot H (mem1 c sp ra) sp v r rs c ys os x)
    (pc0 : PCAt 0x8000cb98#64 x) (regs : YoungRegs r start stop x) (yv : Young start stop v) :
    ∃ d, Steps c d ∧ RootModified Shape foot H rs ys os cls start stop sp ra r v c d := by
  have k1 := h.kept1 pt
  obtain ⟨y, run, sy, lands⟩ := yClassify pt k1.table h.slot.read k1.value s pc0 regs
  rcases lands with ⟨yw, pc, -⟩ | ⟨ow, pc⟩ | ⟨nyw, now, pc⟩
  · exact sy.acting.finish ops h store_block (run0.trans run) pc memb_refl (RootAt.of_young yv (h.root.young yw))
  · exact yRemoveTail ops h (run0.trans run) sy.acting pc yv
  · exact yInsertTail ops h (run0.trans run) sy.acting pc yv (h.root.none nyw now).2 memb_refl

/-! ### The whole function -/

/-- **`caml_modify_generational_global_root(r, v)`**: `*r = v`, and `r` moves
between the young and old lists so that `RootAt` places it for `v`. -/
theorem modify_root_run (ops : Ops Shape foot) (pt : PageTableLookup Table)
    (h : ModifyInput Shape foot Table H cap rs ys os cls D start stop sp ra r v c) :
    FnSummary 0x8000cb08#64 (fun x => x = c) (RootModified Shape foot H rs ys os cls start stop sp ra r v c) := by
  constructor
  intro x ⟨pc, eq⟩
  subst eq
  let R := regsAt x
  have r1 : R 1 = ra := regsAt_of h.leaf.raReg
  have r2 : R 2 = sp := regsAt_of h.stack
  have r10 : R 10 = r := regsAt_of h.slotReg
  have r11 : R 11 = v := regsAt_of h.valueReg
  have frame := h.frame
  have lower : Vsa.Sim.DlHeap.heapEnd + (32 + 768) ≤ sp.toNat := frame.lower
  have small := frame.resize (small := 32) (by unfold opStack; omega) (by decide)
  have op := frame.resize (small := opStack) (by unfold opStack; omega) (by decide)
  have saveW (k : Nat) (hk : k + 8 ≤ 32) (al : k % 8 = 0) : WriteWindow (R 2 - 32#64 + BitVec.ofNat 64 k) 8 := by
    rw [r2, (frame32 op (k := k) (by omega)).1]
    have w := small.word (off := k) hk al
    rwa [show nativeFrameBase sp 32 + k = sp.toNat - 32 + k by unfold nativeFrameBase; rfl] at w
  have saveNat (k : Nat) (hk : k ≤ 32) : (R 2 - 32#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 32 + k := by
    have upper := frame.upper
    simp only [Layout.sym_stack_top] at upper
    rw [r2, (frame32 op hk).1, BitVec.toNat_ofNat]; omega
  have outside (log : List WEntry)
      (hl : log = [((R 2 - 32#64 + 16#64).toNat, 8, R 8), ((R 2 - 32#64 + 8#64).toNat, 8, R 9),
        ((R 2 - 32#64 + 24#64).toNat, 8, R 1)]) : ImageOutside log :=
    OCaml.Vm.Sim.imageOutside_of_above fun e he => by
      have e8 := saveNat 8 (by decide)
      have e16 := saveNat 16 (by decide)
      have e24 := saveNat 24 (by decide)
      have hb : Layout.sym_bss_end ≤ Vsa.Sim.DlHeap.heapEnd := by decide
      subst hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      have base : Vsa.Sim.DlHeap.heapEnd ≤ sp.toNat - 32 :=
        Nat.le_sub_of_add_le (Nat.le_trans (Nat.add_le_add_left (by decide : 32 ≤ 32 + 768) _) lower)
      have up (k : Nat) : Layout.sym_bss_end ≤ sp.toNat - 32 + k :=
        Nat.le_trans hb (Nat.le_trans base (Nat.le_add_right _ k))
      rcases he with rfl | rfl | rfl
      · rw [e16]; exact up 16
      · rw [e8]; exact up 8
      · rw [e24]; exact up 24
  have regs0 : GHolds x.σ [(1, R 1), (2, R 2), (8, R 8), (9, R 9), (10, R 10), (11, R 11)] :=
    ⟨gpr_some (gpr_some_of h.leaf.raReg), gpr_some (gpr_some_of h.stack), gpr_some h.s0, gpr_some h.s1,
      gpr_some (gpr_some_of h.slotReg), gpr_some (gpr_some_of h.valueReg), trivial⟩
  have leaf0 : LeafInput (R 1) x := by rw [r1]; exact h.leaf
  by_cases imm : v &&& 1#64 ≠ 0#64
  · have blk := newImm_fast x R leaf0 regs0 (saveW 16 (by decide) (by decide)) (saveW 8 (by decide) (by decide))
      (saveW 24 (by decide) (by decide)) (outside _ rfl) (by rw [r11]; simpa [guardB] using imm)
    simp only [newImmLog, newImm_regs, r1, r2, r10, r11] at blk
    obtain ⟨x1, run1, pc1, st⟩ := prologue ops h blk pc
    exact xPath ops pt h run1 ⟨st.acting, st.memory⟩ pc1 (fun yv => imm yv.1) (fun ov => imm ov.1)
  · have blkv : v &&& 1#64 = 0#64 := Classical.not_not.mp imm
    have blk := newBlock_fast x R leaf0 regs0 (saveW 16 (by decide) (by decide)) (saveW 8 (by decide) (by decide))
      (saveW 24 (by decide) (by decide)) (outside _ rfl) (by rw [r11]; simp [guardB, blkv])
    simp only [newBlockLog, newBlock_regs, r1, r2, r10, r11] at blk
    obtain ⟨x1, run1, pc1, st⟩ := prologue ops h blk pc
    have k1 := h.kept1 pt
    obtain ⟨y, run2, sy, lands⟩ := vClassify pt k1.table k1.young blkv ⟨st.acting, st.memory⟩ pc1 st.slotReg
      st.valueReg
    rcases lands with ⟨yv, pcY, regsY⟩ | ⟨ov, pcO⟩ | ⟨nyv, nov, pcN⟩
    · exact yPath ops pt h (run1.trans run2) sy pcY regsY yv
    · exact oPath ops pt h (run1.trans run2) sy pcO ov
    · exact xPath ops pt h (run1.trans run2) sy pcN nyv nov

end OCaml.Vm.Primitives.Named.ModifyRoot
