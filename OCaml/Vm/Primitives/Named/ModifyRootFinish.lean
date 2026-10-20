import OCaml.Vm.Primitives.Named.ModifyRootClassify

/-!
# The store and the list calls of `caml_modify_generational_global_root`

Every path ends with the same five instructions at one of three addresses:
`*r = v`, then the restores of `ra`, `s0`, `s1` and the return (`StoreBlock`).
`Acting.finish` turns `Acting` at such a block into `RootModified`, given the
lists' membership and `RootAt` for `v`. The list calls (`caml_skiplist_insert`
and `caml_skiplist_remove`) enter from an `OpEntry`; `OpEntry.insert` and
`OpEntry.remove` put a6-gc's `Ops` contracts in the form `Acting.step_young`
and `Acting.step_old` take.
-/

namespace OCaml.Vm.Primitives.Named.ModifyRoot
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm OCaml.Vm.Primitives OCaml.Vm.Gc OCaml.Vm.Gc.Skiplist
open OCaml.Vm.Boot.Startup (NativeFrame HeapReady nativeFrameBase)
open NamedValue (regsAt regsAt_of gpr_some gpr_some_of gprReg_ne_htif wl_nil)
open RegisterRoot (Young Old rootValue YoungAt ListsFoot IsList lists_kept frame32)

variable {Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop}
  {foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop}

/-! ### The list calls -/

/-- **`caml_skiplist_insert(sk, r, 0)` from an `OpEntry`**: the new keys are
`r` and the old ones. -/
theorem OpEntry.insert (ops : Ops Shape foot) {link sp r : BitVec 64} {sk : Nat} {x z : Config}
    (entry : OpEntry insertPc link sp r sk x z) (a2 : gprGet z.σ 12 = some 0#64) (frame : NativeFrame sp opStack)
    {ks : List (BitVec 64)} :
    ∀ H cap cs, Shape z.σ.mem sk cs → keys z.σ.mem cs = ks → HeapReady H cap z →
      FnSummary insertPc (fun d => d = z) (fun d => Returned H (foot z.σ.mem sk cs) sp link z d ∧
        ∃ cs', Shape d.σ.mem sk cs' ∧ (∀ k, k ∈ keys d.σ.mem cs' ↔ k = r ∨ k ∈ ks) ∧
          ∀ a, foot d.σ.mem sk cs' a → foot z.σ.mem sk cs a ∨ VsaIris.VsaHeap.vsaFoot H a) :=
  fun H cap cs sh hk heap =>
    (ops.insert H cap sk cs r sp link z sh ⟨entry.leaf, heap, ⟨entry.stack, entry.list, entry.key, a2, trivial⟩,
      frame⟩).weaken (fun _ h => h)
      fun _ ⟨ret, cs', sh', kin, kold, kout, footIn⟩ => ⟨ret, cs', sh', insert_keys hk kin kold kout, footIn⟩

/-- **`caml_skiplist_remove(sk, r)` from an `OpEntry`**: the new keys are the
old ones but `r`. -/
theorem OpEntry.remove (ops : Ops Shape foot) {link sp r : BitVec 64} {sk : Nat} {x z : Config}
    (entry : OpEntry removePc link sp r sk x z) (frame : NativeFrame sp opStack) {ks : List (BitVec 64)} :
    ∀ H cap cs, Shape z.σ.mem sk cs → keys z.σ.mem cs = ks → HeapReady H cap z →
      FnSummary removePc (fun d => d = z) (fun d => Returned H (foot z.σ.mem sk cs) sp link z d ∧
        ∃ cs', Shape d.σ.mem sk cs' ∧ (∀ k, k ∈ keys d.σ.mem cs' ↔ k ≠ r ∧ k ∈ ks) ∧
          ∀ a, foot d.σ.mem sk cs' a → foot z.σ.mem sk cs a ∨ VsaIris.VsaHeap.vsaFoot H a) :=
  fun H cap cs sh hk heap =>
    (ops.remove H cap sk cs r sp link z sh ⟨entry.leaf, heap, ⟨entry.stack, entry.list, entry.key, trivial⟩,
      frame⟩).weaken (fun _ h => h)
      fun _ ⟨ret, cs', sh', kout, kold, ksub, footIn⟩ =>
        ⟨ret, cs', sh', remove_keys hk kout kold ksub, fun a f => Or.inl (footIn a f)⟩

/-- New young keys from the young list or apart from the other two lists stay
apart from them. -/
theorem young_apart {m : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {ks : List (BitVec 64)} (sub : ∀ k ∈ ks, k ∈ ys ∨ (k ∉ rs ∧ k ∉ os)) :
    ∀ k ∈ ks, k ∉ rs ∧ k ∉ os := by
  have nd := g.distinct
  simp only [List.nodup_append, List.mem_append] at nd
  intro k hk
  rcases sub k hk with hy | fresh
  · exact ⟨fun h => nd.1.2.2 k h k hy rfl, fun h => nd.2.2 k (Or.inr hy) k h rfl⟩
  · exact fresh

/-- New old keys from the old list or apart from the other two lists stay
apart from them. -/
theorem old_apart {m : Std.ExtHashMap Nat (BitVec 8)} {rs ys os : List (BitVec 64)}
    (g : GlobalRoots Shape foot m rs ys os) {ks : List (BitVec 64)} (sub : ∀ k ∈ ks, k ∈ os ∨ (k ∉ rs ∧ k ∉ ys)) :
    ∀ k ∈ ks, k ∉ rs ∧ k ∉ ys := by
  have nd := g.distinct
  simp only [List.nodup_append, List.mem_append] at nd
  intro k hk
  rcases sub k hk with ho | fresh
  · exact ⟨fun h => nd.2.2 k (Or.inl h) k ho rfl, fun h => nd.2.2 k (Or.inr h) k ho rfl⟩
  · exact fresh

/-! ### The frame -/

/-- The callees' frame below the 32-byte one. -/
theorem inner_frame {sp : BitVec 64} (frame : NativeFrame sp (32 + opStack)) :
    NativeFrame (sp + 18446744073709551584#64) opStack ∧
      (sp + 18446744073709551584#64).toNat = sp.toNat - 32 := by
  have n := frame.nested (front := 32) (by decide)
  have e : OCaml.Vm.Boot.Startup.nativeStack sp 32 = sp + 18446744073709551584#64 := rfl
  rw [e] at n
  refine ⟨n, ?_⟩
  have z := (frame32 (frame.resize (small := opStack) (by omega) (by decide)) (k := 0) (by decide)).2
  rw [BitVec.add_zero, Nat.add_zero] at z
  rw [z, BitVec.toNat_ofNat]
  have := frame.upper; simp only [Layout.sym_stack_top] at this
  omega

/-- Bytes above the arena are outside the lists, newlib's footprint and
`random_seed`. -/
theorem above_arena (ops : Ops Shape foot) {m : Std.ExtHashMap Nat (BitVec 8)} {H : List (Nat × Nat)} {a : Nat}
    (ha : Vsa.Sim.DlHeap.heapEnd ≤ a) :
    ¬ ListsFoot Shape foot m a ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ (a < randomSeed ∨ randomSeed + 4 ≤ a) := by
  have hE : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  refine ⟨fun ⟨sk, cells, _, sh, f⟩ => by have := ops.low _ _ _ sh a f; omega, fun f => ?_, Or.inr ?_⟩
  · rcases f with g | ⟨_, lt, _⟩
    · simp only [VsaIris.VsaHeap.allocGlobal, VsaIris.VsaHeap.InRange] at g; omega
    · omega
  · unfold randomSeed; omega

/-! ### The store and the return -/

/-- **The store and return blocks** at `pS`: `*r = v`, then `ra`, `s0` and
`s1` restored from the 32-byte frame and the return. -/
def StoreBlock (pS : BitVec 64) : Prop :=
  ∀ (x : Config) (ra : BitVec 64) (R : Nat → BitVec 64), LeafInput (R 1) x →
    GHolds x.σ [(2, R 2), (8, R 8), (9, R 9), (10, R 10)] → WriteWindow (R 9) 8 →
    ReadWindow (R 2 + 24#64) 8 → OutLRange ([((R 9).toNat, 8, R 8)].take 1) (R 2 + 24#64).toNat 8 →
    ReadWindow (R 2 + 16#64) 8 → OutLRange ([((R 9).toNat, 8, R 8)].take 1) (R 2 + 16#64).toNat 8 →
    ReadWindow (R 2 + 8#64) 8 → OutLRange ([((R 9).toNat, 8, R 8)].take 1) (R 2 + 8#64).toNat 8 →
    ImageOutside [((R 9).toNat, 8, R 8)] → bytesVal .ld (read8 x.σ.mem (R 2 + 24#64).toNat) = ra →
    ra.toNat % 4 = 0 →
    FnSummary pS (fun d => d = x) (WriteRegistersPost [1, 2, 8, 9] [((R 9).toNat, 8, R 8)] x ra (R 10)
      [(2, R 2 + 32#64), (9, bytesVal .ld (read8 x.σ.mem (R 2 + 8#64).toNat)),
        (8, bytesVal .ld (read8 x.σ.mem (R 2 + 16#64).toNat)), (1, bytesVal .ld (read8 x.σ.mem (R 2 + 24#64).toNat)),
        (10, R 10)])

theorem store_block : StoreBlock 0x8000cb80#64 := store_fast
theorem xStore_block : StoreBlock 0x8000cc30#64 := xStore_fast
theorem oStore_block : StoreBlock 0x8000cc5c#64 := oStore_fast

/-- **The store and the return finish the call**: from `Acting` at a store
block, with the lists' new keys `ys' os'` agreeing with `ys os` off `r` and
placing `r` by `RootAt` for `v`. -/
theorem Acting.finish {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop} (ops : Ops Shape foot)
    {H : List (Nat × Nat)} {cap : Nat} {rs ys os : List (BitVec 64)} {cls : Nat → Nat}
    {D start stop sp ra r v : BitVec 64} {c x : Config} {ys' os' : List (BitVec 64)} {pS : BitVec 64}
    (h : ModifyInput Shape foot Table H cap rs ys os cls D start stop sp ra r v c) (st : StoreBlock pS)
    (run0 : Steps c x)
    (act : Acting Shape foot H (writeLog c.σ.mem (proLog sp (regsAt c 8) (regsAt c 9) ra)) sp v r rs c x ys' os')
    (pc0 : PCAt pS x) (memb : ∀ k, k ≠ r → (k ∈ ys' ↔ k ∈ ys) ∧ (k ∈ os' ↔ k ∈ os))
    (place : RootAt start stop cls v r ys' os') :
    ∃ d, Steps c d ∧ RootModified Shape foot H rs ys os cls start stop sp ra r v c d := by
  have frame := h.frame
  have lower : Vsa.Sim.DlHeap.heapEnd + (32 + 768) ≤ sp.toNat := frame.lower
  have hE : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have upper := frame.upper
  simp only [Layout.sym_stack_top] at upper
  have op := frame.resize (small := opStack) (by unfold opStack; omega) (by decide)
  have small := frame.resize (small := 32) (by unfold opStack; omega) (by decide)
  have slotHigh := h.slotHigh
  have slotLow := h.slotLow
  have hS : Vsa.Sim.DlHeap.heapStart ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  have base : Vsa.Sim.DlHeap.heapEnd ≤ sp.toNat - 32 :=
    Nat.le_sub_of_add_le (Nat.le_trans (Nat.add_le_add_left (by decide : 32 ≤ 32 + 768) _) lower)
  -- the frame after the prologue
  have slot (k : Nat) (hk : k ≤ 32) : (sp - 32#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 32 + k := by
    rw [(frame32 op hk).1, BitVec.toNat_ofNat]; omega
  have spAt (k : Nat) (hk : k ≤ 32) : sp + 18446744073709551584#64 + BitVec.ofNat 64 k =
      BitVec.ofNat 64 (sp.toNat - 32 + k) := (frame32 op hk).2
  have spNat (k : Nat) (hk : k ≤ 32) : (sp + 18446744073709551584#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 32 + k := by
    rw [spAt k hk, BitVec.toNat_ofNat]; omega
  have e8 := slot 8 (by decide)
  have e16 := slot 16 (by decide)
  have e24 := slot 24 (by decide)
  have log0 : LogInW [⟨sp.toNat - 32, sp.toNat⟩] (proLog sp (regsAt c 8) (regsAt c 9) ra) := by
    simp only [proLog, LogInW, InsideW, e8, e16, e24, and_true]; omega
  let m1 := writeLog c.σ.mem (proLog sp (regsAt c 8) (regsAt c 9) ra)
  have outside1 : ∀ a, (a < sp.toNat - 32 ∨ sp.toNat ≤ a) → m1[a]? = c.σ.mem[a]? := fun a out =>
    frameOn_writeLog _ _ _ log0 a ⟨out, trivial⟩
  have low1 : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → (m1[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := fun a ha => by
    rw [outside1 a (Or.inl (by omega))]
  have saved1 : bytesT m1 (sp.toNat - 32 + 24) 8 = ra ∧ bytesT m1 (sp.toNat - 32 + 16) 8 = regsAt c 8 ∧
      bytesT m1 (sp.toNat - 32 + 8) 8 = regsAt c 9 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← e24]
      exact Gc.word_writeLog_at _ _ 2 _ _ (by simp [proLog]) (by simp [proLog, OutLRange])
    · rw [← e16]
      exact Gc.word_writeLog_at _ _ 0 _ _ (by simp [proLog]) (by
        simp only [proLog, List.drop, OutLRange, e8, e16, e24, and_true]; omega)
    · rw [← e8]
      exact Gc.word_writeLog_at _ _ 1 _ _ (by simp [proLog]) (by
        simp only [proLog, List.drop, OutLRange, e8, e24, and_true]; omega)
  -- the frame's words at `x`
  have frameX (k : Nat) (hk : k + 8 ≤ 32) : bytesT x.σ.mem (sp.toNat - 32 + k) 8 = bytesT m1 (sp.toNat - 32 + k) 8 :=
    word_observed _ fun i hi => by
      have up : sp.toNat - 32 ≤ sp.toNat - 32 + k + i := Nat.le_trans (Nat.le_add_right _ k) (Nat.le_add_right _ i)
      obtain ⟨nl, nf, seed⟩ := above_arena ops (m := m1) (H := H) (a := sp.toNat - 32 + k + i) (Nat.le_trans base up)
      exact act.kept _ nl nf (Or.inr up) seed
  -- the registers
  let R := regsAt x
  have r2 : R 2 = sp + 18446744073709551584#64 := regsAt_of act.stack
  have r8 : R 8 = v := regsAt_of act.s0
  have r9 : R 9 = r := regsAt_of act.s1
  have readW (k : Nat) (hk : k + 8 ≤ 32) (al : k % 8 = 0) : ReadWindow (R 2 + BitVec.ofNat 64 k) 8 := by
    rw [r2, spAt k (by omega)]
    have w := small.word (off := k) hk al
    rw [show nativeFrameBase sp 32 + k = sp.toNat - 32 + k by unfold nativeFrameBase; rfl] at w
    exact w.read
  have outL (k : Nat) (hk : k + 8 ≤ 32) :
      OutLRange ([((R 9).toNat, 8, R 8)].take 1) (R 2 + BitVec.ofNat 64 k).toNat 8 := by
    rw [r2, spNat k (by omega), r9]
    simp only [List.take, OutLRange, and_true]; omega
  have frameV (k : Nat) (hk : k + 8 ≤ 32) :
      bytesVal .ld (read8 x.σ.mem (R 2 + BitVec.ofNat 64 k).toNat) = bytesT m1 (sp.toNat - 32 + k) 8 := by
    rw [read8_value, r2, spNat k (by omega), frameX k hk]
  have outside : ImageOutside [((R 9).toNat, 8, R 8)] := OCaml.Vm.Sim.imageOutside_of_above fun e he => by
    simp only [List.mem_singleton] at he
    subst he
    rw [r9]
    have : Layout.sym_bss_end ≤ Vsa.Sim.DlHeap.heapStart := by decide
    exact Nat.le_trans this slotLow
  have regs : GHolds x.σ [(2, R 2), (8, R 8), (9, R 9), (10, R 10)] :=
    ⟨gpr_some (gpr_some_of act.stack), gpr_some (gpr_some_of act.s0), gpr_some (gpr_some_of act.s1),
      gpr_some act.a0, trivial⟩
  obtain ⟨d, run, p⟩ := (st x ra R act.leaf regs (by rw [r9]; exact h.slot) (readW 24 (by decide) (by decide))
    (outL 24 (by decide)) (readW 16 (by decide) (by decide)) (outL 16 (by decide)) (readW 8 (by decide) (by decide))
    (outL 8 (by decide)) outside ((frameV 24 (by decide)).trans saved1.1) h.leaf.aligned).run x ⟨pc0, rfl⟩
  -- the store
  have memD : d.σ.mem = writeLog x.σ.mem [(r.toNat, 8, v)] := by rw [p.memory, r9, r8]
  have slotLog : LogInW [⟨r.toNat, r.toNat + 8⟩] [(r.toNat, 8, v)] := by
    simp only [LogInW, InsideW, and_true]; omega
  have offSlot : ∀ a, (a < r.toNat ∨ r.toNat + 8 ≤ a) → (d.σ.mem[a]?).getD 0 = (x.σ.mem[a]?).getD 0 :=
    fun a out => by rw [memD, frameOn_writeLog _ _ _ slotLog a ⟨out, trivial⟩]
  have listsEq : ∀ a, ListsFoot Shape foot m1 a ↔ ListsFoot Shape foot c.σ.mem a :=
    listsFoot_low ops h.roots low1
  have inSlot : ∀ a, r.toNat ≤ a → a < r.toNat + 8 →
      ¬ ListsFoot Shape foot m1 a ∧ ¬ VsaIris.VsaHeap.vsaFoot H a := fun a lo hi => by
    obtain ⟨nl, nf⟩ := h.slotApart a lo hi
    exact ⟨fun l => nl ((listsEq a).1 l), nf⟩
  have keepD : ∀ a, (ListsFoot Shape foot m1 a ∨ VsaIris.VsaHeap.vsaFoot H a) →
      (d.σ.mem[a]?).getD 0 = (x.σ.mem[a]?).getD 0 := fun a f => by
    apply offSlot a
    rcases Nat.lt_or_ge a r.toNat with lo | lo
    · exact Or.inl lo
    rcases Nat.lt_or_ge a (r.toNat + 8) with hi | hi
    · obtain ⟨nl, nf⟩ := inSlot a lo hi
      rcases f with l | v'
      · exact (nl l).elim
      · exact (nf v').elim
    · exact Or.inr hi
  have keep (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [1, 2, 8, 9]) : gprGet d.σ n = gprGet x.σ n :=
    p.gpr_frame (by decide) n lo hi out
  have gp : gpr d 3 = gpr c 3 := (keep 3 (by decide) (by decide) (by decide)).trans act.gp
  obtain ⟨H', cap', hr, hb⟩ := act.heap
  refine ⟨d, run0.trans run,
    { good := p.good
      image := p.image
      minstret := p.minstret
      tick := p.tick
      pc := p.pc
      stack := holds_at p.regs rfl (by
        rw [r2, BitVec.add_assoc, show (18446744073709551584#64 : BitVec 64) + 32#64 = 0#64 by decide,
          BitVec.add_zero])
      saved := fun n hn => ?_
      gprs := GprsKept.of_steps gprsPersist (run0.trans run) gp
      output := p.output.trans act.output
      heap := ⟨H', cap', OCaml.Vm.Gc.HeapReady.frame_read hr fun a _ reads => by
          rcases reads with rd | pin
          · exact keepD a ((hb a rd.1).symm)
          · exact offSlot a (Or.inl (Nat.lt_of_lt_of_le (HeapPinned.low pin) slotLow)),
        fun a f => (hb a f).imp id (listsEq a).1⟩
      roots := ⟨ys', os', act.roots.keep ops (fun sk cells list sh a f => keepD a
          (act.feet sk cells list sh a f)), memb, place⟩
      slot := by rw [memD]; exact Gc.word_writeLog_at _ _ 0 _ _ rfl trivial
      kept := fun a nl nf out win seed => by
        have win' : a < sp.toNat - 32 - opStack ∨ sp.toNat - 32 ≤ a := by
          rcases win with w | w
          · exact Or.inl (by rw [Nat.sub_sub]; exact w)
          · exact Or.inr (Nat.le_trans (Nat.sub_le _ _) w)
        have out1 : a < sp.toNat - 32 ∨ sp.toNat ≤ a := by
          rcases win with w | w
          · exact Or.inl (Nat.lt_of_lt_of_le w (Nat.sub_le_sub_left (Nat.le_add_right 32 opStack) _))
          · exact Or.inr w
        rw [offSlot a out, act.kept a (fun l => nl ((listsEq a).1 l)) nf win' seed, outside1 a out1] }⟩
  by_cases e8 : n = 8
  · subst e8
    exact (holds_at p.regs rfl ((frameV 16 (by decide)).trans saved1.2.1)).trans (gpr_some h.s0).symm
  by_cases e9 : n = 9
  · subst e9
    exact (holds_at p.regs rfl ((frameV 8 (by decide)).trans saved1.2.2)).trans (gpr_some h.s1).symm
  have hr' : n ∈ [18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega
  have b : 18 ≤ n ∧ n ≤ 27 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'; omega
  exact (keep n (by omega) (by omega) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)).trans
    (act.saved n hr')

end OCaml.Vm.Primitives.Named.ModifyRoot
