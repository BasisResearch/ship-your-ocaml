import OCaml.Vm.Boot.Startup.InitMergeSteps
import OCaml.Vm.Boot.Startup.MinorHeap
import Vsa.Sim.IndexedLoop
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! bf_init_merge over 16 empty small free lists, folded by `indexedLoop`. -/

/-- A window of runtime globals that misses the allocator's text and impure
word, its globals, `Caml_state` and the pool. -/
theorem globalWindow_ok {H : List (Nat × Nat)} {lo hi : Nat} (text : Image.textBase + Image.textSize ≤ lo)
    (impure : hi ≤ allocatorImpureAddr ∨ allocatorImpureAddr + 8 ≤ lo) (heap : hi ≤ heapStart)
    (globals : ∀ a, lo ≤ a → a < hi → ¬ allocGlobal a)
    (domain : hi ≤ Layout.sym_Caml_state ∨ Layout.sym_Caml_state + 8 ≤ lo)
    (pool : hi ≤ Layout.sym_pool ∨ Layout.sym_pool + 8 ≤ lo) : WindowsOk H [⟨lo, hi⟩] := by
  refine ⟨fun pin member => ?_, ?_, ?_, fun a foot => ?_⟩
  · have source := allocator_sources pin member
    unfold AllocatorByteSource at source
    simp only [OutW, and_true]
    split at source <;> omega
  · simp only [OutWRange, and_true]; omega
  · simp only [OutWRange, and_true]; omega
  · simp only [OutW, and_true]
    rcases foot with global | ⟨above, _, _⟩
    · by_cases inside : lo ≤ a ∧ a < hi
      · exact absurd global (globals a inside.1 inside.2)
      · omega
    · omega

/-- `bf_small_fl[1..16]`. -/
def smallListsWindow : W := ⟨0x800662e8, 0x800663e8⟩

theorem smallLists_ok {H : List (Nat × Nat)} : WindowsOk H [smallListsWindow] := by
  refine ⟨fun pin member => ?_, by simp only [OutWRange, smallListsWindow]; decide,
    by simp only [OutWRange, smallListsWindow]; decide, fun a foot => ?_⟩
  · have source := allocator_sources pin member
    unfold AllocatorByteSource at source
    simp only [OutW, smallListsWindow, and_true]
    split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr] at * <;> omega
  · simp only [OutW, smallListsWindow, and_true]
    rcases foot with global | ⟨above, _, _⟩
    · unfold allocGlobal InRange at global; omega
    · unfold heapStart at above; omega

theorem smallListLog_in (k : Nat) (hk : k < 16) : LogInW [smallListsWindow] (smallListLog k) := by
  have a0 := smallList_nat k hk 0 (by decide)
  have a8 := smallList_nat k hk 8 (by decide)
  rw [show smallList k + BitVec.ofNat 64 0 = smallList k by simp] at a0
  simp only [smallListLog, LogInW, InsideW, smallListsWindow, a0,
    show smallList k + 8#64 = smallList k + BitVec.ofNat 64 8 from rfl, a8, or_false, and_true]
  omega

theorem smallList_apart {j k : Nat} (hj : j < 16) (hk : k < 16) (ne : j ≠ k) :
    OutLRange (smallListLog k) (smallList j).toNat 8 := by
  have aj := smallList_nat j hj 0 (by decide)
  have a0 := smallList_nat k hk 0 (by decide)
  have a8 := smallList_nat k hk 8 (by decide)
  rw [show smallList j + BitVec.ofNat 64 0 = smallList j by simp] at aj
  rw [show smallList k + BitVec.ofNat 64 0 = smallList k by simp] at a0
  simp only [smallListLog, OutLRange, a0, show smallList k + 8#64 = smallList k + BitVec.ofNat 64 8 from rfl, a8, aj,
    and_true]
  omega

theorem smallList_apart8 {j k : Nat} (hj : j < 16) (hk : k < 16) (ne : j ≠ k) :
    OutLRange (smallListLog k) (smallList j + 8#64).toNat 8 := by
  have aj := smallList_nat j hj 8 (by decide)
  have a0 := smallList_nat k hk 0 (by decide)
  have a8 := smallList_nat k hk 8 (by decide)
  rw [show smallList k + BitVec.ofNat 64 0 = smallList k by simp] at a0
  simp only [smallListLog, OutLRange, a0, show smallList k + 8#64 = smallList k + BitVec.ofNat 64 8 from rfl, a8,
    show smallList j + 8#64 = smallList j + BitVec.ofNat 64 8 from rfl, aj, and_true]
  omega

/-- `bf_small_fl[k + 1]` after the reset. -/
structure ListReset (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) : Prop where
  free : bytesT m (smallList k).toNat 8 = 0#64
  merge : bytesT m (smallList k + 8#64).toNat 8 = smallList k

/-- The loop before list `k`. -/
structure MergeAt (H : List (Nat × Nat)) (capacity : Nat) (sp ra map : BitVec 64) (start : Config) (k : Nat)
    (d : Config) : Prop where
  pc : PCAt (if k < 16 then 0x800061d4#64 else 0x80006254#64) d
  regs : GHolds d.σ [(16, smallList k), (17, BitVec.ofNat 64 k), (6, map &&& clearLow k), (30, 1#64), (28, 16#64),
    (10, 512#64)]
  someEmptied : 0 < k → gprGet d.σ 29 = some 1#64
  ready : RuntimeReady H capacity sp ra d
  bound : k ≤ 16
  pending : ∀ j, k ≤ j → j < 16 → bytesT d.σ.mem (smallList j).toNat 8 = 0#64
  done : ∀ j, j < k → ListReset d.σ.mem j
  kept : ∀ x, OutW [smallListsWindow] x → (d.σ.mem[x]?).getD 0 = (start.σ.mem[x]?).getD 0
  saved : ∀ r, 1 ≤ r → r ≤ 31 → r ∉ [13, 15, 17, 6, 29, 16] → gprGet d.σ r = gprGet start.σ r

theorem MergeAt.index {H capacity sp ra map start k d} (A : MergeAt H capacity sp ra map start k d) :
    ((gprGet d.σ 17).getD 0).toNat = k := by
  rw [gholds_lookup (n := 17) _ A.regs rfl]
  have := A.bound
  simp only [Option.getD_some, BitVec.toNat_ofNat]
  omega

theorem merge_step {H capacity sp ra map start} (k : Nat) (d : Config)
    (A : MergeAt H capacity sp ra map start k d) (lt : k < 16) :
    ∃ e, Steps d e ∧ MergeAt H capacity sp ra map start (k + 1) e := by
  have pc : PCAt 0x800061d4#64 d := by have := A.pc; simp only [lt, ite_true] at this; exact this
  obtain ⟨e, run, p⟩ := (init_merge_step d ra (map &&& clearLow k) k lt A.ready.toLeafInput A.regs
    (A.pending k (Nat.le_refl _) lt)).run d ⟨pc, rfl⟩
  have keep (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [13, 15, 17, 6, 29, 16]) : gprGet e.σ r = gprGet d.σ r :=
    p.toEffectPost.gpr_frame (by decide) r lo hi out
  have W := smallLists_ok (H := H)
  refine ⟨e, run, {
    pc := p.pc
    regs := ⟨gholds_lookup (n := 16) _ p.regs rfl, gholds_lookup (n := 17) _ p.regs rfl,
      by rw [gholds_lookup (n := 6) _ p.regs rfl, BitVec.and_assoc, clearLow_succ k lt],
      gholds_lookup (n := 30) _ p.regs rfl, gholds_lookup (n := 28) _ p.regs rfl, gholds_lookup (n := 10) _ p.regs rfl,
      trivial⟩
    someEmptied := fun _ => gholds_lookup (n := 29) _ p.regs rfl
    ready := A.ready.window_log p (by decide) (by simp only [keysG]; decide) (by decide)
      ((keep 2 (by decide) (by decide) (by decide)).trans A.ready.stack)
      ((keep 1 (by decide) (by decide) (by decide)).trans A.ready.raReg) A.ready.aligned (smallListLog_in k lt)
      W.pins W.domain W.pool W.heap
    bound := by omega
    pending := fun j lo hi => by
      rw [p.memory, bytesT_writeLog_out _ (smallList_apart hi lt (by omega))]
      exact A.pending j (by omega) hi
    done := fun j hj => by
      by_cases same : j = k
      · subst same
        rw [p.memory]
        exact ⟨word_writeLog_at _ _ 0 _ _ rfl (by
            have a := smallList_apart8 (j := j) (k := j) lt lt
            simp only [smallListLog, List.drop, OutLRange, and_true]
            have a0 := smallList_nat j lt 0 (by decide)
            have a8 := smallList_nat j lt 8 (by decide)
            rw [show smallList j + BitVec.ofNat 64 0 = smallList j by simp] at a0
            rw [show smallList j + 8#64 = smallList j + BitVec.ofNat 64 8 from rfl, a8, a0]
            omega),
          word_writeLog_at _ _ 1 _ _ rfl trivial⟩
      · have r := A.done j (by omega)
        rw [p.memory]
        exact ⟨by rw [bytesT_writeLog_out _ (smallList_apart (by omega) lt same)]; exact r.free,
          by rw [bytesT_writeLog_out _ (smallList_apart8 (by omega) lt same)]; exact r.merge⟩
    kept := fun x out => by
      rw [p.memory, frameOn_writeLog _ _ _ (smallListLog_in k lt) x out]
      exact A.kept x out
    saved := fun r lo hi out => (keep r lo hi out).trans (A.saved r lo hi out) }⟩

theorem merge_loop {H capacity sp ra map start} (A : MergeAt H capacity sp ra map start 0 start) :
    ∃ d, Steps start d ∧ MergeAt H capacity sp ra map start 16 d :=
  indexedLoop (I := MergeAt H capacity sp ra map start) (index := fun d => ((gprGet d.σ 17).getD 0).toNat)
    (start := 0) (count := 16) (fun _ _ h => h.index) (fun _ _ h => h.bound)
    (fun k d ⟨h, lt⟩ => merge_step k d h lt) start A

/-- `caml_fl_merge`. -/
def flMergeAddr : Nat := 0x80064a38

/-- bf_init_merge returned: every small list is reset, `caml_fl_merge` is
NULL and the map has lost bits 0–15. -/
structure InitMerged (H : List (Nat × Nat)) (capacity : Nat) (sp ra map : BitVec 64) (before after : Config) : Prop where
  pc : PCAt ra after
  ready : RuntimeReady H capacity sp ra after
  lists : ∀ j, j < 16 → ListReset after.σ.mem j
  flMerge : bytesT after.σ.mem flMergeAddr 8 = 0#64
  kept : ∀ x, OutW [smallListsWindow, ⟨flMergeAddr, flMergeAddr + 8⟩, ⟨smallMapAddr, smallMapAddr + 4⟩] x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  saved : ∀ k ∈ abiSaved, gprGet after.σ k = gprGet before.σ k

theorem init_merge (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (sp ra map v : BitVec 64)
    (pc : PCAt 0x800061a0#64 c) (ready : RuntimeReady H capacity sp ra c) (a0 : gprGet c.σ 10 = some v)
    (small : bytesVal .lw (read4 c.σ.mem smallMapAddr) = map)
    (empty : ∀ j, j < 16 → bytesT c.σ.mem (smallList j).toNat 8 = 0#64) :
    ∃ d, Steps c d ∧ InitMerged H capacity sp ra map c d := by
  obtain ⟨d1, run1, p1⟩ := (init_merge_entry c ra v map ready.toLeafInput ⟨a0, trivial⟩ small).run c ⟨pc, rfl⟩
  have k1 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [6, 15, 16, 17, 29, 11, 10, 30, 28]) :
      gprGet d1.σ r = gprGet c.σ r :=
    p1.toEffectPost.gpr_frame (by decide) r lo hi out
  have W1 := globalWindow_ok (H := H) (lo := flMergeAddr) (hi := flMergeAddr + 8) (by decide) (by decide) (by decide)
    (fun a lo hi => by unfold flMergeAddr at lo hi; unfold allocGlobal InRange; omega) (by decide) (by decide)
  have ready1 := ready.window_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    ((k1 2 (by decide) (by decide) (by decide)).trans ready.stack)
    ((k1 1 (by decide) (by decide) (by decide)).trans ready.raReg) ready.aligned
    (by simp only [LogInW, InsideW, flMergeAddr]; decide) W1.pins W1.domain W1.pool W1.heap
  have below (j : Nat) (hj : j < 16) : OutLRange [(0x80064a38, 8, 0#64)] (smallList j).toNat 8 := by
    have a := smallList_nat j hj 0 (by decide)
    rw [show smallList j + BitVec.ofNat 64 0 = smallList j by simp] at a
    simp only [OutLRange, a, and_true]; omega
  obtain ⟨d2, run2, L⟩ := merge_loop (start := d1) (map := map) {
    pc := p1.pc
    regs := ⟨gholds_lookup (n := 16) _ p1.regs rfl, gholds_lookup (n := 17) _ p1.regs rfl,
      by rw [gholds_lookup (n := 6) _ p1.regs rfl, show clearLow 0 = BitVec.allOnes 64 by decide, BitVec.and_allOnes],
      gholds_lookup (n := 30) _ p1.regs rfl, gholds_lookup (n := 28) _ p1.regs rfl, gholds_lookup (n := 10) _ p1.regs rfl,
      trivial⟩
    someEmptied := fun h => absurd h (Nat.lt_irrefl 0)
    ready := ready1
    bound := Nat.zero_le _
    pending := fun j _ hj => by rw [p1.memory, bytesT_writeLog_out _ (below j hj)]; exact empty j hj
    done := fun j hj => absurd hj (Nat.not_lt_zero j)
    kept := fun _ _ => rfl
    saved := fun _ _ _ _ => rfl }
  have pc2 : PCAt 0x80006254#64 d2 := by have := L.pc; simp only [Nat.lt_irrefl, ite_false] at this; exact this
  obtain ⟨d3, run3, p3⟩ := (init_merge_tail d2 ra (map &&& clearLow 16) 512#64 L.ready.toLeafInput
    ⟨L.someEmptied (by decide), gholds_lookup (n := 6) _ L.regs rfl, L.ready.raReg,
      gholds_lookup (n := 10) _ L.regs rfl, trivial⟩).run d2 ⟨pc2, rfl⟩
  have k3 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [15]) : gprGet d3.σ r = gprGet d2.σ r :=
    p3.toEffectPost.gpr_frame (by decide) r lo hi out
  have W3 := globalWindow_ok (H := H) (lo := smallMapAddr) (hi := smallMapAddr + 4) (by decide) (by decide) (by decide)
    (fun a lo hi => by unfold smallMapAddr at lo hi; unfold allocGlobal InRange; omega) (by decide) (by decide)
  have mapOut (j : Nat) (hj : j < 16) (off : Nat) (h : off ≤ 8) :
      OutLRange [(smallMapAddr, 4, map &&& clearLow 16)] (smallList j + BitVec.ofNat 64 off).toNat 8 := by
    rw [smallList_nat j hj off h]; simp only [OutLRange, smallMapAddr, and_true]; omega
  refine ⟨d3, run1.trans (run2.trans run3), {
    pc := p3.pc
    ready := L.ready.window_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
      ((k3 2 (by decide) (by decide) (by decide)).trans L.ready.stack)
      ((k3 1 (by decide) (by decide) (by decide)).trans L.ready.raReg) L.ready.aligned
      (by simp only [LogInW, InsideW, smallMapAddr]; decide) W3.pins W3.domain W3.pool W3.heap
    lists := fun j hj => by
      have r := L.done j hj
      have m0 := mapOut j hj 0 (by decide)
      rw [show smallList j + BitVec.ofNat 64 0 = smallList j by simp] at m0
      exact ⟨by rw [p3.memory, bytesT_writeLog_out _ m0]; exact r.free,
        by rw [p3.memory, bytesT_writeLog_out _ (mapOut j hj 8 (by decide))]; exact r.merge⟩
    flMerge := by
      rw [p3.memory, bytesT_writeLog_out _ (by simp only [OutLRange, smallMapAddr, flMergeAddr]; decide),
        word_observed (m := d1.σ.mem) _ fun i hi => L.kept _ (by
          simp only [OutW, smallListsWindow, flMergeAddr, and_true]; omega), p1.memory]
      exact word_writeLog_at _ _ 0 _ _ rfl trivial
    kept := fun x out => by
      simp only [OutW, and_true] at out
      obtain ⟨lists, merge, smallMap⟩ := out
      rw [p3.memory, writeLog_out _ _ _ (by simp only [OutL, and_true]; exact smallMap), L.kept x
        (by simp only [OutW, and_true]; exact lists), p1.memory, writeLog_out _ _ _ (by
          simp only [OutL, flMergeAddr, and_true]; exact merge)]
    saved := fun k member => by
      have range : 1 ≤ k ∧ k ≤ 31 := by simp [abiSaved] at member; omega
      have out (L : List Nat) (low : ∀ m ∈ L, m ∉ abiSaved) : k ∉ L := fun mem => low k mem member
      rw [k3 k range.1 range.2 (out _ (by decide)), L.saved k range.1 range.2 (out _ (by decide)),
        k1 k range.1 range.2 (out _ (by decide))] }⟩
end OCaml.Vm.Boot.Startup
