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
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

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
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : Config) : Prop where
  pc : PCAt (if k < 256 then 0x800044d4#64 else 0x800044f0#64) d
  regs : GHolds d.σ [(11, base), (15, atomCursor k), (14, atomHeader k), (12, BitVec.ofNat 64 atomTableAddr),
    (10, a0)]
  ready : RuntimeReady H capacity sp ra d
  bound : k ≤ 256
  published : bytesT d.σ.mem atomTableAddr 8 = base
  atoms : ∀ j, j < k → bytesT d.σ.mem (base.toNat + 8 * j) 8 = atomHeader j
  kept : ∀ x, x < base.toNat ∨ base.toNat + 2048 ≤ x → (d.σ.mem[x]?).getD 0 = (m0[x]?).getD 0

theorem AtomAt.index {H capacity sp ra base a0 m0 k d} (A : AtomAt H capacity sp ra base a0 m0 k d) :
    ((gprGet d.σ 15).getD 0).toNat / 8 = k := by
  have bound := A.bound
  rw [gholds_lookup (n := 15) _ A.regs rfl]
  simp only [Option.getD_some, atomCursor, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem atom_at_step {H capacity sp ra base a0 m0 q n} (S : AtomSpan H base q n) (k : Nat) (d : Config)
    (A : AtomAt H capacity sp ra base a0 m0 k d) (lt : k < 256) :
    ∃ e, Steps d e ∧ AtomAt H capacity sp ra base a0 m0 (k + 1) e := by
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
      (if k + 1 < 256 then 0x800044d4#64 else 0x800044f0#64)) : ∃ e, Steps d e ∧ AtomAt H capacity sp ra base a0 m0 (k + 1) e := by
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
        exact A.kept x out }⟩
  by_cases more : k + 1 < 256
  · exact go (by simp only [more, ite_true]; exact .more more)
  · exact go (by simp only [more, ite_false]; exact .last (by omega))

theorem atom_loop {H capacity sp ra base a0 m0 q n} (S : AtomSpan H base q n) {start : Config}
    (A : AtomAt H capacity sp ra base a0 m0 0 start) :
    ∃ d, Steps start d ∧ AtomAt H capacity sp ra base a0 m0 256 d :=
  indexedLoop (I := AtomAt H capacity sp ra base a0 m0) (index := fun d => ((gprGet d.σ 15).getD 0).toNat / 8)
    (start := 0) (count := 256) (fun _ _ h => h.index) (fun _ _ h => h.bound)
    (fun k d ⟨h, lt⟩ => atom_at_step S k d h lt) start A

end OCaml.Vm.Boot.Startup
