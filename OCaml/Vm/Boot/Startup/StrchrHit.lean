import OCaml.Vm.Boot.Startup.StrchrMiss
import OCaml.Vm.Boot.Startup.StrchrHitNormalized
import OCaml.Vm.Boot.Startup.StrchrHitImage
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

/-- The low byte of `slashPattern ^^^ x` is zero when `x`'s low byte is '/'. -/
theorem slash_xor_low {x : BitVec 64} (hx : x.toNat % 256 = 47) : (slashPattern ^^^ x).toNat % 256 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < 8
  · have hxi : x.toNat.testBit i = (47 : Nat).testBit i := by
      rw [← hx, show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow]; simp [hi]
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    simp only [hi, decide_true, Bool.true_and, BitVec.toNat_xor, Nat.testBit_xor, hxi]
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp [hi]

/-- A word whose first byte is '/' always hits the first test. -/
theorem setupTest_low_slash {x : BitVec 64} (hx : x.toNat % 256 = 47) : setupTest x ≠ 0#64 := by
  have low := slash_xor_low hx
  intro z
  have bit := congrArg (fun v : BitVec 64 => v.getLsbD 7) z
  simp only [setupTest, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor] at bit
  have sum := sum_bit7 (slashPattern ^^^ x) lowOnes low (by decide)
  have zero := bit7_zero (slashPattern ^^^ x) low
  simp only [BitVec.getLsbD_xor] at sum zero
  rw [sum] at bit
  generalize (x + lowOnes).getLsbD 7 = t at bit
  generalize hs : slashPattern.getLsbD 7 = s at bit zero
  generalize hx7 : x.getLsbD 7 = u at bit zero
  cases t <;> cases s <;> cases u <;> revert bit zero <;> decide

/-- The scanned byte is '/': return its address. -/
theorem strchr_hit (c : Config) (q ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, q), (13, 47#64), (15, nameByteWord 47#8), (1, ra)]) :
    FnSummary 0x800407d0#64 (fun e => e = c)
      (WriteRegistersPost [] [] c ra q [(10, q), (13, 47#64), (15, nameByteWord 47#8), (1, ra)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (strchrX07d0TSeg ++ strchrX0870Seg) 0x800407d0#64
        [(10, q), (13, 47#64), (15, nameByteWord 47#8), (1, ra)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 13, 15, 1]; decide
      shape := by change ChainOK _ [10, 13, 15, 1] _; decide
      tick := leaf.tick
      facts := by
        have code := strchrTail_code leaf.image
        have code2 := strchrHit_code leaf.image
        chain_facts code with "Vsa.Sim.Code.strchr_at_"
        · change guardB bop.BEQ 47#64 (nameByteWord 47#8) = true
          decide
        · change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [ret_tgt ra leaf.aligned]
          exact leaf.aligned }))
  · rfl
  · change Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1 = ra
    rw [ret_tgt ra leaf.aligned]
  · rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

/-- `strchr(s, '/')` returned `s`. -/
structure StrchrHitDone (a ra : BitVec 64) (before after : Config) : Prop extends LeafInput ra after where
  pc : PCAt ra after
  result : gprGet after.σ 10 = some a
  present : GprPresent after.σ
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : StrchrFrame before after

/-- `strchr(s, '/')` for an 8-aligned `s` whose first byte is '/'. -/
theorem strchr_slash_first (c : Config) (a ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(11, 47#64), (10, a), (1, ra)]) (present : GprPresent c.σ)
    (aligned : a.toNat % 8 = 0) (window : ReadWindow a 8) (slash : (c.σ.mem[a.toNat]?).getD 0 = 47#8) :
    FnSummary 0x80040704#64 (fun e => e = c) (StrchrHitDone a ra c) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨e0, run1, entered⟩ := (strchr_entry c a ra leaf regs).run c ⟨pc, rfl⟩
  have pc0 : PCAt 0x8004072c#64 e0 := by have p := entered.pc; rw [ite_cond_eq_true _ _ (eq_true aligned)] at p; exact p
  have leaf0 : LeafInput ra e0 := ⟨entered.good, entered.image, entered.minstret,
    gholds_lookup (n := 1) _ entered.regs (by rfl), leaf.aligned, entered.tick⟩
  obtain ⟨l, run2, loaded⟩ := (strchr_load e0 a ra leaf0
    ⟨gholds_lookup (n := 11) _ entered.regs (by rfl), gholds_lookup (n := 10) _ entered.regs (by rfl),
      gholds_lookup (n := 13) _ entered.regs (by rfl), gholds_lookup (n := 1) _ entered.regs (by rfl), trivial⟩
    window).run e0 ⟨pc0, rfl⟩
  have leafL : LeafInput ra l := ⟨loaded.good, loaded.image, loaded.minstret,
    gholds_lookup (n := 1) _ loaded.regs (by rfl), leaf.aligned, loaded.tick⟩
  obtain ⟨m1, run3, masked⟩ := (strchr_masks l a ra _ leafL loaded.regs).run l ⟨loaded.pc, rfl⟩
  have leafM : LeafInput ra m1 := ⟨masked.good, masked.image, masked.minstret,
    gholds_lookup (n := 1) _ masked.regs (by rfl), leaf.aligned, masked.tick⟩
  obtain ⟨t, run4, tested⟩ := (strchr_test m1 a ra _ leafM masked.regs).run m1 ⟨masked.pc, rfl⟩
  have mem0 : e0.σ.mem = c.σ.mem := entered.memory
  have memT : t.σ.mem = c.σ.mem := (show t.σ.mem = m1.σ.mem from tested.memory).trans
    ((show m1.σ.mem = l.σ.mem from masked.memory).trans ((show l.σ.mem = e0.σ.mem from loaded.memory).trans mem0))
  have low : (bytesT e0.σ.mem a.toNat 8).toNat % 256 = 47 := by
    rw [mem0, bytesT_eight_eq]
    simp only [bytesT8]
    rw [slash, BitVec.append_eq, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (by decide), Nat.shiftLeft_eq]
    simp only [BitVec.toNat_ofNat]
    omega
  have hit : setupTest (bytesT e0.σ.mem a.toNat 8) ≠ 0#64 := setupTest_low_slash low
  have pcT : PCAt 0x800407d8#64 t := by have p := tested.pc; rw [ite_cond_eq_false _ _ (eq_false hit)] at p; exact p
  have leafT : LeafInput ra t := ⟨tested.good, tested.image, tested.minstret,
    gholds_lookup (n := 1) _ tested.regs (by rfl), leaf.aligned, tested.tick⟩
  have w1 : ReadWindow a 1 := by
    refine ⟨window.lower, by have := window.upper; omega, ?_⟩
    rcases window.htif with b | h
    · exact Or.inl (by omega)
    · exact Or.inr h
  obtain ⟨s1, run5, scan⟩ := (strchr_scan_first t a ra 47#8 leafT
    ⟨gholds_lookup (n := 10) _ tested.regs (by rfl), gholds_lookup (n := 13) _ tested.regs (by rfl), trivial⟩
    w1 (by rw [memT]; exact slash)).run t ⟨pcT, rfl⟩
  have pcS : PCAt 0x800407d0#64 s1 := by have p := scan.pc; rw [ite_cond_eq_false _ _ (eq_false (by decide))] at p; exact p
  have leafS : LeafInput ra s1 := ⟨scan.good, scan.image, scan.minstret,
    (scan.frame .x1 (by decide) (by decide)).trans (gholds_lookup (n := 1) _ tested.regs (by rfl)),
    leaf.aligned, scan.tick⟩
  obtain ⟨d, run6, hitPost⟩ := (strchr_hit s1 a ra leafS
    ⟨gholds_lookup (n := 10) _ scan.regs (by rfl), gholds_lookup (n := 13) _ scan.regs (by rfl),
      gholds_lookup (n := 15) _ scan.regs (by rfl), leafS.raReg, trivial⟩).run s1 ⟨pcS, rfl⟩
  have presT := tested.present (masked.present (loaded.present (entered.present present (by decide)
    (by simp only [keysG]; decide)) (by decide) (by simp only [strchrLoaded, keysG]; decide)) (by decide)
    (by simp only [strchrMasked, keysG]; decide)) (by decide) (by simp only [strchrTested, keysG]; decide)
  exact ⟨d, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))), {
    toLeafInput := ⟨hitPost.good, hitPost.image, hitPost.minstret, gholds_lookup (n := 1) _ hitPost.regs (by rfl),
      leaf.aligned, hitPost.tick⟩
    pc := hitPost.pc
    result := gholds_lookup (n := 10) _ hitPost.regs (by rfl)
    present := hitPost.present (scan.present presT (by decide) (by simp only [keysG]; decide)) (by decide)
      (by simp only [keysG]; decide)
    memory := (show d.σ.mem = s1.σ.mem from hitPost.memory).trans ((show s1.σ.mem = t.σ.mem from scan.memory).trans
      memT)
    output := hitPost.output.trans (scan.output.trans (tested.output.trans (masked.output.trans (loaded.output.trans
      entered.output))))
    frame := (StrchrFrame.of_post entered (by decide)).trans ((StrchrFrame.of_post loaded (by decide)).trans
      ((StrchrFrame.of_post masked (by decide)).trans ((StrchrFrame.of_post tested (by decide)).trans
        ((StrchrFrame.of_post scan (by decide)).trans (StrchrFrame.of_post hitPost (by decide)))))) }⟩
end OCaml.Vm.Boot.Startup
