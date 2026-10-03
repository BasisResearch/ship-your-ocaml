import OCaml.Vm.Boot.Startup.MallocBootAligned
namespace OCaml.Vm.Boot.Startup
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The source initializes one contiguous top chunk before its statistics pass. -/
def mallocTopLog : List WEntry :=
  [(topAddr, 8, BitVec.ofNat 64 heapStart), (heapStart + 8, 8, 3777#64),
   (mallinfoAddr, 8, 3776#64)]

structure MallocBootTop (C : MCtx) (before : Mem) (R : Nat → BitVec 64) (m : Mem) : Prop where
  frame : MFrame C R m
  a2 : R 12 = 3777#64
  a4 : R 14 = 944#64
  a6 : R 16 = BitVec.ofNat 64 avAddr
  t3 : R 28 = BitVec.ofNat 64 heapStart
  memory : m = writeLog before mallocTopLog

#ix_piece mallocTop_p1 {C : MCtx} (O : WOK C) {R : Nat → BitVec 64} {before m : Mem}
    (p : MallocBootAligned C before R m) (stackHigh : heapEnd + mHead ≤ C.s.toNat)
    (empty : C.H = [])
    (next : ∀ R' m', MallocBootTop C m R' m' → AW C.live C.S C.Q 0x800379e8#64 R' m') :
    AW C.live C.S C.Q 0x80037d18#64 R m by
  have hlo := O.sp.lo
  have hhi := O.sp.hi
  have hal := O.sp.align
  have sp := p.frame.sp
  have spNat : (R 2).toNat = C.s.toNat - 96 := by rw [sp]; sx_addr
  have spAlign : (R 2).toNat % 16 = 0 := by rw [spNat]; omega
  unfold mHead Vsa.Sim.tohostAddr Vsa.Sim.LibraryLayout.tohostAddr at hlo
  have addr (off : Nat) (ho : off ≤ 96) : C.s.toNat - 96 + off = C.s.toNat - (96 - off) := by
    unfold heapEnd mHead at stackHigh
    omega
  have slot8 := p.spill_value stackHigh 8 8 (2800#64) (by decide)
    (by rw [addr 8 (by decide)]; rfl)
    (by simp only [mallocAlignLog, List.drop, OutLRange, and_true]; omega)
  have slot24 := p.spill_value stackHigh 24 7 (BitVec.ofNat 64 heapStart) (by decide)
    (by rw [addr 24 (by decide)]; rfl)
    (by simp only [mallocAlignLog, List.drop, OutLRange, and_true]; omega)
  have slot32 := p.spill_value stackHigh 32 6 (0#64) (by decide)
    (by rw [addr 32 (by decide)]; rfl)
    (by simp only [mallocAlignLog, List.drop, OutLRange, and_true]; omega)
  have slot40 := p.spill_value stackHigh 40 5 (944#64) (by decide)
    (by rw [addr 40 (by decide)]; rfl)
    (by simp only [mallocAlignLog, List.drop, OutLRange, and_true]; omega)
  have slot48 := p.spill_value stackHigh 48 4 (BitVec.ofNat 64 avAddr) (by decide)
    (by rw [addr 48 (by decide)]; rfl)
    (by simp only [mallocAlignLog, List.drop, OutLRange, and_true]; omega)
  have slot56 := p.spill_value stackHigh 56 3 (BitVec.ofNat 64 avAddr) (by decide)
    (by rw [addr 56 (by decide)]; rfl)
    (by simp only [mallocAlignLog, List.drop, OutLRange, and_true]; omega)
  have slot64 := p.spill_value stackHigh 64 2 (BitVec.ofNat 64 mallinfoAddr) (by decide)
    (by rw [addr 64 (by decide)]; rfl)
    (by simp only [mallocAlignLog, List.drop, OutLRange, and_true]; omega)
  have result := p.a0
  have resultNat : (R 10).toNat = heapStart + 976 := congrArg BitVec.toNat p.a0
  unfold heapStart at resultNat
  rw [← upd_self_eq result]
  sx_run [10] O.live at 0x80037d38
  simp (disch := sx_addr) only [ldv_at slot8, ldv_at slot24, ldv_at slot32,
    ldv_at slot40, ldv_at slot48, ldv_at slot56, ldv_at slot64]
  simp only [heapStart, avAddr, mallinfoAddr]
  sx_run [1] O.live at 0x80037d3c
  refine st_80037d3c O.live (fun _ => ?_) (fun bad => False.elim (bad (by sx_norm; decide)))
  sx_run [1] O.live at 0x80037990
  have stat : read64 m mallinfoAddr = some 976 := by
    rw [p.read _ (by intro k hk; unfold SbrkW brkAddr mallinfoAddr heapEnd mHead at *; omega)]
    apply read64_of_writeLog_at _ _ 0 _ (976#64) rfl
    simp only [mallocAlignLog, List.drop, OutLRange, and_true]
    unfold mallinfoAddr sbrkBaseAddr heapEnd mHead at *
    omega
  simp (disch := decide) only [ldv_at stat]
  sx_run [12] O.live at 0x800379e8
  · sx_norm
    refine O.foot (fun k hk => .inr ⟨by sx_addr, by sx_addr, ?_⟩)
    rw [empty]
    simp

#ix_piece mallocTop_p2 from mallocTop_p1 by
  have header : (BitVec.ofNat 64 (heapStart + 976) - BitVec.ofNat 64 heapStart + 2800#64 ||| 1#64) = 3777#64 := by decide
  simp only [heapStart, Nat.reduceAdd] at header
  simp only [header]
  unfold heapEnd mHead at stackHigh
  refine next _ _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] using p.frame.sp
  · simp (disch := sx_addr) only [read64_miss]
    exact p.frame.s0
  · simp (disch := sx_addr) only [read64_miss]
    exact p.frame.ra
  · simpa only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] using p.frame.s1
  · simpa only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] using p.frame.s2
  · simpa only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] using p.frame.s3
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [← writeLog_append, List.cons_append, List.nil_append, mallocTopLog]
    rfl

#ix_chain malloc_boot_top := [mallocTop_p1, mallocTop_p2]
end OCaml.Vm.Boot.Startup
