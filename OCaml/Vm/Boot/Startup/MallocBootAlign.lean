import OCaml.Vm.Boot.Startup.MallocBootMorecore
namespace OCaml.Vm.Boot.Startup
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- Stores between the first and second source morecore calls. -/
def mallocAlignLog (sp : BitVec 64) : List WEntry :=
  [(mallinfoAddr, 8, 976#64), (sbrkBaseAddr, 8, BitVec.ofNat 64 heapStart),
   (sp.toNat - 32, 8, BitVec.ofNat 64 mallinfoAddr),
   (sp.toNat - 40, 8, BitVec.ofNat 64 avAddr),
   (sp.toNat - 48, 8, BitVec.ofNat 64 avAddr),
   (sp.toNat - 56, 8, 944#64), (sp.toNat - 64, 8, 0#64),
   (sp.toNat - 72, 8, BitVec.ofNat 64 heapStart),
   (sp.toNat - 88, 8, 2800#64),
   (sp.toNat - 80, 8, BitVec.ofNat 64 (heapStart + 976))]

structure MallocBootAlignmentCall (C : MCtx) (before : Mem)
    (R : Nat → BitVec 64) (m : Mem) : Prop where
  frame : MFrame C R m
  a0 : R 10 = reentV
  a1 : R 11 = 2800#64
  s0 : R 8 = reentV
  ra : R 1 = 0x80037d18#64
  memory : m = writeLog before (mallocAlignLog C.s)

#ix_piece mallocAlign_p1 {C : MCtx} (O : WOK C) {R : Nat → BitVec 64} {m : Mem}
    (p : MallocBootAfterMorecore C R m) (arena : InitialArena C.Mt0)
    (stackHigh : heapEnd + mHead ≤ C.s.toNat)
    (next : ∀ R' m', MallocBootAlignmentCall C m R' m' →
      AW C.live C.S C.Q 0x80042454#64 R' m') :
    AW C.live C.S C.Q 0x800378a4#64 R m by
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
  have slot8 := p.spill_value stackHigh 8 7 (976#64) (by decide)
    (by rw [addr 8 (by decide)]; rfl) (by trivial)
  have slot16 := p.spill_value stackHigh 16 6 (0#64) (by decide)
    (by rw [addr 16 (by decide)]; rfl) (by simp only [mallocBootLog, List.drop, OutLRange, and_true]; omega)
  have slot24 := p.spill_value stackHigh 24 5 (944#64) (by decide)
    (by rw [addr 24 (by decide)]; rfl) (by simp only [mallocBootLog, List.drop, OutLRange, and_true]; omega)
  have slot32 := p.spill_value stackHigh 32 4 (BitVec.ofNat 64 avAddr) (by decide)
    (by rw [addr 32 (by decide)]; rfl) (by simp only [mallocBootLog, List.drop, OutLRange, and_true]; omega)
  have slot40 := p.spill_value stackHigh 40 3 (BitVec.ofNat 64 avAddr) (by decide)
    (by rw [addr 40 (by decide)]; rfl) (by simp only [mallocBootLog, List.drop, OutLRange, and_true]; omega)
  have result := p.a0
  have resultNat : (R 10).toNat = heapStart := congrArg BitVec.toNat p.a0
  unfold heapStart at resultNat
  have saved := p.s0
  sx_run [8] O.live at 0x800378c0
  simp (disch := sx_addr) only [ldv_at slot8, ldv_at slot16, ldv_at slot24, ldv_at slot32, ldv_at slot40]
  simp only [result, heapStart, avAddr]
  sx_run [12] O.live at 0x800378e0
  have stat := p.initial_read stackHigh (a := mallinfoAddr) (by decide)
    (by intro k hk; unfold SbrkW brkAddr mallinfoAddr; omega)
  rw [arena.mallinfo] at stat
  simp (disch := decide) only [ldv_at stat]
  sx_run [8] O.live at 0x800378f4
  have base := p.initial_read stackHigh (a := sbrkBaseAddr) (by decide)
    (by intro k hk; unfold SbrkW brkAddr sbrkBaseAddr; omega)
  rw [arena.sbrk_base] at base
  simp (disch := decide) only [ldv_at base]
  sx_run [12] O.live at 0x80037908
  have heapAlign : (BitVec.ofNat 64 heapStart &&& 15#64) = 0#64 := by decide
  simp only [heapStart] at heapAlign
  simp only [heapAlign]
  sx_run [16] O.live at 0x80042454

#ix_piece mallocAlign_p2 from mallocAlign_p1 by
  have padding : ((0#64 - BitVec.ofNat 64 (heapStart + 976)) <<< 52 >>> 52) = 2800#64 := by decide
  simp only [heapStart, Nat.reduceAdd] at padding
  simp only [padding]
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
  · simpa only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] using p.s0
  · rfl
  · simpa only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] using p.s0
  · rfl
  · have writeAddr (off : Nat) (ho : off ≤ 96) :
        (R 2 + BitVec.ofNat 64 off).toNat = C.s.toNat - (96 - off) := by sx_addr
    simp only [← writeLog_append, List.cons_append, List.nil_append, mallocAlignLog,
      writeAddr 64 (by decide), writeAddr 56 (by decide), writeAddr 48 (by decide),
      writeAddr 40 (by decide), writeAddr 32 (by decide), writeAddr 24 (by decide),
      writeAddr 8 (by decide), writeAddr 16 (by decide)]
    rfl

#ix_chain malloc_boot_alignment := [mallocAlign_p1, mallocAlign_p2]
end OCaml.Vm.Boot.Startup
