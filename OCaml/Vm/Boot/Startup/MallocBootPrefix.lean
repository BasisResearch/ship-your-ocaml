import OCaml.Vm.Boot.Startup.AllocatorInitial
import VsaIris.Vsa.MallocPro
namespace OCaml.Vm.Boot.Startup
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The empty-bin observation used by the allocator's first search. -/
theorem InitialArena.bin_links {m : Mem} (h : InitialArena m) (i : Nat)
    (lo : 0 < i) (hi : i < numBins) :
    read64 m (binAt i + 16) = some (binAt i) ∧
    read64 m (binAt i + 24) = some (binAt i) := by
  obtain ⟨first, forward, links⟩ := h.bins i lo hi
  cases links with
  | close backward => exact ⟨forward, backward⟩

/-- Native frame writes before the first morecore call. -/
def mallocBootLog (sp ra saved : BitVec 64) : List WEntry :=
  [(sp.toNat - 16, 8, saved), (sp.toNat - 8, 8, ra),
   (sp.toNat - 88, 8, 944#64), (sp.toNat - 56, 8, BitVec.ofNat 64 avAddr),
   (sp.toNat - 64, 8, BitVec.ofNat 64 avAddr), (sp.toNat - 72, 8, 944#64),
   (sp.toNat - 80, 8, 0#64), (sp.toNat - 88, 8, 976#64)]

/-- Exact call boundary supplied to the first-morecore summary. -/
structure MallocBootAtCall (C : MCtx) (R : Nat → BitVec 64) (m : Mem) : Prop where
  frame : MFrame C R m
  a0 : R 10 = reentV
  a1 : R 11 = 976#64
  s0 : R 8 = reentV
  ra : R 1 = 0x800378a4#64
  memory : m = writeLog C.Mt0 (mallocBootLog C.s C.r (C.rv0 8))

macro_rules
  | `(tactic| sx_side) => `(tactic| (refine VsaIris.VsaHeap.WOK.stack ‹VsaIris.VsaHeap.WOK _› ?_ ?_ <;> ((try unfold VsaIris.VsaHeap.mHead); sx_addr)))
macro_rules
  | `(tactic| sx_side) => `(tactic| (refine VsaIris.VsaHeap.WOK.foot ‹VsaIris.VsaHeap.WOK _› (fun k hk => Or.inl ?_); unfold VsaIris.VsaHeap.allocGlobal VsaIris.VsaHeap.InRange; omega))

-- The generated step table supplies the first allocation transitions.
#ix_piece mallocBoot_p1 {C : MCtx} (O : WOK C) {R : Nat → BitVec 64}
    (E : MEntry C R) (arena : InitialArena C.Mt0) (size : C.n = 928#64)
    (stackHigh : heapEnd + mHead ≤ C.s.toNat)
    (next : ∀ R' m, MallocBootAtCall C R' m → AW C.live C.S C.Q 0x80042454#64 R' m) :
    AW C.live C.S C.Q 0x800375b8#64 R C.Mt0 by
  have hlo := O.sp.lo
  have hhi := O.sp.hi
  have hal := O.sp.align
  have hra := O.ral
  have sp := E.sp
  have spNat : (R 2).toNat = C.s.toNat := congrArg BitVec.toNat sp
  have request : R 11 = 928#64 := E.a1.trans size
  have requestNat : (R 11).toNat = 928 := congrArg BitVec.toNat request
  have reent := E.a0
  unfold mHead Vsa.Sim.tohostAddr Vsa.Sim.LibraryLayout.tohostAddr at hlo
  unfold heapEnd mHead at stackHigh
  sx_run [16] O.live at 0x800375d0
  simp only [request]
  sx_run [40] O.live at 0x80037694

#ix_piece mallocBoot_p2 from mallocBoot_p1 by
  simp only [show (951#64 &&& 18446744073709551600#64) = 944#64 from by decide]
  sx_run [32] O.live at 0x800376cc
  try sx_norm
  try sx_mem
  have bin70 := (arena.bin_links 70 (by decide) (by decide)).2
  simp (disch := decide) only [ldv_at bin70]
  sx_run [16] O.live at 0x80037708

#ix_piece mallocBoot_p3 from mallocBoot_p2 by
  have bin1 := (arena.bin_links 1 (by decide) (by decide)).1
  simp (disch := decide) only [ldv_at bin1]
  sx_run [16] O.live at 0x80037784
  simp (disch := decide) only [ldv_at arena.binblocks,
    show BitVec.signExtend 64 (shift_bits_right_arith (71#32) (2#5)) = 17#64 from by decide]
  sx_run [16] O.live at 0x80037840
  simp (disch := decide) only [ldv_at arena.top]
  simp only [avAddr]
  sx_run [8] O.live at 0x8003784c
  simp (disch := decide) only [ldv_at arena.binblocks]
  sx_run [8] O.live at 0x80037870
  simp (disch := decide) only [ldv_at arena.top_pad, ldv_at arena.sbrk_base]
  sx_run [16] O.live at 0x80042454

#ix_piece mallocBoot_p4 from mallocBoot_p3 by
  refine next _ _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, E.sp]
  · simp (disch := sx_addr) only [read64_hit_eq, read64_miss, E.s0]
  · simp (disch := sx_addr) only [read64_hit_eq, read64_miss, E.ra]
  · simpa only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] using E.s1
  · simpa only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] using E.s2
  · simpa only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] using E.s3
  · simpa only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] using E.a0
  · rfl
  · simpa only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] using E.a0
  · rfl
  · have addr (off : Nat) (hoff : off ≤ 96) :
        (R 2 + 18446744073709551520#64 + BitVec.ofNat 64 off).toNat = C.s.toNat - (96 - off) := by
      sx_addr
    simp only [← writeLog_append, List.cons_append, List.nil_append, mallocBootLog,
      addr 80 (by decide), addr 88 (by decide), addr 8 (by decide), addr 40 (by decide),
      addr 32 (by decide), addr 24 (by decide), addr 16 (by decide), E.s0, E.ra]
    rfl

#ix_chain malloc_boot_prefix := [mallocBoot_p1, mallocBoot_p2, mallocBoot_p3, mallocBoot_p4]
end OCaml.Vm.Boot.Startup
