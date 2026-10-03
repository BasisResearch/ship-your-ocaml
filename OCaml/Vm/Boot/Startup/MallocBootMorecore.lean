import OCaml.Vm.Boot.Startup.MallocBootPrefix
import OCaml.Vm.Boot.Startup.SbrkBootstrap
namespace OCaml.Vm.Boot.Startup
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- All allocator metadata below the native frame survives the malloc prefix. -/
theorem MallocBootAtCall.read_below {C : MCtx} {R : Nat → BitVec 64} {m : Mem}
    (p : MallocBootAtCall C R m) {a : Nat} (ha : a + 8 ≤ C.s.toNat - 88) :
    read64 m a = read64 C.Mt0 a := by
  rw [p.memory]
  apply VsaIris.Sym.read64_logOut
  intro k hk
  simp only [mallocBootLog, OutL, and_true]
  omega

/-- Morecore writes only inside malloc's existing ownership window. -/
theorem malloc_sbrk_window (C : MCtx) (a : Nat)
    (h : SbrkW (C.s.toNat - 96) a) : MWin C.H C.s a := by
  unfold SbrkW brkAddr at h
  rcases h with h | h | h | h
  · exact .inr ⟨by unfold mHead; omega, by omega⟩
  all_goals exact .inl (.inl (by unfold allocGlobal InRange; omega))

/-- Shared call geometry for morecore calls inside malloc's native frame. -/
theorem malloc_morecore_pre {C : MCtx} (O : WOK C)
    {R : Nat → BitVec 64} {m : Mem} {brkv size : Nat}
    (stackHigh : heapEnd + mHead ≤ C.s.toNat)
    (hsp : R 2 = C.s + 18446744073709551520#64)
    (hsize : (R 11).toNat = size) (sizeLt : size < 2^32)
    (read : read64 m brkAddr = some brkv) (positive : 0 < brkv)
    (bound : brkv ≤ heapEnd) (link : (R 1).toNat % 4 = 0) :
    SbrkPre C.S R m brkv size := by
  have hlo := O.sp.lo
  have hhi := O.sp.hi
  have hal := O.sp.align
  have sp : (R 2).toNat = C.s.toNat - 96 := by rw [hsp]; sx_addr
  unfold heapEnd mHead at stackHigh
  refine ⟨hsize, sizeLt, read, positive, bound, ?_, ?_, ?_, link, ?_, ?_, ?_⟩
  · rw [sp]; unfold Vsa.Sim.tohostAddr Vsa.Sim.LibraryLayout.tohostAddr; omega
  · rw [sp]; omega
  · rw [sp]; omega
  · rw [sp]; omega
  · rw [sp]; unfold brkAddr; omega
  · intro a ha
    exact O.own a (malloc_sbrk_window C a (sp ▸ ha))

/-- The prefix supplies every precondition of the source zero-break morecore
summary; no initialized heap is required. -/
theorem MallocBootAtCall.sbrk_pre {C : MCtx} (O : WOK C)
    {R : Nat → BitVec 64} {m : Mem} (p : MallocBootAtCall C R m)
    (arena : InitialArena C.Mt0) (stackHigh : heapEnd + mHead ≤ C.s.toNat) :
    SbrkBootPre C.S R m 976 := by
  refine ⟨?_, malloc_morecore_pre O stackHigh p.frame.sp
    (by rw [p.a1]; rfl) (by decide) (by rw [read64_store_hit]; rfl)
    (by decide) (by decide) (by rw [p.ra]; decide), by decide⟩
  rw [p.read_below (by unfold brkAddr heapEnd mHead at *; omega)]
  exact arena.brk

/-- Morecore preserves the enclosing malloc frame above its own native stack. -/
theorem MFrame.after_sbrk {C : MCtx} (O : WOK C) {R R' : Nat → BitVec 64}
    {m m' : Mem} {brk' : Nat} (f : MFrame C R m)
    (stackHigh : heapEnd + mHead ≤ C.s.toNat) (p : SbrkPost R R' m m' brk') :
    MFrame C R' m' := by
  have hlo := O.sp.lo
  have hhi := O.sp.hi
  have sp : (R 2).toNat = C.s.toNat - 96 := by rw [f.sp]; sx_addr
  unfold heapEnd mHead at stackHigh
  have slot (off : Nat) (ho : off + 8 ≤ 96) :
      read64 m' (C.s.toNat - 96 + off) = read64 m (C.s.toNat - 96 + off) :=
    read64_keep fun k hk => p.agree _ (by unfold SbrkW brkAddr; rw [sp]; omega)
  exact ⟨(p.regs 2 (by decide) (by decide) (by decide)).trans f.sp,
    (slot 80 (by decide)).trans f.s0, (slot 88 (by decide)).trans f.ra,
    (p.regs 9 (by decide) (by decide) (by decide)).trans f.s1,
    (p.regs 18 (by decide) (by decide) (by decide)).trans f.s2,
    (p.regs 19 (by decide) (by decide) (by decide)).trans f.s3⟩

/-- The first-morecore return boundary. Its word frame covers both the malloc
spills and all untouched initial allocator metadata. -/
structure MallocBootAfterMorecore (C : MCtx) (R : Nat → BitVec 64) (m : Mem) : Prop where
  frame : MFrame C R m
  a0 : R 10 = BitVec.ofNat 64 heapStart
  s0 : R 8 = reentV
  brk : read64 m brkAddr = some (heapStart + 976)
  read : ∀ a, (∀ k, k < 8 → ¬ SbrkW (C.s.toNat - 96) (a + k)) →
    read64 m a = read64 (writeLog C.Mt0 (mallocBootLog C.s C.r (C.rv0 8))) a
  present : ∀ a : Nat, (C.Mt0[a]?).isSome → (m[a]?).isSome
  agree : ∀ a, ¬ MWin C.H C.s a → m[a]? = C.Mt0[a]?

/-- Compose the generated malloc prefix with the proved source bootstrap call. -/
theorem malloc_boot_morecore {C : MCtx} (O : WOK C) {R : Nat → BitVec 64}
    (E : MEntry C R) (arena : InitialArena C.Mt0) (size : C.n = 928#64)
    (stackHigh : heapEnd + mHead ≤ C.s.toNat)
    (next : ∀ R' m, MallocBootAfterMorecore C R' m →
      AW C.live C.S C.Q 0x800378a4#64 R' m) :
    AW C.live C.S C.Q 0x800375b8#64 R C.Mt0 := by
  apply malloc_boot_prefix O E arena size stackHigh
  intro Rc mc call
  apply sbrk_r_boot O.live (call.sbrk_pre O arena stackHigh)
  intro R' m' post result
  rw [call.ra]
  apply next
  refine ⟨MFrame.after_sbrk O call.frame stackHigh post, result,
    (post.regs 8 (by decide) (by decide) (by decide)).trans call.s0, post.brk, ?_, ?_, ?_⟩
  · intro a ha
    rw [← call.memory]
    have hlo := O.sp.lo
    have hhi := O.sp.hi
    have sp : (Rc 2).toNat = C.s.toNat - 96 := by rw [call.frame.sp]; sx_addr
    exact read64_keep fun k hk => post.agree _ (by rw [sp]; exact ha k hk)
  · intro a ha
    apply post.pres
    rw [call.memory]
    exact writeLog_present _ _ _ ha
  · intro a ha
    have hlo := O.sp.lo
    have hhi := O.sp.hi
    have sp : (Rc 2).toNat = C.s.toNat - 96 := by rw [call.frame.sp]; sx_addr
    rw [post.agree a (by rw [sp]; exact fun h => ha (malloc_sbrk_window C a h)), call.memory]
    apply writeLog_out
    have outside : ¬ (C.s.toNat - mHead ≤ a ∧ a < C.s.toNat) := fun h => ha (.inr h)
    simp only [mallocBootLog, OutL, and_true]
    unfold mHead at outside
    unfold heapEnd mHead at stackHigh
    omega

/-- Word reads in the enclosing malloc frame survive the nested call. -/
theorem MallocBootAfterMorecore.spill {C : MCtx} {R : Nat → BitVec 64} {m : Mem}
    (p : MallocBootAfterMorecore C R m) (stackHigh : heapEnd + mHead ≤ C.s.toNat)
    (off : Nat) (ho : off + 8 ≤ 96) :
    read64 m (C.s.toNat - 96 + off) =
      read64 (writeLog C.Mt0 (mallocBootLog C.s C.r (C.rv0 8))) (C.s.toNat - 96 + off) := by
  apply p.read
  intro k hk
  unfold SbrkW brkAddr heapEnd mHead at *
  omega

/-- Initial metadata outside the morecore globals survives both prefixes.
`SbrkW 0` selects only the summary's global writes, since its stack is empty. -/
theorem MallocBootAfterMorecore.initial_read {C : MCtx} {R : Nat → BitVec 64} {m : Mem}
    (p : MallocBootAfterMorecore C R m) (stackHigh : heapEnd + mHead ≤ C.s.toNat)
    {a : Nat} (ha : a + 8 ≤ heapEnd) (safe : ∀ k, k < 8 → ¬ SbrkW 0 (a + k)) :
    read64 m a = read64 C.Mt0 a := by
  rw [p.read a (by
    intro k hk
    have := safe k hk
    unfold SbrkW at *
    unfold mHead at stackHigh
    omega)]
  apply VsaIris.Sym.read64_logOut
  intro k hk
  simp only [mallocBootLog, OutL, and_true]
  unfold mHead at stackHigh
  omega

/-- Shared spill recovery for either nested morecore call. -/
theorem morecore_spill_value {sp : BitVec 64} {before m : Mem} {log : List WEntry}
    (read : ∀ a, (∀ k, k < 8 → ¬ SbrkW (sp.toNat - 96) (a + k)) →
      read64 m a = read64 (writeLog before log) a)
    (stackHigh : heapEnd + mHead ≤ sp.toNat) (off index : Nat) (v : BitVec 64)
    (ho : off + 8 ≤ 96) (atWord : log[index]? = some (sp.toNat - 96 + off, 8, v))
    (afterWord : OutLRange (log.drop (index + 1)) (sp.toNat - 96 + off) 8) :
    read64 m (sp.toNat - 96 + off) = some v.toNat := by
  rw [read _ (by intro k hk; unfold SbrkW brkAddr heapEnd mHead at *; omega)]
  exact read64_of_writeLog_at _ _ index _ v atWord afterWord

/-- Select a saved word through the generic last-write certificate. -/
theorem MallocBootAfterMorecore.spill_value {C : MCtx} {R : Nat → BitVec 64} {m : Mem}
    (p : MallocBootAfterMorecore C R m) (stackHigh : heapEnd + mHead ≤ C.s.toNat)
    (off index : Nat) (v : BitVec 64) (ho : off + 8 ≤ 96)
    (atWord : (mallocBootLog C.s C.r (C.rv0 8))[index]? =
      some (C.s.toNat - 96 + off, 8, v))
    (afterWord : OutLRange ((mallocBootLog C.s C.r (C.rv0 8)).drop (index + 1))
      (C.s.toNat - 96 + off) 8) :
    read64 m (C.s.toNat - 96 + off) = some v.toNat :=
  morecore_spill_value p.read stackHigh off index v ho atWord afterWord
end OCaml.Vm.Boot.Startup
