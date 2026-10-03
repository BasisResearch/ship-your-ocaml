import OCaml.Vm.Boot.Startup.MallocBootAlign
namespace OCaml.Vm.Boot.Startup
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The second-morecore return, before the source initializes the top chunk. -/
structure MallocBootAligned (C : MCtx) (before : Mem) (R : Nat → BitVec 64) (m : Mem) : Prop where
  frame : MFrame C R m
  a0 : R 10 = BitVec.ofNat 64 (heapStart + 976)
  s0 : R 8 = reentV
  brk : read64 m brkAddr = some (heapStart + 3776)
  read : ∀ a, (∀ k, k < 8 → ¬ SbrkW (C.s.toNat - 96) (a + k)) →
    read64 m a = read64 (writeLog before (mallocAlignLog C.s)) a
  present : ∀ a : Nat, (before[a]?).isSome → (m[a]?).isSome
  agree : ∀ a, ¬ MWin C.H C.s a → m[a]? = before[a]?

/-- The initialized break lets the second call consume the ordinary landed
sbrk contract. Its failure branch is impossible by the generated heap bound. -/
theorem malloc_alignment_morecore {C : MCtx} (O : WOK C)
    {R : Nat → BitVec 64} {m : Mem} (p : MallocBootAfterMorecore C R m)
    (arena : InitialArena C.Mt0) (stackHigh : heapEnd + mHead ≤ C.s.toNat)
    (next : ∀ R' m', MallocBootAligned C m R' m' →
      AW C.live C.S C.Q 0x80037d18#64 R' m') :
    AW C.live C.S C.Q 0x800378a4#64 R m := by
  apply malloc_boot_alignment O p arena stackHigh
  intro Rc mc call
  have hlo := O.sp.lo
  have hhi := O.sp.hi
  have sp : (Rc 2).toNat = C.s.toNat - 96 := by rw [call.frame.sp]; sx_addr
  have breakWord : read64 mc brkAddr = some (heapStart + 976) := by
    rw [call.memory, VsaIris.Sym.read64_logOut]
    · exact p.brk
    · intro k hk
      simp only [mallocAlignLog, OutL, and_true]
      unfold brkAddr mallinfoAddr sbrkBaseAddr heapEnd mHead at *
      omega
  have pre := malloc_morecore_pre O stackHigh call.frame.sp
    (by rw [call.a1]; rfl) (by decide : 2800 < 2^32) breakWord
    (by decide) (by decide) (by rw [call.ra]; decide)
  apply sbrk_r_run O.live pre
  · intro _ R' m' post result
    rw [call.ra]
    apply next
    refine ⟨MFrame.after_sbrk O call.frame stackHigh post, result,
      (post.regs 8 (by decide) (by decide) (by decide)).trans call.s0,
      post.brk, ?_, ?_, ?_⟩
    · intro a ha
      rw [← call.memory]
      exact read64_keep fun k hk => post.agree _ (by rw [sp]; exact ha k hk)
    · intro a ha
      apply post.pres
      rw [call.memory]
      exact writeLog_present _ _ _ ha
    · intro a ha
      rw [post.agree a (by rw [sp]; exact fun h => ha (malloc_sbrk_window C a h)), call.memory]
      apply writeLog_out
      have hstack : ¬ (C.s.toNat - mHead ≤ a ∧ a < C.s.toNat) := fun h => ha (.inr h)
      have hglobal : ¬ allocGlobal a := fun h => ha (.inl (.inl h))
      simp only [mallocAlignLog, OutL, and_true]
      unfold allocGlobal InRange at hglobal
      unfold mHead at hstack
      unfold mallinfoAddr sbrkBaseAddr heapEnd mHead at *
      omega
  · intro impossible
    exact False.elim (by revert impossible; decide)

/-- Restore a spilled word after the second call using the same last-write
certificate consumed by the first-call proof. -/
theorem MallocBootAligned.spill_value {C : MCtx} {before : Mem}
    {R : Nat → BitVec 64} {m : Mem} (p : MallocBootAligned C before R m)
    (stackHigh : heapEnd + mHead ≤ C.s.toNat) (off index : Nat) (v : BitVec 64)
    (ho : off + 8 ≤ 96)
    (atWord : (mallocAlignLog C.s)[index]? = some (C.s.toNat - 96 + off, 8, v))
    (afterWord : OutLRange ((mallocAlignLog C.s).drop (index + 1))
      (C.s.toNat - 96 + off) 8) : read64 m (C.s.toNat - 96 + off) = some v.toNat :=
  morecore_spill_value p.read stackHigh off index v ho atWord afterWord
end OCaml.Vm.Boot.Startup
