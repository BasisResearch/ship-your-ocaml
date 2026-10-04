import OCaml.Vm.Gc.AllocAccount

namespace OCaml.Vm.Gc.AllocAccount
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The accounting writes leave the native save bank intact. -/
structure ReturnInput (R : Nat → BitVec 64) (c : Config) : Prop extends Input R c where
  stackRead : ∀ off ∈ AllocReturn.offsets, ReadWindow (R 2 + BitVec.ofNat 64 off) 8
  stackOutside : ∀ off ∈ AllocReturn.offsets, OutLRange (effect R c) (R 2 + BitVec.ofNat 64 off).toNat 8
  aligned : (AllocReturn.returnWord (R 2) (R 10) c).toNat % 4 = 0

structure ReturnPost (R : Nat → BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem
  pc : PCAt (AllocReturn.returnWord (R 2) (R 10) before) after
  registers : GHolds after.σ (AllocReturn.restored (R 2) (R 10) before)
  memory : after.σ.mem = writeLog before.σ.mem (effect R before)
  counter : word after Layout.sym_caml_allocated_words = counted R before
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,2,8,9,10,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Actual header installation, accounting and native return when the
loaded counter/threshold select the no-major-slice path. -/
theorem account_return {R c} (input : ReturnInput R c) :
    FnSummary pc (fun d => d = c) (ReturnPost R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (account input.toInput).run
  intro middle accounted
  have saved (off : Nat) (member : off ∈ AllocReturn.offsets) :
      bytesT middle.σ.mem (R 2 + BitVec.ofNat 64 off).toNat 8 =
      bytesT c.σ.mem (R 2 + BitVec.ofNat 64 off).toNat 8 := by
    rw [accounted.memory]
    exact bytesT_writeLog_out _ (input.stackOutside off member)
  have returnSame : AllocReturn.returnWord (R 2) (R 10) middle =
      AllocReturn.returnWord (R 2) (R 10) c := saved _ (by decide)
  have returnInput : AllocReturn.Input (R 2) (R 10) middle :=
    ⟨accounted.machine.good,accounted.machine.minstret,accounted.machine.tick,
      accounted.code,accounted.registers,input.stackRead,by rw [returnSame]; exact input.aligned⟩
  obtain ⟨after,run,returned⟩ := (AllocReturn.return_machine returnInput).run middle ⟨accounted.pc,rfl⟩
  refine ⟨after,run,⟨returned.machine.good,returned.machine.tick,returned.machine.minstret,
    returned.code,?_,?_,returned.memory.trans accounted.memory,?_,
    returned.machine.output.trans accounted.machine.output,?_⟩⟩
  · simpa only [returnSame] using returned.pc
  · have sameRegs : AllocReturn.restored (R 2) (R 10) middle = AllocReturn.restored (R 2) (R 10) c := by
      unfold AllocReturn.restored
      congr 2
      apply List.map_congr_left
      intro cell member
      simp only [List.mem_reverse] at member
      exact congrArg (fun value => (cell.1,value)) (saved cell.2 (AllocReturn.slot_offset cell member))
    simpa only [sameRegs] using returned.registers
  · rw [word,returned.memory]
    exact accounted.counter
  · intro r noise outside
    have returnCover : ∀ n ∈ wrChain AllocReturn.blocks, n ∈ [1,2,8,9,10,13,14,15] := by decide
    have accountCover : ∀ n ∈ wrChain blocks, n ∈ [1,2,8,9,10,13,14,15] := by decide
    exact (returned.machine.frame r noise (fun n hn => outside n (returnCover n hn))).trans
      (accounted.machine.frame r noise (fun n hn => outside n (accountCover n hn)))

/-- The native ABI returns the payload address of the initialized block. -/
theorem ReturnPost.result {R before after} (post : ReturnPost R before after) :
    gprGet after.σ 10 = some (R 10 + BitVec.ofNat 64 Layout.header_bytes) :=
  gholds_lookup _ post.registers rfl

/-- Accounting preserves the installed header when the two cells are disjoint. -/
theorem ReturnPost.header {R before after} (post : ReturnPost R before after)
    (outside : OutLRange ((effect R before).drop 1) (R 10).toNat 8) :
    word after (R 10).toNat = R 11 := by
  rw [word,post.memory]
  exact word_writeLog_at _ _ 0 _ _ rfl outside

/-- The modular machine counter agrees with natural allocation accounting
when the caller supplies the no-overflow bound. -/
theorem ReturnPost.counter_nat {R before after} (post : ReturnPost R before after)
    (bound : (bytesT (initialized R before) Layout.sym_caml_allocated_words 8).toNat +
      1 + (R 8).toNat < 2^64) :
    (word after Layout.sym_caml_allocated_words).toNat =
      (bytesT (initialized R before) Layout.sym_caml_allocated_words 8).toNat + 1 + (R 8).toNat := by
  rw [post.counter]
  simp only [counted,BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

end OCaml.Vm.Gc.AllocAccount
