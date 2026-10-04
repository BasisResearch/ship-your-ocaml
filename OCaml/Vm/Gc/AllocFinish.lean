import OCaml.Vm.Gc.AllocSuccess
import Vsa.Sim.GRegsFrame

namespace OCaml.Vm.Gc.AllocFinish
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Common wrapper register interface, independent of the free-list route. -/
def entryRegs (sp size hp : BitVec 64) (n : Nat) :=
  if n = 2 then sp else if n = 8 then size else hp

def snapshot (log : List WEntry) (c : Config) : Config :=
  {c with σ := {c.σ with mem := writeLog c.σ.mem log}}

def effect (sp size hp : BitVec 64) (log : List WEntry) (c : Config) :=
  log ++ AllocAccount.effect (AllocSuccess.completed (entryRegs sp size hp) (snapshot log c)) (snapshot log c)

theorem effect_of_memory {sp size hp log} {before after : Config}
    (memory : after.σ.mem = before.σ.mem) :
    effect sp size hp log after = effect sp size hp log before := by
  have same : (snapshot log after).σ.mem = (snapshot log before).σ.mem := by
    simp only [snapshot,memory]
  unfold effect
  rw [AllocSuccess.completed_of_memory same]
  simp only [AllocAccount.effect,AllocAccount.counted,AllocAccount.initialized,same]

/-- The common continuation preserves the code-image boundary for every
free-list route whose finite store log does. -/
theorem effect_high {sp size hp log c}
    (high : ∀ e ∈ log, Layout.sym_tohost + 16 ≤ e.1)
    (conditions : AllocSuccess.Conditions (entryRegs sp size hp) (snapshot log c)) :
    ∀ e ∈ effect sp size hp log c, Layout.sym_tohost + 16 ≤ e.1 := by
  intro e member
  rw [effect,List.mem_append] at member
  rcases member with member | member
  · exact high e member
  · simp only [AllocAccount.effect,AllocAccount.headerLog,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact conditions.account.headerWrite.htif
    · change Layout.sym_tohost + 16 ≤ Layout.sym_caml_allocated_words
      decide

/-- Normalized evidence from a proved free-list callee. Concrete allocator
summaries construct this record; it does not postulate an allocator run. -/
structure CalleePost (sp size hp : BitVec 64) (log : List WEntry) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem
  pc : PCAt AllocEntry.returnPc after
  registers : GHolds after.σ [(2,sp),(8,size),(10,hp)]
  memory : after.σ.mem = writeLog before.σ.mem log
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,2,10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

structure Post (sp size hp : BitVec 64) (log : List WEntry) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem
  pc : PCAt (AllocReturn.returnWord sp hp (snapshot log before)) after
  registers : GHolds after.σ (AllocReturn.restored sp hp (snapshot log before))
  result : gprGet after.σ 10 = some (hp + BitVec.ofNat 64 Layout.header_bytes)
  memory : after.σ.mem = writeLog before.σ.mem (effect sp size hp log before)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,2,8,9,10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Shared continuation for any proved successful free-list route: actual
color selection, header/accounting stores and native wrapper return. -/
theorem CalleePost.finish {sp size hp log before middle} (callee : CalleePost sp size hp log before middle)
    (tagRead : ReadWindow (sp + BitVec.ofNat 64 AllocEntry.tagOffset) 8)
    (conditions : AllocSuccess.Conditions (entryRegs sp size hp) (snapshot log before)) :
    FnSummary AllocEntry.returnPc (fun d => d = middle) (Post sp size hp log before) := by
  have memory : middle.σ.mem = (snapshot log before).σ.mem := callee.memory
  have nonnull : hp ≠ 0 := by
    have lower := conditions.account.headerWrite.lower
    change 0x80000000 ≤ hp.toNat at lower
    intro zero
    rw [zero] at lower
    change (0x80000000 : Nat) ≤ 0 at lower
    omega
  have input : AllocSuccess.Input (entryRegs sp size hp) middle :=
    { toInput :=
      { good := callee.good
        tick := callee.tick
        minstret := callee.minstret
        code := callee.code
        registers := callee.registers
        tagRead := tagRead
        nonnull := nonnull }
      toConditions := conditions.of_memory memory }
  apply (AllocSuccess.finish input).weaken (fun _ h => h)
  intro after finished
  refine ⟨finished.good,finished.tick,finished.minstret,finished.code,?_,?_,?_,?_,
    finished.output.trans callee.output,?_⟩
  · simpa [AllocReturn.returnWord,entryRegs,memory] using finished.pc
  · simpa [AllocReturn.restored,entryRegs,memory] using finished.registers
  · simpa [entryRegs,Layout.header_bytes] using finished.result
  · have same := AllocSuccess.completed_of_memory (R := entryRegs sp size hp) memory
    rw [finished.memory,same]
    unfold effect
    simp only [AllocAccount.effect,AllocAccount.counted,AllocAccount.initialized,memory,snapshot,writeLog_append]
  · intro r noise outside
    have finishCover : ∀ n ∈ [1,2,8,9,10,11,13,14,15], n ∈ [1,2,8,9,10,11,12,13,14,15] := by decide
    have calleeCover : ∀ n ∈ [1,2,10,11,12,13,14,15], n ∈ [1,2,8,9,10,11,12,13,14,15] := by decide
    exact (finished.native r noise (fun n hn => outside n (finishCover n hn))).trans
      (callee.native r noise (fun n hn => outside n (calleeCover n hn)))

/-- Route-independent typed header readback from the common continuation log. -/
theorem header_of_effect {sp size hp log} {before after : Config}
    (memory : after.σ.mem = writeLog before.σ.mem (effect sp size hp log before))
    (separate : hp.toNat + 8 ≤ Layout.sym_caml_allocated_words ∨ Layout.sym_caml_allocated_words + 8 ≤ hp.toNat)
    (sizeBound : size.toNat < 2^54)
    (tagBound : (word (snapshot log before) (sp + BitVec.ofNat 64 AllocEntry.tagOffset).toNat).toNat < 256) :
    HeaderOk (word after hp.toNat) size.toNat
      (word (snapshot log before) (sp + BitVec.ofNat 64 AllocEntry.tagOffset).toNat).toNat := by
  have stored : word after hp.toNat = AllocSuccess.completed (entryRegs sp size hp) (snapshot log before) 11 := by
    rw [word,memory,effect,writeLog_append]
    apply word_writeLog_at _ _ 0 _ _ rfl
    exact ⟨separate,True.intro⟩
  rw [stored]
  exact AllocColor.header_ok _ _ _ sizeBound tagBound

theorem Post.header {sp size hp log before after} (post : Post sp size hp log before after)
    (separate : hp.toNat + 8 ≤ Layout.sym_caml_allocated_words ∨ Layout.sym_caml_allocated_words + 8 ≤ hp.toNat)
    (sizeBound : size.toNat < 2^54)
    (tagBound : (word (snapshot log before) (sp + BitVec.ofNat 64 AllocEntry.tagOffset).toNat).toNat < 256) :
    HeaderOk (word after hp.toNat) size.toNat
      (word (snapshot log before) (sp + BitVec.ofNat 64 AllocEntry.tagOffset).toNat).toNat :=
  header_of_effect post.memory separate sizeBound tagBound

end OCaml.Vm.Gc.AllocFinish
