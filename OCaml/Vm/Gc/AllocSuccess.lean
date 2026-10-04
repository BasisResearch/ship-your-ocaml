import OCaml.Vm.Gc.AllocSelect
import OCaml.Vm.Gc.AllocAccountReturn

namespace OCaml.Vm.Gc.AllocSuccess
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def completed (R : Nat → BitVec 64) (c : Config) :=
  AllocColor.colored (AllocSelect.isBlack R c) (AllocSelect.withTag R c)

/-- Memory conditions for the successful continuation, with the actual
phase-selected header substituted into accounting. -/
structure Conditions (R : Nat → BitVec 64) (c : Config) : Prop where
  account : AllocAccount.Conditions (completed R c) c
  nativeReturn : AllocAccount.ReturnConditions (completed R c) c

/-- Initial memory supplies all conditions after a successful free-list
call; the phase/color prefix is read-only. -/
structure Input (R : Nat → BitVec 64) (c : Config) : Prop
    extends AllocSelect.Input R c, Conditions R c

theorem completed_of_memory {R} {before after : Config} (memory : after.σ.mem = before.σ.mem) :
    completed R after = completed R before := by
  funext n
  simp only [completed,AllocColor.colored,AllocSelect.withTag,AllocSelect.tag,AllocSelect.isBlack,
    AllocSelect.phase,AllocSelect.sweep,word,memory]

theorem Conditions.of_memory {R} {before after : Config} (memory : after.σ.mem = before.σ.mem)
    (conditions : Conditions R before) : Conditions R after := by
  have same := completed_of_memory (R := R) memory
  constructor
  · rw [same]
    exact conditions.account.of_memory memory
  · rw [same]
    exact conditions.nativeReturn.of_memory memory

structure Post (R : Nat → BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem
  pc : PCAt (AllocReturn.returnWord (R 2) (R 10) before) after
  registers : GHolds after.σ (AllocReturn.restored (R 2) (R 10) before)
  memory : after.σ.mem = writeLog before.σ.mem (AllocAccount.effect (completed R before) before)
  counter : word after Layout.sym_caml_allocated_words = AllocAccount.counted (completed R before) before
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,2,8,9,10,11,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Every header-color route after a nonnull free-list result, through
actual native return, when accounting requires no major-slice request. -/
theorem finish {R c} (input : Input R c) :
    FnSummary AllocSelect.pc (fun d => d = c) (Post R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (AllocSelect.select input.toInput).run
  intro middle selected
  have colorInput : AllocColor.Input (AllocSelect.withTag R c) middle :=
    ⟨selected.machine.good,selected.machine.tick,selected.machine.minstret,selected.code,selected.registers⟩
  obtain ⟨ready,colorRun,colored⟩ := (AllocColor.prepare (AllocSelect.isBlack R c) colorInput).run middle ⟨selected.pc,rfl⟩
  have memory : ready.σ.mem = c.σ.mem := colored.memory.trans selected.memory
  have accountInput : AllocAccount.ReturnInput (completed R c) ready :=
    { toInput :=
      { toConditions := input.account.of_memory memory
        good := colored.machine.good
        tick := colored.machine.tick
        minstret := colored.machine.minstret
        code := colored.code
        registers := colored.registers }
      toReturnConditions := input.nativeReturn.of_memory memory }
  obtain ⟨after,returnRun,returned⟩ := (AllocAccount.account_return accountInput).run ready ⟨colored.pc,rfl⟩
  refine ⟨after,colorRun.trans returnRun,⟨returned.good,returned.tick,returned.minstret,returned.code,
    ?_,?_,?_,?_,returned.output.trans (colored.machine.output.trans selected.machine.output),?_⟩⟩
  · simpa [AllocReturn.returnWord,memory,completed,AllocColor.colored,AllocSelect.withTag] using returned.pc
  · simpa [AllocReturn.restored,memory,completed,AllocColor.colored,AllocSelect.withTag] using returned.registers
  · simpa only [AllocAccount.effect,AllocAccount.counted,AllocAccount.initialized,memory] using returned.memory
  · simpa only [AllocAccount.counted,AllocAccount.initialized,memory] using returned.counter
  · intro r noise outside
    have accountCover : ∀ n ∈ [1,2,8,9,10,13,14,15], n ∈ [1,2,8,9,10,11,13,14,15] := by decide
    have colorCover : ∀ n ∈ wrChain (AllocColor.blocks (AllocSelect.isBlack R c)), n ∈ [1,2,8,9,10,11,13,14,15] := by
      cases AllocSelect.isBlack R c <;> decide
    have selectCover : ∀ n ∈ wrChain (AllocSelect.selected R c), n ∈ [1,2,8,9,10,11,13,14,15] := by
      intro n hn
      have small := AllocSelect.written _ _ _ n hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at small
      rcases small with rfl | rfl | rfl <;> simp
    exact (returned.native r noise (fun n hn => outside n (accountCover n hn))).trans
      ((colored.machine.frame r noise (fun n hn => outside n (colorCover n hn))).trans
        (selected.machine.frame r noise (fun n hn => outside n (selectCover n hn))))

/-- The wrapper returns the initialized block's payload, not its header. -/
theorem Post.result {R before after} (post : Post R before after) :
    gprGet after.σ 10 = some (R 10 + BitVec.ofNat 64 Layout.header_bytes) :=
  gholds_lookup _ post.registers rfl

/-- Actual final-memory size/tag agreement for either selected collector color. -/
theorem Post.header {R before after} (post : Post R before after)
    (outside : OutLRange ((AllocAccount.effect (completed R before) before).drop 1) (R 10).toNat 8)
    (sizeBound : (R 8).toNat < 2^54) (tagBound : (AllocSelect.tag R before).toNat < 256) :
    HeaderOk (word after (R 10).toNat) (R 8).toNat (AllocSelect.tag R before).toNat := by
  have stored : word after (R 10).toNat = completed R before 11 := by
    rw [word,post.memory]
    exact word_writeLog_at _ _ 0 _ _ rfl outside
  rw [stored]
  exact AllocColor.header_ok _ _ _ sizeBound tagBound

end OCaml.Vm.Gc.AllocSuccess
