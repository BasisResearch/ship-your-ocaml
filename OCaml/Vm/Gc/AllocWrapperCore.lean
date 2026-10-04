import OCaml.Vm.Gc.AllocIndirect
import OCaml.Vm.Gc.Generated.BestFitSmall
import OCaml.Vm.Gc.AllocSaved
import OCaml.Vm.Gc.AllocFinish

namespace OCaml.Vm.Gc.AllocWrapperCore
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def prepared (R : Nat → BitVec 64) (c : Config) : Config :=
  {c with σ := {c.σ with mem := writeLog c.σ.mem (AllocEntry.effect R)}}

def callerRegs (R : Nat → BitVec 64) (payload : BitVec 64) : GRegs :=
  (2,R 2) :: (10,payload) :: AllocReturn.slots.reverse.map (fun cell => (cell.1,R cell.1))

/-- The real wrapper prologue and loaded indirect jump have entered bf_allocate. -/
structure Entered (R : Nat → BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem
  pc : PCAt BestFitSmall.pc after
  registers : GHolds after.σ (AllocEntry.callRegs R BestFitSmall.pc)
  link : gprGet after.σ 1 = some AllocEntry.returnPc
  memory : after.σ.mem = writeLog before.σ.mem (AllocEntry.effect R)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,2,8,9,10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Shared actual wrapper entry and linking JALR for every free-list route. -/
theorem enter {R c} (input : AllocEntry.Input R BestFitSmall.pc c) :
    FnSummary AllocEntry.pc (fun d => d = c) (Entered R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (AllocEntry.prepare input).run
  intro atCall prologue
  obtain ⟨after,run,called⟩ := (AllocEntry.call_free_list prologue.machine.good prologue.machine.tick
    prologue.machine.minstret prologue.code prologue.registers (by decide)).run atCall ⟨prologue.pc,rfl⟩
  have memory : after.σ.mem = atCall.σ.mem := called.mem
  refine ⟨after,run,⟨called.good,called.tick,called.minstret,memory ▸ prologue.code,called.pc,
    called.registers,called.ra,memory.trans prologue.memory,called.output.trans prologue.machine.output,?_⟩⟩
  intro r noise outside
  apply (called.frame r noise (by simp [wrChain]) (outside 1 (by simp))).trans
  apply prologue.machine.frame r noise
  intro n hn
  have cover : ∀ n ∈ wrChain AllocEntry.blocks, n ∈ [1,2,8,9,10,11,12,13,14,15] := by decide
  exact outside n (cover n hn)

/-- Every runtime image below HTIF survives the wrapper's native saves. -/
theorem Entered.image {R before after lo hi} {Image : Std.ExtHashMap Nat (BitVec 8) → Prop}
    (post : Entered R before after) (windows : AllocEntry.Windows R)
    (transport : ∀ {m m'}, Image m → (∀ a, lo ≤ a → a < hi → m'[a]? = m[a]?) → Image m')
    (bound : hi ≤ Layout.sym_tohost + 16) (code : Image before.σ.mem) : Image after.σ.mem := by
  rw [post.memory]
  apply image_writeLog transport code
  intro e member
  exact Nat.le_trans bound (AllocEntry.effect_high windows e member)

def effect (R : Nat → BitVec 64) (hp : BitVec 64) (log : List WEntry) (c : Config) :=
  AllocEntry.effect R ++ AllocFinish.effect (AllocEntry.frameSp R) (R 10) hp log (prepared R c)

structure Post (R : Nat → BitVec 64) (hp : BitVec 64) (log : List WEntry) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem
  pc : PCAt (R 1) after
  registers : GHolds after.σ (callerRegs R (hp + BitVec.ofNat 64 Layout.header_bytes))
  result : gprGet after.σ 10 = some (hp + BitVec.ofNat 64 Layout.header_bytes)
  memory : after.σ.mem = writeLog before.σ.mem (effect R hp log before)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,2,8,9,10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Shared original-caller restoration from a proved allocator body. Only
its finite free-list write footprint must avoid the wrapper save/tag bank. -/
theorem Entered.complete {R hp log before middle after} (entered : Entered R before middle)
    (windows : AllocEntry.Windows R)
    (outside : ∀ cell ∈ AllocEntry.saveCells,
      OutLRange log (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8)
    (body : AllocFinish.Post (AllocEntry.frameSp R) (R 10) hp log middle after) :
    Post R hp log before after := by
  have saved (cell : Nat × Nat) (member : cell ∈ AllocEntry.saveCells) :
      word (AllocFinish.snapshot log middle) (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat = R cell.1 := by
    simp only [AllocFinish.snapshot,word,entered.memory]
    exact AllocEntry.saved_after before.σ.mem windows log cell member (outside cell member)
  have returnWord : AllocReturn.returnWord (AllocEntry.frameSp R) hp (AllocFinish.snapshot log middle) = R 1 :=
    saved AllocReturn.slots.head! (by decide)
  have restored : AllocReturn.restored (AllocEntry.frameSp R) hp (AllocFinish.snapshot log middle) =
      callerRegs R (hp + BitVec.ofNat 64 Layout.header_bytes) := by
    have stack : AllocEntry.frameSp R + AllocReturn.frameSize = R 2 := by
      change (R 2 + -AllocReturn.frameSize) + AllocReturn.frameSize = R 2
      rw [BitVec.add_neg_eq_sub,BitVec.sub_add_cancel]
    unfold AllocReturn.restored callerRegs
    rw [stack]
    congr 2
    apply List.map_congr_left
    intro cell member
    exact congrArg (fun value => (cell.1,value)) (saved cell (AllocEntry.restore_cells _ (List.mem_reverse.mp member)))
  refine ⟨body.good,body.tick,body.minstret,body.code,?_,?_,body.result,?_,body.output.trans entered.output,?_⟩
  · simpa only [returnWord] using body.pc
  · simpa only [restored] using body.registers
  · have same : middle.σ.mem = (prepared R before).σ.mem := entered.memory
    rw [body.memory,AllocFinish.effect_of_memory same,entered.memory,effect,writeLog_append]
  · intro r noise untouched
    exact (body.native r noise untouched).trans (entered.native r noise untouched)

/-- Original size/tag agreement after either proved wrapper route. The
free-list log must preserve the native slot holding the requested tag. -/
theorem header_of_effect {R hp log before after}
    (memory : after.σ.mem = writeLog before.σ.mem (effect R hp log before))
    (windows : AllocEntry.Windows R)
    (tagOutside : OutLRange log (AllocEntry.frameSp R + BitVec.ofNat 64 AllocEntry.tagOffset).toNat 8)
    (sizeBound : (R 10).toNat < 2^54)
    (separate : hp.toNat + 8 ≤ Layout.sym_caml_allocated_words ∨ Layout.sym_caml_allocated_words + 8 ≤ hp.toNat)
    (tagBound : (R 11).toNat < 256) :
    HeaderOk (word after hp.toNat) (R 10).toNat (R 11).toNat := by
  have memory' : after.σ.mem = writeLog (prepared R before).σ.mem
      (AllocFinish.effect (AllocEntry.frameSp R) (R 10) hp log (prepared R before)) := by
    rw [memory,effect,writeLog_append]
    rfl
  have savedTag : word (AllocFinish.snapshot log (prepared R before))
      (AllocEntry.frameSp R + BitVec.ofNat 64 AllocEntry.tagOffset).toNat = R 11 :=
    AllocEntry.saved_after before.σ.mem windows log (11,AllocEntry.tagOffset)
      (by simp [AllocEntry.saveCells]) tagOutside
  have tagBound' : (word (AllocFinish.snapshot log (prepared R before))
      (AllocEntry.frameSp R + BitVec.ofNat 64 AllocEntry.tagOffset).toNat).toNat < 256 := by
    rw [savedTag]
    exact tagBound
  have header := AllocFinish.header_of_effect memory' separate sizeBound tagBound'
  simpa only [savedTag] using header

end OCaml.Vm.Gc.AllocWrapperCore
