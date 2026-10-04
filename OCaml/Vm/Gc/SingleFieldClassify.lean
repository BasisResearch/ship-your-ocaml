import OCaml.Vm.Gc.SingleField
import OCaml.Vm.Gc.ChildClassify

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def child (q : PendingCopy) (root : BitVec 64) (c : Config) :=
  bytesVal .ld ((WorkQueue.enqueueLoads q root c).headD [])

structure Classified (q : PendingCopy) (root : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt (ChildClassify.exitPc (ChildClassify.even (child q root before))) after
  registers : GHolds after.σ (ChildClassify.classified (child q root before))
  target : gprGet after.σ 9 = some q.target
  memory : after.σ.mem = writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [8,9,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Single-field forwarding followed by actual child classification. Both
routes preserve the new destination and original native frame. -/
theorem prepare_classify {q root c} (input : Input q root c) :
    FnSummary pc (fun d => d = c) (Classified q root c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare input).run
  intro middle prepared
  have childInput : ChildClassify.Input (child q root c) middle :=
    ⟨prepared.machine.good,prepared.machine.tick,prepared.machine.minstret,prepared.code,
      ⟨gholds_lookup _ prepared.registers rfl,True.intro⟩⟩
  obtain ⟨after,run,tested⟩ := (ChildClassify.classify childInput).run middle ⟨prepared.pc,rfl⟩
  have target : gprGet after.σ 9 = gprGet middle.σ 9 := by
    exact tested.machine.frame_subset (ChildClassify.written _) Register.x9 (by decide) (by decide)
  refine ⟨after,run,⟨tested.machine.good,tested.machine.tick,tested.machine.minstret,tested.code,
    tested.pc,tested.registers,target.trans (gholds_lookup _ prepared.registers rfl),
    tested.memory.trans prepared.memory,tested.machine.output.trans prepared.machine.output,?_⟩⟩
  intro r noise untouched
  apply (tested.machine.frame_subset (ChildClassify.written _) r noise (fun n hn => untouched n (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn ⊢
    rcases hn with rfl | rfl <;> simp))).trans
  apply prepared.machine.frame_subset written r noise
  intro n hn
  apply untouched n
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn ⊢
  rcases hn with rfl | rfl <;> simp

end OCaml.Vm.Gc.SingleField
