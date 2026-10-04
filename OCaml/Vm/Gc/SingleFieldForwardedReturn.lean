import OCaml.Vm.Gc.SingleObject
import OCaml.Vm.Gc.SingleFieldForwarded

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The child result read from the parent's forwarded-memory snapshot. -/
def forwardedValue (q : PendingCopy) (root : BitVec 64) (c : Config) : BitVec 64 :=
  word (forwardedSnapshot q root c) (child q root c).toNat

def forwardedEffect (q : PendingCopy) (root : BitVec 64) (c : Config) : List WEntry :=
  Enqueue.prefixLog q.source q.target root ++ [(q.target.toNat,8,forwardedValue q root c)]

structure ForwardedReturnConditions (q : PendingCopy) (root sp : BitVec 64) (c : Config) : Prop
    extends ForwardedConditions q root sp c where
  prefixOutside : ∀ off ∈ OldifyReturn.offsets,
    OutLRange (Enqueue.prefixLog q.source q.target root) (sp + BitVec.ofNat 64 off).toNat 8

/-- Complete single-field route when its young child is already forwarded.
The saved native words are those before forwarding the parent. -/
structure ForwardedReturned (q : PendingCopy) (root sp : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt (OldifyReturn.returnWord sp before) after
  registers : GHolds after.σ (OldifyReturn.restored sp before)
  memory : after.σ.mem = writeLog before.σ.mem (forwardedEffect q root before)
  value : word after q.target.toNat = forwardedValue q root before
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ (wrChain Forwarded.blocks ++ wrChain OldifyReturn.blocks) ++ [8,9,14,15,25],
      (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

/-- The actual child return composes with the forwarding prefix and the
same saved bank; the child forwarding word supplies the final field. -/
theorem YoungHead.finish_forwarded {q root sp before middle}
    (head : YoungHead q root sp before middle)
    (conditions : ForwardedReturnConditions q root sp before) :
    FnSummary Forwarded.pc (fun d => d = middle) (ForwardedReturned q root sp before) := by
  have memory : middle.σ.mem = (forwardedSnapshot q root before).σ.mem := head.memory
  have same := OldifyReturn.SavedSame.of_writeLog head.memory conditions.prefixOutside
  apply (head.forwarded_return conditions.toForwardedConditions).weaken (fun _ h => h)
  intro after returned
  refine ⟨returned.good,returned.tick,returned.minstret,returned.code,?_,?_,?_,?_,
    returned.output.trans head.output,?_⟩
  · simpa only [same.returnWord] using returned.pc
  · simpa only [same.restored] using returned.registers
  · rw [returned.memory]
    have childWord : word middle (child q root before).toNat = forwardedValue q root before := by
      simp only [forwardedValue,word,memory]
    rw [childWord,head.memory,forwardedEffect,writeLog_append]
  · simpa only [forwardedValue,word,memory] using returned.rootWord
  · intro r noise outside
    exact (returned.native r noise (fun n hn => outside n (List.mem_append_left _ hn))).trans
      (head.native r noise (fun n hn => outside n (List.mem_append_right _ hn)))

/-- Actual forwarding, tag/range tests, zero-header child path and original
native-bank return. This includes a self-pointer once its forwarding
observations are supplied by the parent prefix. -/
theorem return_young_forwarded {q root sp domain c} (input : Input q root c)
    (stack : gprGet c.σ 2 = some sp) (constants : GHolds c.σ Fresh.loopConstants)
    (even : ChildClassify.even (child q root c) = true)
    (range : YoungConditions q root domain c)
    (conditions : ForwardedReturnConditions q root sp c) :
    FnSummary pc (fun d => d = c) (ForwardedReturned q root sp c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_young input stack constants even range).run
  intro middle head
  have pc : PCAt Forwarded.pc middle := by
    simpa only [OldifyYoung.exitPc,Forwarded.pc] using head.pc
  exact (head.finish_forwarded conditions).run middle ⟨pc,rfl⟩

/-- A forwarded child's final store is the typed relocation image of the
original field. The forwarding table supplies the typed target equation;
no post-state representation or collector execution is assumed. -/
theorem ForwardedReturned.payload {q root sp before after pl cp tag value μ}
    (post : ForwardedReturned q root sp before after)
    (object : ObjAt before pl cp q.source.toNat (.block tag [value]))
    (rootOutside : OutLRange [(root.toNat,8,q.target)] q.source.toNat 8)
    (forwarding : forwardedValue q root before =
      Reloc.relocWord μ pl value (child q root before)) :
    (Reloc.Eqv.val value id).P (Reloc.reloc μ pl) q.target.toNat after := by
  apply single_field_relocated object
  rw [post.value,forwarding,child_original rootOutside]

end OCaml.Vm.Gc.SingleField
