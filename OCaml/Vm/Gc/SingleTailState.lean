import OCaml.Vm.Gc.SingleFieldBackEdge
import OCaml.Vm.Gc.NativeRestore
import OCaml.Vm.Gc.ForwardingComplete

namespace OCaml.Vm.Gc.SingleTail
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def tailWrites : List Nat := [1,2,8,9,10,11,12,13,14,15,24,25]
def exitWrites : List Nat := [1,2,8,9,10,11,12,13,14,15,18,19,20,21,22,23,24,25]

/-- Ordinary size-one copying boundary on a fixed native frame. Published
forwarding entries and the original saved bank are retained across every
iteration. Typed pending payloads and global ownership are separate obligations. -/
structure Head (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (copies : List PendingCopy) (q : PendingCopy) (root : BitVec 64) (c : Config) : Prop where
  input : SingleField.Input q root c
  pc : PCAt SingleField.pc c
  stack : gprGet c.σ 2 = some sp
  constants : GHolds c.σ Fresh.loopConstants
  member : q.source ∈ sources
  fresh : word c (q.source - 8#64).toNat ≠ 0
  table : (ForwardingTable.eqv copies).P pl 0 c
  complete : ForwardingTable.Complete sources copies c
  saved : OldifyReturn.SavedSame sp initial c
  output : c.σ.sailOutput = initial.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ tailWrites, (gprReg n == r) = false) → c.σ.regs.get? r = initial.σ.regs.get? r

/-- Initialize the operational invariant at an actual allocated size-one
copying boundary; the saved bank and output start by reflexivity. -/
theorem Head.start {sp sources pl initial copies q root}
    (input : SingleField.Input q root initial) (pc : PCAt SingleField.pc initial)
    (stack : gprGet initial.σ 2 = some sp) (constants : GHolds initial.σ Fresh.loopConstants)
    (member : q.source ∈ sources) (fresh : word initial (q.source - 8#64).toNat ≠ 0)
    (table : (ForwardingTable.eqv copies).P pl 0 initial)
    (complete : ForwardingTable.Complete sources copies initial) :
    Head sp sources pl initial copies q root initial :=
  ⟨input,pc,stack,constants,member,fresh,table,complete,fun _ _ => rfl,rfl,fun _ _ _ => rfl⟩

/-- Either concrete allocation back edge re-establishes the operational
partial-relocation invariant with one additional published parent. -/
theorem Head.advance {sp sources pl initial copies q root before after payload log}
    (head : Head sp sources pl initial copies q root before)
    (post : SingleField.BackEdgeResult q root sp payload copies sources log pl before after)
    (conditions : SingleField.BackEdgeConditions q root sp payload copies sources log before) :
    Head sp sources pl initial (q :: copies) ⟨SingleField.child q root before,payload⟩ q.target after := by
  refine ⟨post.next_input,?_,post.allocated.stack,post.allocated.constants,post.member,
    post.fresh,post.table,?_,?_,post.allocated.output.trans head.output,?_⟩
  · simpa only [Enqueue.pc,SingleField.pc] using post.allocated.pc
  · exact head.complete.extend (other_headers_preserved post.allocated.memory
      conditions.headerOutside conditions.allocationHeaders)
  · intro off member
    exact (post.saved off member).trans (head.saved off member)
  · intro r noise outside
    have cover : ∀ n ∈ [8,9,14,15,25] ++ ((1 :: wrChain Fresh.blocks) ++ [1,2,8,9,10,11,12,13,14,15]),
        n ∈ tailWrites := by decide
    exact (post.allocated.native r noise (fun n hn => outside n (cover n hn))).trans
      (head.native r noise outside)

/-- Common actual native return interface, relative to the current copying
boundary. Both epilogue orders are normalized before loop composition. -/
structure Returned (q : PendingCopy) (root sp : BitVec 64) (log : List WEntry)
    (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt (OldifyReturn.returnWord sp before) after
  registers : GHolds after.σ (OldifyReturn.restored sp before)
  memory : after.σ.mem = writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root ++ log)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ exitWrites, (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

theorem returned_plain {q root sp before after} (post : SingleField.Returned q root sp before after) :
    Returned q root sp (StoreReturn.effect (SingleField.child q root before) q.target) before after := by
  refine ⟨post.good,post.minstret,post.tick,post.code,post.pc,StoreReturn.as_oldify post.registers,
    post.memory,post.output,?_⟩
  intro r noise outside
  have cover : ∀ n ∈ wrChain StoreReturn.blocks ++ [8,9,14,15], n ∈ exitWrites := by decide
  exact post.native r noise (fun n hn => outside n (cover n hn))

theorem returned_forwarded {q root sp before after} (post : SingleField.ForwardedReturned q root sp before after) :
    Returned q root sp [(q.target.toNat,8,SingleField.forwardedValue q root before)] before after := by
  refine ⟨post.good,post.minstret,post.tick,post.code,post.pc,post.registers,post.memory,post.output,?_⟩
  intro r noise outside
  have cover : ∀ n ∈ (wrChain Forwarded.blocks ++ wrChain OldifyReturn.blocks) ++ [8,9,14,15,25],
      n ∈ exitWrites := by decide
  exact post.native r noise (fun n hn => outside n (cover n hn))

/-- Final heap/table footprints. The actual return summaries separately
supply native-stack access and saved-word restoration. -/
structure ExitFootprint (q : PendingCopy) (root : BitVec 64) (copies : List PendingCopy)
    (sources : List (BitVec 64)) (log : List WEntry) : Prop where
  headerOutside : ∀ source ∈ sources, source ≠ q.source →
    OutLRange (Enqueue.prefixLog q.source q.target root) (source - 8#64).toNat 8
  finalHeaders : ∀ source ∈ sources, OutLRange log (source - 8#64).toNat 8
  tableOutside : ForwardingTable.Outside copies (Enqueue.prefixLog q.source q.target root)
  finalTable : ForwardingTable.Outside (q :: copies) log

/-- Actual return to the initial saved link and bank, preserving the growing
forwarding table and the registers outside the complete tail/epilogue write set. -/
structure Finished (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config) (copies : List PendingCopy)
    (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  pc : PCAt (OldifyReturn.returnWord sp initial) c
  registers : GHolds c.σ (OldifyReturn.restored sp initial)
  table : (ForwardingTable.eqv copies).P pl 0 c
  complete : ForwardingTable.Complete sources copies c
  output : c.σ.sailOutput = initial.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ exitWrites, (gprReg n == r) = false) → c.σ.regs.get? r = initial.σ.regs.get? r

/-- A concrete exit shares the same publication/progress argument as the
back edges, then identifies the saved words with the initial native bank. -/
theorem Head.finish {sp sources pl initial copies q root before after log}
    (head : Head sp sources pl initial copies q root before) (post : Returned q root sp log before after)
    (footprint : ExitFootprint q root copies sources log) :
    Finished sp sources pl initial (q :: copies) after ∧ tailRemaining sources after < tailRemaining sources before := by
  refine ⟨⟨post.good,post.minstret,post.tick,post.code,?_,?_,?_,?_,post.output.trans head.output,?_⟩,?_⟩
  · simpa only [head.saved.returnWord] using post.pc
  · simpa only [head.saved.restored] using post.registers
  · exact ForwardingTable.publish_then head.table post.memory head.input.windows.source footprint.tableOutside footprint.finalTable
  · exact head.complete.extend (other_headers_preserved post.memory footprint.headerOutside footprint.finalHeaders)
  · intro r noise outside
    have cover : ∀ n ∈ tailWrites, n ∈ exitWrites := by decide
    exact (post.native r noise outside).trans (head.native r noise (fun n hn => outside n (cover n hn)))
  · exact forwarding_then_decreases post.memory head.input.windows.source head.member head.fresh
      footprint.headerOutside footprint.finalHeaders

end OCaml.Vm.Gc.SingleTail
