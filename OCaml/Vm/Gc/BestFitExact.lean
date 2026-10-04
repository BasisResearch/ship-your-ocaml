import OCaml.Vm.Gc.BestFitEmpty

namespace OCaml.Vm.Gc.BestFitExact
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable BestFitSmall

/-- Exact-size small-list allocation. Both branch decisions are read from
initial memory. Repair and bitmap separation are required only on routes
that actually perform those accesses. -/
structure Input (ra size : BitVec 64) (c : Config) : Prop extends CoreInput ra size c where
  repair : cursor size c = first size c → RepairConditions size c
  bitmap : next size c = 0 → OutLRange (BestFitEmpty.effect size c) Layout.sym_bf_small_map 4

def effect (size : BitVec 64) (c : Config) : List WEntry :=
  if next size c = 0 then BestFitEmpty.allocationEffect size c else selectedEffect size c

/-- Uniform result for all four exact-size small-list branches. This gives
actual execution and accounting, not a complete free-list ownership invariant. -/
structure Post (ra size : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded after.σ.mem
  pc : PCAt ra after
  result : gprGet after.σ 10 = some (first size before - BitVec.ofNat 64 Layout.header_bytes)
  memory : after.σ.mem = writeLog before.σ.mem (effect size before)
  counter : total after = total before - 1#64 - size
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Complete real exact-size small-list allocation, covering empty and
nonempty successors and both merge-cursor branches. -/
theorem allocate {ra size c} (input : Input ra size c) :
    FnSummary BestFitSmall.pc (fun d => d = c) (Post ra size c) := by
  by_cases empty : next size c = 0
  · have pathInput : BestFitEmpty.Input ra size c :=
      ⟨input.toCoreInput,empty,input.repair,input.bitmap empty⟩
    apply (BestFitEmpty.allocate pathInput).weaken (fun _ h => h)
    intro after post
    exact ⟨post.good,post.tick,post.minstret,post.code,post.pc,post.result,
      by simpa only [effect,empty,ite_true] using post.memory,
      post.counter,post.output,post.native⟩
  · have pathInput : NonemptyInput ra size c :=
      ⟨⟨input.toCoreInput,empty⟩,input.repair⟩
    apply (allocate_nonempty pathInput).weaken (fun _ h => h)
    intro after post
    have counter : total after = total c - 1#64 - size := by
      by_cases repair : cursor size c = first size c
      · have repaired : RepairPost ra size c after := by
          simpa only [NonemptyPost,selectedBlocks,selectedEffect,repair,ite_true,RepairPost] using post
        exact RepairPost.counter repaired
      · have kept : BestFitSmall.Post ra size c after := by
          simpa only [NonemptyPost,selectedBlocks,selectedEffect,repair,ite_false] using post
        exact BestFitSmall.Post.counter kept
    have cover : ∀ n ∈ wrChain (selectedBlocks size c), n ∈ [10,11,12,13,14,15] := by
      unfold selectedBlocks
      split
      · exact repair_written
      · exact BestFitSmall.written
    exact ⟨post.machine.good,post.machine.tick,post.machine.minstret,post.code,post.pc,post.result,
      by simpa only [effect,empty,ite_false] using post.memory,
      counter,post.machine.output,fun r noise outside =>
        post.machine.frame r noise (fun n hn => outside n (cover n hn))⟩

/-- All exact-size paths consume exactly the payload plus header when the
initial free-word counter has sufficient credit. -/
theorem Post.counter_nat {ra size before after} (post : Post ra size before after)
    (credit : size.toNat + 1 ≤ (total before).toNat) :
    (total after).toNat + size.toNat + 1 = (total before).toNat :=
  accounting_nat post.counter credit

end OCaml.Vm.Gc.BestFitExact
