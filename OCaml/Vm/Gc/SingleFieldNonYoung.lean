import OCaml.Vm.Gc.SingleFieldReturn
import OCaml.Vm.Gc.OldifyNonYoung

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def forwardedSnapshot (q : PendingCopy) (root : BitVec 64) (c : Config) : Config :=
  {c with σ := {c.σ with mem := writeLog c.σ.mem (Enqueue.prefixLog q.source q.target root)}}

/-- Actual range observations after forwarding. The ownership invariant
must supply the runtime domain pointer and valid nursery bound windows. -/
structure RangeConditions (q : PendingCopy) (root domain : BitVec 64) (c : Config) : Prop where
  domainRoot : word (forwardedSnapshot q root c) Layout.sym_Caml_state = domain
  windows : Young.Windows domain
  outside : ¬ ((Young.lowerWord domain (forwardedSnapshot q root c)).toNat < (child q root c).toNat ∧
    (child q root c).toNat < (Young.upperWord domain (forwardedSnapshot q root c)).toNat)

theorem forwardedSnapshot_memory {q root before after} (memory : after.σ.mem = before.σ.mem) :
    (forwardedSnapshot q root after).σ.mem = (forwardedSnapshot q root before).σ.mem := by
  simp only [forwardedSnapshot,memory]

theorem RangeConditions.of_memory {q root domain before after} (memory : after.σ.mem = before.σ.mem)
    (conditions : RangeConditions q root domain before) : RangeConditions q root domain after := by
  have same := forwardedSnapshot_memory (q := q) (root := root) memory
  refine ⟨?_,conditions.windows,?_⟩
  · simpa only [word,same] using conditions.domainRoot
  · simpa only [Young.lowerWord,Young.upperWord,word,same,child_of_memory memory] using conditions.outside

/-- Execute both possible rejection edges after the real even-child branch,
reaching the same return boundary as an immediate child. -/
theorem Classified.nonYoung_ready {q root sp domain before middle}
    (classified : Classified q root before middle) (stack : gprGet before.σ 2 = some sp)
    (domainRegister : gprGet before.σ 18 = some (BitVec.ofNat 64 Layout.sym_Caml_state))
    (conditions : RangeConditions q root domain before) :
    FnSummary OldifyYoung.pc (fun d => d = middle) (ReturnReady q root sp before) := by
  have memory : middle.σ.mem = (forwardedSnapshot q root before).σ.mem := classified.memory
  have readInput : OldifyYoung.ReadInput (child q root before) domain middle :=
    { good := classified.good
      minstret := classified.minstret
      tick := classified.tick
      code := classified.code
      registers := ⟨(classified.native Register.x18 (by decide) (by decide)).trans domainRegister,
        gholds_lookup _ classified.registers rfl,True.intro⟩
      root := by simpa only [word,memory] using conditions.domainRoot
      windows := conditions.windows }
  have outside : ¬ ((Young.lowerWord domain middle).toNat < (child q root before).toNat ∧
      (child q root before).toNat < (Young.upperWord domain middle).toNat) := by
    simpa only [Young.lowerWord,Young.upperWord,word,memory] using conditions.outside
  apply (OldifyYoung.nonYoung_machine readInput outside).weaken (fun _ h => h)
  intro after ranged
  have target : gprGet after.σ 9 = gprGet middle.σ 9 :=
    ranged.machine.frame_subset (OldifyYoung.reject_written _) Register.x9 (by decide) (by decide)
  have stackRange : gprGet after.σ 2 = gprGet middle.σ 2 :=
    ranged.machine.frame_subset (OldifyYoung.reject_written _) Register.x2 (by decide) (by decide)
  have stackClassified : gprGet middle.σ 2 = gprGet before.σ 2 :=
    classified.native Register.x2 (by decide) (by decide)
  refine ⟨ranged.machine.good,ranged.machine.tick,ranged.machine.minstret,ranged.code,?_,ranged.value,
    target.trans classified.target,stackRange.trans (stackClassified.trans stack),
    ranged.memory.trans classified.memory,ranged.machine.output.trans classified.output,?_⟩
  · simpa only [OldifyYoung.rejectPc,StoreReturn.pc] using ranged.pc
  · intro r noise untouched
    have rangeCover : ∀ n ∈ [14,15,25], n ∈ [8,9,14,15,25] := by decide
    have classCover : ∀ n ∈ [8,9,14,15], n ∈ [8,9,14,15,25] := by decide
    exact (ranged.machine.frame_subset (OldifyYoung.reject_written _) r noise
      (fun n hn => untouched n (rangeCover n hn))).trans
      (classified.native r noise (fun n hn => untouched n (classCover n hn)))

/-- Complete forwarding and store/return for an even child outside the
nursery, sharing the original-bank restoration with the immediate route. -/
theorem return_even_nonYoung {q root sp domain c} (input : Input q root c)
    (stack : gprGet c.σ 2 = some sp)
    (domainRegister : gprGet c.σ 18 = some (BitVec.ofNat 64 Layout.sym_Caml_state))
    (even : ChildClassify.even (child q root c) = true)
    (range : RangeConditions q root domain c) (geometry : ReturnGeometry q root sp c) :
    FnSummary pc (fun d => d = c) (Returned q root sp c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_classify input).run
  intro middle classified
  have pc : PCAt OldifyYoung.pc middle := by
    simpa only [even,ChildClassify.exitPc,OldifyYoung.pc,ite_true] using classified.pc
  obtain ⟨readyState,run,ready⟩ := (classified.nonYoung_ready stack domainRegister range).run middle ⟨pc,rfl⟩
  obtain ⟨after,returnedRun,post⟩ := (ready.finish geometry).run readyState ⟨ready.pc,rfl⟩
  exact ⟨after,run.trans returnedRun,post⟩

end OCaml.Vm.Gc.SingleField
