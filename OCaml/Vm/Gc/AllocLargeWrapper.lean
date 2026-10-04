import OCaml.Vm.Gc.AllocLarge
import OCaml.Vm.Gc.AllocWrapperCore

namespace OCaml.Vm.Gc.AllocLargeWrapper
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def resultHeader (R : Nat → BitVec 64) (c : Config) :=
  AllocLarge.resultHeader (AllocEntry.frameSp R) (R 10) (AllocWrapperCore.prepared R c)
def freeEffect (R : Nat → BitVec 64) (c : Config) :=
  AllocLarge.freeEffect (AllocEntry.frameSp R) (R 10) (AllocWrapperCore.prepared R c)

def effect (R : Nat → BitVec 64) (c : Config) :=
  AllocWrapperCore.effect R (resultHeader R c) (freeEffect R c) c

theorem prepared_memory {R before after} (memory : after.σ.mem = before.σ.mem) :
    (AllocWrapperCore.prepared R after).σ.mem = (AllocWrapperCore.prepared R before).σ.mem := by
  simp only [AllocWrapperCore.prepared,memory]

theorem resultHeader_of_memory {R before after} (memory : after.σ.mem = before.σ.mem) :
    resultHeader R after = resultHeader R before := AllocLarge.resultHeader_of_memory (prepared_memory memory)

theorem freeEffect_of_memory {R before after} (memory : after.σ.mem = before.σ.mem) :
    freeEffect R after = freeEffect R before := AllocLarge.freeEffect_of_memory (prepared_memory memory)

theorem effect_of_memory {R before after} (memory : after.σ.mem = before.σ.mem) :
    effect R after = effect R before := by
  unfold effect AllocWrapperCore.effect
  rw [resultHeader_of_memory memory,freeEffect_of_memory memory,
    AllocFinish.effect_of_memory (prepared_memory memory)]

/-- Initial-memory conditions for the least-large-block wrapper route.
The native/heap ownership invariant supplies the finite save-bank separation. -/
structure Conditions (R : Nat → BitVec 64) (c : Config) : Prop where
  body : AllocLarge.Conditions (AllocEntry.frameSp R) (R 10) (AllocWrapperCore.prepared R c)
  freeOutside : ∀ cell ∈ AllocEntry.saveCells, OutLRange (freeEffect R c)
    (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8

theorem Conditions.of_memory {R before after} (memory : after.σ.mem = before.σ.mem)
    (conditions : Conditions R before) : Conditions R after := by
  refine ⟨conditions.body.of_memory (prepared_memory memory),?_⟩
  simpa only [freeEffect_of_memory memory] using conditions.freeOutside

theorem effect_high {R c} (windows : AllocEntry.Windows R) (conditions : Conditions R c) :
    ∀ e ∈ effect R c, Layout.sym_tohost + 16 ≤ e.1 := by
  intro e member
  rw [effect,AllocWrapperCore.effect,List.mem_append] at member
  rcases member with member | member
  · exact AllocEntry.effect_high windows e member
  · exact AllocFinish.effect_high
      (BestFitFallback.completeEffect_high conditions.body.toStackConditions conditions.body.large)
      conditions.body.continuation e member

structure Input (R : Nat → BitVec 64) (c : Config) : Prop
    extends AllocEntry.Input R BestFitSmall.pc c, Conditions R c where
  freeCode : Code.Bf_allocateLoaded c.σ.mem
  ffsCode : Code.FfsLoaded c.σ.mem
  splitCode : Code.Bf_splitLoaded c.σ.mem

abbrev Post (R : Nat → BitVec 64) (before after : Config) :=
  AllocWrapperCore.Post R (resultHeader R before) (freeEffect R before) before after

/-- Actual wrapper entry, indirect call, complete least-large-block allocation,
color/header/accounting and original caller restoration. -/
theorem allocate {R c} (input : Input R c) :
    FnSummary AllocEntry.pc (fun d => d = c) (Post R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (AllocWrapperCore.enter input.toInput).run
  intro callee entered
  have memory : callee.σ.mem = (AllocWrapperCore.prepared R c).σ.mem := entered.memory
  have conditions := input.body.of_memory memory
  have freeInput : AllocLarge.Input (AllocEntry.frameSp R) (R 10) callee :=
    { toConditions := conditions
      good := entered.good
      tick := entered.tick
      minstret := entered.minstret
      code := entered.image input.windows Code.bf_allocate_transport (by decide) input.freeCode
      registers := ⟨entered.link,gholds_lookup _ entered.registers rfl,
        gholds_lookup _ entered.registers rfl,True.intro⟩
      ffsCode := entered.image input.windows Code.ffs_transport (by decide) input.ffsCode
      splitCode := entered.image input.windows Code.bf_split_transport (by decide) input.splitCode
      wrapperCode := entered.code
      sizeRegister := gholds_lookup _ entered.registers rfl }
  obtain ⟨after,run,finished⟩ := (AllocLarge.allocate freeInput).run callee ⟨entered.pc,rfl⟩
  have outside : ∀ cell ∈ AllocEntry.saveCells,
      OutLRange (AllocLarge.freeEffect (AllocEntry.frameSp R) (R 10) callee)
        (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8 := by
    simpa only [AllocLarge.freeEffect_of_memory memory,freeEffect] using input.freeOutside
  have complete := entered.complete input.windows outside finished
  refine ⟨after,run,?_⟩
  simpa only [AllocLarge.resultHeader_of_memory memory,AllocLarge.freeEffect_of_memory memory,
    Post,resultHeader,freeEffect] using complete

end OCaml.Vm.Gc.AllocLargeWrapper
