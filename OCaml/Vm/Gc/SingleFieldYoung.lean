import OCaml.Vm.Gc.SingleFieldNonYoung
import OCaml.Vm.Gc.FreshEntry

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Actual nursery observations after publishing the parent's forwarding
pointer. Ownership must keep the domain and its bounds readable. -/
structure YoungConditions (q : PendingCopy) (root domain : BitVec 64) (c : Config) : Prop where
  domainRoot : word (forwardedSnapshot q root c) Layout.sym_Caml_state = domain
  windows : Young.Windows domain
  lower : (Young.lowerWord domain (forwardedSnapshot q root c)).toNat < (child q root c).toNat
  upper : (child q root c).toNat < (Young.upperWord domain (forwardedSnapshot q root c)).toNat

theorem YoungConditions.of_memory {q root domain before after} (memory : after.σ.mem = before.σ.mem)
    (conditions : YoungConditions q root domain before) : YoungConditions q root domain after := by
  have same := forwardedSnapshot_memory (q := q) (root := root) memory
  refine ⟨?_,conditions.windows,?_,?_⟩
  · simpa only [word,same] using conditions.domainRoot
  · simpa only [Young.lowerWord,word,same,child_of_memory memory] using conditions.lower
  · simpa only [Young.upperWord,word,same,child_of_memory memory] using conditions.upper

/-- Tail-loop boundary: the captured child is still the original word,
while the parent already has its forwarding header and updated root.
The destination field has not yet been initialized. -/
structure YoungHead (q : PendingCopy) (root sp : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt OldifyYoung.exitPc after
  value : gprGet after.σ 8 = some (child q root before)
  target : gprGet after.σ 9 = some q.target
  stack : gprGet after.σ 2 = some sp
  constants : GHolds after.σ Fresh.loopConstants
  memory : after.σ.mem = writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [8,9,14,15,25], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Execute the actual accepted nursery tests for the captured child,
retaining the native frame and the constants installed by oldify's prologue. -/
theorem Classified.young_head {q root sp domain before middle}
    (classified : Classified q root before middle) (stack : gprGet before.σ 2 = some sp)
    (constants : GHolds before.σ Fresh.loopConstants)
    (conditions : YoungConditions q root domain before) :
    FnSummary OldifyYoung.pc (fun d => d = middle) (YoungHead q root sp before) := by
  have memory : middle.σ.mem = (forwardedSnapshot q root before).σ.mem := classified.memory
  have domainRegister : gprGet before.σ 18 = some (BitVec.ofNat 64 Layout.sym_Caml_state) :=
    gholds_lookup _ constants rfl
  have input : OldifyYoung.Input (child q root before) domain middle :=
    { good := classified.good
      minstret := classified.minstret
      tick := classified.tick
      code := classified.code
      registers := ⟨(classified.native Register.x18 (by decide) (by decide)).trans
        domainRegister,gholds_lookup _ classified.registers rfl,True.intro⟩
      root := by simpa only [word,memory] using conditions.domainRoot
      windows := conditions.windows
      lower := by simpa only [Young.lowerWord,word,memory] using conditions.lower
      upper := by simpa only [Young.upperWord,word,memory] using conditions.upper }
  apply (OldifyYoung.young_machine input).weaken (fun _ h => h)
  intro after ranged
  have native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ [8,9,14,15,25], (gprReg n == r) = false) →
      after.σ.regs.get? r = before.σ.regs.get? r := by
    intro r noise untouched
    have rangeCover : ∀ n ∈ [14,15,25], n ∈ [8,9,14,15,25] := by decide
    have classCover : ∀ n ∈ [8,9,14,15], n ∈ [8,9,14,15,25] := by decide
    exact (ranged.machine.frame_subset OldifyYoung.written r noise
      (fun n hn => untouched n (rangeCover n hn))).trans
      (classified.native r noise (fun n hn => untouched n (classCover n hn)))
  refine ⟨ranged.machine.good,ranged.machine.tick,ranged.machine.minstret,ranged.code,ranged.pc,
    gholds_lookup _ ranged.registers rfl,?_,?_,?_,ranged.memory.trans classified.memory,
    ranged.machine.output.trans classified.output,native⟩
  · exact (ranged.machine.frame_subset OldifyYoung.written Register.x9 (by decide) (by decide)).trans classified.target
  · exact (native Register.x2 (by decide) (by decide)).trans stack
  · apply gholds_of_frame native _ (by change KeysOK [18,19,20,21,22,23]; decide) ?_ ?_ constants
    · change ∀ n ∈ [18,19,20,21,22,23], ∀ q ∈ noiseRegs, (q == gprReg n) = false
      decide
    · change ∀ n ∈ [18,19,20,21,22,23], ∀ m ∈ [8,9,14,15,25], (gprReg m == gprReg n) = false
      decide

/-- Forward a single-field parent and follow its young child directly to
the header classifier, without executing a second native prologue. -/
theorem prepare_young {q root sp domain c} (input : Input q root c)
    (stack : gprGet c.σ 2 = some sp) (constants : GHolds c.σ Fresh.loopConstants)
    (even : ChildClassify.even (child q root c) = true)
    (range : YoungConditions q root domain c) :
    FnSummary pc (fun d => d = c) (YoungHead q root sp c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_classify input).run
  intro middle classified
  have pc : PCAt OldifyYoung.pc middle := by
    simpa only [even,ChildClassify.exitPc,OldifyYoung.pc,ite_true] using classified.pc
  exact (classified.young_head stack constants range).run middle ⟨pc,rfl⟩

end OCaml.Vm.Gc.SingleField
