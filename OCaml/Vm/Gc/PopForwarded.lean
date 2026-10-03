import OCaml.Vm.Gc.PopFirstSetup
import OCaml.Vm.Gc.QueueWindows
import Vsa.Sim.FrameComposition

namespace OCaml.Vm.Gc.WorkQueue
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc LeanRV64DExecutable

/-- Predicted suffix-register map, obtained by the actual first call and
setup. Its values depend only on the initial native pins and queue head. -/
def suffixRegs (R : Nat → BitVec 64) (q : PendingCopy) (c : Config) :=
  ForwardedField.setupResult (afterFirst R q c) q.source.toNat q.target.toNat

/-- The first slot is outside the native save interval and scanned suffix. -/
theorem first_outside {R domain a b count initial expected}
    (data : ForwardedField.LoopData R domain a b count 1 initial expected) (large : 1 < count) :
    OutWRange (MopupCall.scanFootprint R b 1 count) b 8 := by
  refine ⟨?_, Or.inl (by change b + 8 ≤ b + 8; exact Nat.le_refl _), True.intro⟩
  have separate := data.stack
  rcases separate with below | above
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

/-- A pending object has been popped and completely scanned at the new
placement, with the remaining queue and all external machine frames kept. -/
structure PopForwardedPost (R : Nat → BitVec 64) (q : PendingCopy) (qs : List PendingCopy)
    (fields : List Val) (pl : Place) (μ : Nat → Nat) (cp : ChanPlace) (tag : Nat)
    (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_mopupLoaded after.σ.mem
  oldifyCode : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt FieldCopy.exitPc after
  object : ObjAt after (reloc μ pl) cp q.target.toNat (.block tag fields)
  queue : View qs pl after
  memory : FrameOn (firstFootprint R q ++ MopupCall.scanFootprint R q.target.toNat 1 fields.length)
    before.σ.mem after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,8,9,10,11,12,14,15,18,19], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Complete real pending-object traversal when its first child and suffix
children are already-forwarded young values. Every intermediate input comes
from executed code plus initial heap/native observations and separation. -/
theorem pop_forwarded {R domain q qs fields pl μ cp tag c expected}
    (input : PopInput q qs pl c) (ready : FirstReady R domain q c)
    (separate : FirstSeparation R q qs c)
    (data : ForwardedField.LoopData (suffixRegs R q c) domain q.source.toNat q.target.toNat fields.length 1 c expected)
    (outside : ForwardedField.LoopOutside (suffixRegs R q c) domain q.source.toNat q.target.toNat fields.length 1 c
      (firstFootprint R q))
    (queueOutside : OutsideWindows qs (MopupCall.scanFootprint R q.target.toNat 1 fields.length))
    (large : 1 < fields.length) (one : R 24 = 1#64)
    (header : HeaderOk (word c (q.target.toNat - 8)) fields.length tag)
    (grey : (pendingPayload q fields).P pl q.target.toNat c)
    (firstForwarding : ∀ v, fields[0]? = some v →
      word c (word c q.target.toNat).toNat = relocWord μ pl v (word c q.target.toNat))
    (observed : ∀ i v, fields[i]? = some v → 1 ≤ i →
      expected i = relocWord μ pl v (word c (q.source.toNat + 8 * i))) :
    FnSummary MopupPop.pc (fun d => d = c) (PopForwardedPost R q qs fields pl μ cp tag c) := by
  constructor
  apply Vsa.Logic.Triple.seq (pop_first input ready separate).run
  intro middle poppedFirst
  have memory := poppedFirst.memory_frame ready
  have setupInput := poppedFirst.setup_input ready data.geometry large one data.header outside.header
  have middleGrey := poppedFirst.grey_frame ready data.geometry grey firstForwarding outside.source
  have middleHeader : HeaderOk (word middle (q.target.toNat - 8)) fields.length tag := by
    rw [frame_word memory outside.header]
    exact header
  have middleObserved : ∀ i v, fields[i]? = some v → 1 ≤ i →
      expected i = relocWord μ pl v (word middle (q.source.toNat + 8 * i)) := by
    intro i v member lower
    have bound : i < fields.length := (List.getElem?_eq_some_iff.mp member).1
    have same := frame_word memory (outside.source i lower bound)
    rw [data.geometry.sourceRange.ptr_nat (Nat.le_of_lt bound)] at same
    rw [same]
    exact observed i v member lower
  have firstOutside := first_outside data large
  obtain ⟨after, run, scanned⟩ := (ForwardedField.setup_relocated (cp := cp)
    setupInput (data.frame outside memory) poppedFirst.setup_carried poppedFirst.oldifyCode middleGrey
    firstOutside middleHeader middleObserved).run middle ⟨poppedFirst.pc,rfl⟩
  have scannedMemory : FrameOn (MopupCall.scanFootprint R q.target.toNat 1 fields.length) middle.σ.mem after.σ.mem :=
    scanned.memory
  refine ⟨after, run, ⟨scanned.good, scanned.minstret, scanned.tick, scanned.code, scanned.oldifyCode,
    scanned.pc, scanned.object, poppedFirst.queue.frame_windows queueOutside scannedMemory,
    frameOn_comp memory scannedMemory, scanned.output.trans poppedFirst.output, ?_⟩⟩
  intro r noise untouched
  apply (scanned.native r noise ?_).trans (poppedFirst.native r noise ?_)
  · intro n member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact untouched _ (by decide)
  · intro n member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact untouched _ (by decide)

end OCaml.Vm.Gc.WorkQueue
