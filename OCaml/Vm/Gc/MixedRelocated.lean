import OCaml.Vm.Gc.MixedLoop
import OCaml.Vm.Gc.RelocatedPayload
import OCaml.Vm.Gc.ScanPayload

namespace OCaml.Vm.Gc.MixedField
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc Vsa.Logic LeanRV64DExecutable

abbrev RelocatedPost (maps : Nat → Nat → BitVec 64) (a b : Nat) (fields : List Val)
    (initial : Config) (expected : Nat → BitVec 64) (pl : Place) (μ : Nat → Nat)
    (cp : ChanPlace) (tag : Nat) :=
  FieldCopy.RelocatedResult (LoopAt maps a b fields.length 1 initial expected fields.length)
    pl μ cp tag b fields

/-- The mixed concrete suffix produces ObjAt at the new placement using the
shared Eqv transport. Stable copied fields and forwarded young fields supply
their respective typed expected words; fresh allocation is still separate. -/
theorem scan_relocated {maps domain a b fields initial expected pl μ cp tag}
    (data : LoopData maps domain a b fields.length 1 initial expected)
    (grey : FieldCopy.RelocatingGrey a b fields pl μ initial)
    (firstOutside : OutWRange (MopupCall.scanFootprint (maps 1) b 1 fields.length) b 8)
    (header : HeaderOk (word initial (b - 8)) fields.length tag)
    (observed : ∀ i v, fields[i]? = some v → 1 ≤ i →
      expected i = relocWord μ pl v (word initial (a + 8 * i))) :
    Triple (LoopAt maps a b fields.length 1 initial expected 1)
      (RelocatedPost maps a b fields initial expected pl μ cp tag) := by
  apply (mixed_scan data).conseq (fun _ h => h)
  intro c post
  exact ⟨post, post.scan.relocated_object grey firstOutside data.headerOutside header observed⟩

/-- Initialize the mixed invariant from the concrete platform and native
pins. The initial index is strictly below the count because setup sends an
empty suffix directly to the outer queue test. -/
theorem LoopAt.initial {maps domain a b count start c expected}
    (data : LoopData maps domain a b count start c expected)
    (good : GoodState c.σ)
    (minstret : ∃ v, c.σ.regs.get? Register.minstret = some v)
    (tick : c.tick < 2) (code : Code.Caml_oldify_mopupLoaded c.σ.mem)
    (oldifyCode : Code.Caml_oldify_oneLoaded c.σ.mem)
    (bound : start < count) (pc : PCAt FieldCopy.pc c)
    (registers : GHolds c.σ (ForwardedField.carried (maps start))) :
    LoopAt maps a b count start c expected start c := by
  refine ⟨FieldCopy.ScanAtWith.initial good minstret tick code (Nat.le_of_lt bound)
    (by simpa only [ite_eq_left bound] using pc) ?_, oldifyCode, registers⟩
  have pins : GHolds c.σ (FieldCopy.regs (maps start 8) (maps start 18) (maps start 19) (maps start 9)) :=
    ⟨gholds_lookup _ registers rfl, gholds_lookup _ registers rfl,
      gholds_lookup _ registers rfl, gholds_lookup _ registers rfl, True.intro⟩
  simpa only [data.slot start (Nat.le_refl _) bound, data.delta start (Nat.le_refl _) bound,
    data.target start (Nat.le_refl _) bound, data.index start (Nat.le_refl _) bound] using pins

end OCaml.Vm.Gc.MixedField
