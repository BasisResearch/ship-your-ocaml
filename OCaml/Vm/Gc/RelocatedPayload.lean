import OCaml.Vm.Gc.ForwardedLoop
import OCaml.Vm.Reloc
import OCaml.Vm.Gc.PendingPayload

namespace OCaml.Vm.Gc.FieldCopy
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc

/-- Grey scanned object after its first field has been handled: that field
is represented at the new placement in the copy; suffix fields still live
at the source under the original placement. The first-field machine route
and partial relocation invariant supply this boundary assertion. -/
structure RelocatingGrey (a b : Nat) (fields : List Val) (pl : Place)
    (μ : Nat → Nat) (initial : Config) : Prop where
  first : ∀ v, fields[0]? = some v → (Eqv.val v id).P (reloc μ pl) b initial
  suffix : ∀ i v, fields[i]? = some v → 1 ≤ i →
    (Eqv.val v id).P pl (a + 8 * i) initial

/-- Shared grey-boundary construction from an actual first-slot image and
unchanged source suffix. Both standalone and queue-pop compositions use the
same Eqv transport, independent of their different exact write logs. -/
theorem relocating_grey_of_pending {q : PendingCopy} {fields pl μ before after}
    (grey : (pendingPayload q fields).P pl q.target.toNat before)
    (firstImage : ∀ v, fields[0]? = some v →
      word after q.target.toNat = relocWord μ pl v (word before q.target.toNat))
    (suffixSame : ∀ i, 1 ≤ i → i < fields.length →
      word after (q.source.toNat + 8 * i) = word before (q.source.toNat + 8 * i)) :
    RelocatingGrey q.source.toNat q.target.toNat fields pl μ after := by
  constructor
  · intro v member
    apply (Eqv.val v id).transport μ pl q.target.toNat q.target.toNat before after
    · simpa only [pendingPayload, Eqv.list, Eqv.all, Eqv.guard, Eqv.val, id_eq, ite_true] using grey 0 v member
    · exact firstImage v member
  · intro i v member lower
    have bound : i < fields.length := (List.getElem?_eq_some_iff.mp member).1
    have nonzero : i ≠ 0 := by omega
    simpa only [pendingPayload, Eqv.list, Eqv.all, Eqv.guard, Eqv.val, id_eq,
      ite_eq_right nonzero, suffixSame i lower bound] using grey i v member

/-- A completed scan with typed relocation observations represents the
entire payload at the new placement. The already-handled first field is
preserved by separation; suffix transport uses Eqv's typed value action. -/
theorem ScanAtWith.relocated_payload {writes a b fields pl μ initial c expected footprint cp tag}
    (grey : RelocatingGrey a b fields pl μ initial)
    (scan : ScanAtWith writes a b fields.length 1 initial fields.length c footprint expected)
    (firstOutside : OutWRange footprint b 8)
    (observed : ∀ i v, fields[i]? = some v → 1 ≤ i →
      expected i = relocWord μ pl v (word initial (a + 8 * i))) :
    (payload cp (.block tag fields)).P (reloc μ pl) b c := by
  intro i v member
  by_cases zero : i = 0
  · subst i
    have first := grey.first v member
    have same := frame_word scan.memory firstOutside
    simpa only [Eqv.val, id_eq, Nat.mul_zero, Nat.add_zero, same] using first
  · have lower : 1 ≤ i := by omega
    have bound : i < fields.length := (List.getElem?_eq_some_iff.mp member).1
    apply (Eqv.val v id).transport μ pl (a + 8 * i) (b + 8 * i) initial c
      (grey.suffix i v member lower)
    change word c (b + 8 * i) = relocWord μ pl v (word initial (a + 8 * i))
    rw [scan.copied i lower bound, observed i v member lower]

/-- The relocated payload and preserved target header form the final object
representation. Color bits remain governed by HeaderOk's existing policy. -/
theorem ScanAtWith.relocated_object {writes a b fields pl μ initial c expected footprint cp tag}
    (grey : RelocatingGrey a b fields pl μ initial)
    (scan : ScanAtWith writes a b fields.length 1 initial fields.length c footprint expected)
    (firstOutside : OutWRange footprint b 8)
    (headerOutside : OutWRange footprint (b - 8) 8)
    (header : HeaderOk (word initial (b - 8)) fields.length tag)
    (observed : ∀ i v, fields[i]? = some v → 1 ≤ i →
      expected i = relocWord μ pl v (word initial (a + 8 * i))) :
    ObjAt c (reloc μ pl) cp b (.block tag fields) := by
  refine ⟨?_, scan.relocated_payload (cp := cp) (tag := tag) grey firstOutside observed⟩
  simpa only [frame_word scan.memory headerOutside, Obj.wosize, Obj.tag] using header

/-- A completed concrete loop together with its typed relocated object.
Different field-route invariants share this same result interface. -/
structure RelocatedResult (Loop : Config → Prop) (pl : Place) (μ : Nat → Nat)
    (cp : ChanPlace) (tag b : Nat) (fields : List Val) (c : Config) : Prop where
  loop : Loop c
  object : ObjAt c (reloc μ pl) cp b (.block tag fields)

end OCaml.Vm.Gc.FieldCopy

namespace OCaml.Vm.Gc.ForwardedField
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc Vsa.Logic

/-- Completed concrete scan and its typed relocated object. -/
abbrev RelocatedPost (R : Nat → BitVec 64) (a b : Nat) (fields : List Val)
    (initial : Config) (expected : Nat → BitVec 64) (pl : Place) (μ : Nat → Nat)
    (cp : ChanPlace) (tag : Nat) :=
  FieldCopy.RelocatedResult (LoopAt R a b fields.length 1 initial expected fields.length)
    pl μ cp tag b fields

/-- The real already-forwarded suffix loop produces a represented object
at the new placement. First-field handling and typed forwarding targets
are explicit heap obligations, not assumed collector executions. -/
theorem scan_relocated {R domain a b fields initial expected pl μ cp tag}
    (data : LoopData R domain a b fields.length 1 initial expected)
    (grey : FieldCopy.RelocatingGrey a b fields pl μ initial)
    (firstOutside : OutWRange (MopupCall.scanFootprint R b 1 fields.length) b 8)
    (header : HeaderOk (word initial (b - 8)) fields.length tag)
    (observed : ∀ i v, fields[i]? = some v → 1 ≤ i →
      expected i = relocWord μ pl v (word initial (a + 8 * i))) :
    Triple (LoopAt R a b fields.length 1 initial expected 1)
      (RelocatedPost R a b fields initial expected pl μ cp tag) := by
  apply (forwarded_scan data).conseq (fun _ h => h)
  intro c post
  exact ⟨post, post.scan.relocated_object grey firstOutside data.headerOutside header observed⟩

end OCaml.Vm.Gc.ForwardedField
