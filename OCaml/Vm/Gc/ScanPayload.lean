import OCaml.Vm.Gc.ScanLoop
import OCaml.Vm.Gc.PendingPayload

namespace OCaml.Vm.Gc.FieldCopy
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc

/-- The scan invariant starts with an empty copied prefix and reflexive frames.
The mopup setup blocks supply the platform and register pins. -/
theorem ScanAtWith.initial {writes : List Nat} {a b count start c footprint expected}
    (good : GoodState c.σ)
    (minstret : ∃ v, c.σ.regs.get? LeanRV64DExecutable.Register.minstret = some v)
    (tick : c.tick < 2) (code : Code.Caml_oldify_mopupLoaded c.σ.mem)
    (bound : start ≤ count)
    (pc : PCAt (if start < count then FieldCopy.pc else exitPc) c)
    (registers : GHolds c.σ (regs (scanPtr a start) (BitVec.ofNat 64 b - BitVec.ofNat 64 a)
      (BitVec.ofNat 64 b) (BitVec.ofNat 64 start))) :
    ScanAtWith writes a b count start c start c footprint expected :=
  ⟨good, minstret, tick, code, Nat.le_refl _, bound, pc, registers,
    fun _ _ => rfl, fun _ lo hi => False.elim (by omega), rfl, fun _ _ _ => rfl⟩

theorem ScanAt.initial {a b count start c}
    (good : GoodState c.σ)
    (minstret : ∃ v, c.σ.regs.get? LeanRV64DExecutable.Register.minstret = some v)
    (tick : c.tick < 2) (code : Code.Caml_oldify_mopupLoaded c.σ.mem)
    (bound : start ≤ count)
    (pc : PCAt (if start < count then FieldCopy.pc else exitPc) c)
    (registers : GHolds c.σ (regs (scanPtr a start) (BitVec.ofNat 64 b - BitVec.ofNat 64 a)
      (BitVec.ofNat 64 b) (BitVec.ofNat 64 start))) :
    ScanAt a b count start c start c :=
  ScanAtWith.initial good minstret tick code bound pc registers

/-- A completed suffix transports each grey field into its final payload slot.
This is identity-placement transport: fields requiring oldification must use
its stronger, partially relocated counterpart. -/
theorem ScanAtWith.payload {writes : List Nat} {q : PendingCopy} {fields : List Val} {pl cp tag initial c}
    (grey : (pendingPayload q fields).P pl q.target.toNat initial)
    (scan : ScanAtWith writes q.source.toNat q.target.toNat fields.length 1 initial fields.length c) :
    (payload cp (.block tag fields)).P pl q.target.toNat c := by
  intro i v hi
  have before := grey i v hi
  have copied : word c (q.target.toNat + 8 * i) =
      word initial (if i = 0 then q.target.toNat else q.source.toNat + 8 * i) := by
    by_cases zero : i = 0
    · subst i
      simpa using word_frame scan.memory (a := q.target.toNat) (Or.inl (by omega))
    · have bound : i < fields.length := (List.getElem?_eq_some_iff.mp hi).1
      simpa only [ite_eq_right zero] using scan.copied i (by omega) bound
  have image : (Eqv.val v id).Img id pl
      (if i = 0 then q.target.toNat else q.source.toNat + 8 * i)
      (q.target.toNat + 8 * i) initial c := by
    apply relocWord_of_post before
    simp only [placement_identity, id_eq]
    rw [copied]
    exact before
  simpa only [placement_identity, Eqv.val, id_eq] using
    (Eqv.val v id).transport id pl _ _ initial c before image

theorem ScanAt.payload {q : PendingCopy} {fields : List Val} {pl cp tag initial c}
    (grey : (pendingPayload q fields).P pl q.target.toNat initial)
    (scan : ScanAt q.source.toNat q.target.toNat fields.length 1 initial fields.length c) :
    (payload cp (.block tag fields)).P pl q.target.toNat c :=
  ScanAtWith.payload grey scan

/-- The copied payload and untouched destination header form a represented
block. The saved first field is outside the scanned suffix. -/
theorem ScanAtWith.object {writes : List Nat} {q : PendingCopy} {fields : List Val} {pl cp tag initial c}
    (geometry : Geometry q.source.toNat q.target.toNat fields.length)
    (header : HeaderOk (word initial (q.target.toNat - 8)) fields.length tag)
    (grey : (pendingPayload q fields).P pl q.target.toNat initial)
    (scan : ScanAtWith writes q.source.toNat q.target.toNat fields.length 1 initial fields.length c) :
    ObjAt c pl cp q.target.toNat (.block tag fields) := by
  refine ⟨?_, scan.payload (cp := cp) (tag := tag) grey⟩
  have same := word_frame scan.memory (a := q.target.toNat - 8)
    (Or.inl (by have lower := geometry.targetRange.lower; omega))
  simpa only [same, Obj.wosize, Obj.tag] using header

theorem ScanAt.object {q : PendingCopy} {fields : List Val} {pl cp tag initial c}
    (geometry : Geometry q.source.toNat q.target.toNat fields.length)
    (header : HeaderOk (word initial (q.target.toNat - 8)) fields.length tag)
    (grey : (pendingPayload q fields).P pl q.target.toNat initial)
    (scan : ScanAt q.source.toNat q.target.toNat fields.length 1 initial fields.length c) :
    ObjAt c pl cp q.target.toNat (.block tag fields) :=
  ScanAtWith.object geometry header grey scan

/-- Represented integer suffixes supply the machine classifier at every index.
No static assumption that all typed values are integers is made. -/
theorem pending_immediates {q : PendingCopy} {fields : List Val} {pl initial}
    (grey : (pendingPayload q fields).P pl q.target.toNat initial)
    (integers : ∀ i v, fields[i]? = some v → 1 ≤ i → ∃ n, v = .int n) :
    ∀ i, 1 ≤ i → i < fields.length →
      guardB .BNE (word initial (q.source.toNat + 8 * i) &&& 1#64) 0 = true := by
  intro i lower bound
  have hi : fields[i]? = some fields[i] := List.getElem?_eq_getElem bound
  obtain ⟨n, value⟩ := integers i fields[i] hi lower
  have represented := grey i fields[i] hi
  have nonzero : i ≠ 0 := by omega
  have wordEq : tag64 n = word initial (q.source.toNat + 8 * i) := by
    simpa [Eqv.val, value, valWord, nonzero] using represented
  rw [← wordEq]
  exact immediate_tag n

/-- Completed machine scan and its represented destination block. -/
structure GreyScanPost (q : PendingCopy) (fields : List Val) (pl : Place)
    (cp : ChanPlace) (tag : Nat) (initial c : Config) : Prop where
  scan : ScanAt q.source.toNat q.target.toNat fields.length 1 initial fields.length c
  object : ObjAt c pl cp q.target.toNat (.block tag fields)

/-- The concrete integer-suffix loop blackens a grey payload. This leaves
placement unchanged; pointer-field oldification is a separate obligation. -/
theorem scan_grey {q : PendingCopy} {fields : List Val} {pl cp tag initial}
    (geometry : Geometry q.source.toNat q.target.toNat fields.length)
    (header : HeaderOk (word initial (q.target.toNat - 8)) fields.length tag)
    (grey : (pendingPayload q fields).P pl q.target.toNat initial)
    (integers : ∀ i v, fields[i]? = some v → 1 ≤ i → ∃ n, v = .int n) :
    Vsa.Logic.Triple (ScanAt q.source.toNat q.target.toNat fields.length 1 initial 1)
      (GreyScanPost q fields pl cp tag initial) := by
  apply (scan_loop geometry header.2 (pending_immediates grey integers)).conseq
  · exact fun _ h => h
  · intro c h
    exact ⟨h, h.object geometry header grey⟩

end OCaml.Vm.Gc.FieldCopy
