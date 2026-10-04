import OCaml.Vm.Gc.EnqueueAccess

namespace OCaml.Vm.Gc
open OCaml.Bytecode Vsa.Machine Vsa.Sim Reloc Primitives WorkQueue

/-- While a copied object is grey, its saved first field is at the supplied
base and every later field remains in the source object. In particular the
copy's second word is a queue link, not yet an OCaml field. All pending fields
still use the original placement; mopup must oldify them before blackening. -/
def pendingPayload (q : PendingCopy) (fields : List Val) : Eqv :=
  Eqv.list fields fun i v => Eqv.val v
    (fun base => if i = 0 then base else q.source.toNat + 8 * i)

/-- Before enqueue, the original object supplies every pending field. -/
theorem pendingPayload_before {q fields tag pl cp c}
    (object : ObjAt c pl cp q.source.toNat (.block tag fields)) :
    (pendingPayload q fields).P pl q.source.toNat c := by
  intro i v hi
  have field := object.2 i v hi
  by_cases zero : i = 0
  · simpa [Eqv.val, zero] using field
  · simpa [Eqv.val, zero] using field

/-- Shared grey-payload transport: the first field has moved to the copy,
while every remaining field is still observed at its original source. -/
theorem pendingPayload_of_observations {q fields tag pl cp c c'}
    (object : ObjAt c pl cp q.source.toNat (.block tag fields))
    (first : word c' q.target.toNat = word c q.source.toNat)
    (suffix : ∀ i v, fields[i]? = some v → i ≠ 0 →
      word c' (q.source.toNat + 8 * i) = word c (q.source.toNat + 8 * i)) :
    (pendingPayload q fields).P pl q.target.toNat c' := by
  have before := pendingPayload_before object
  have image : (pendingPayload q fields).Img id pl q.source.toNat q.target.toNat c c' := by
    apply Eqv.list_val_img before
    intro i v hi
    rw [placement_identity]
    have field := object.2 i v hi
    by_cases zero : i = 0
    · subst i
      simpa [first] using field
    · simpa only [ite_eq_right zero, suffix i v hi zero] using field
  simpa only [placement_identity] using
    (pendingPayload q fields).transport id pl q.source.toNat q.target.toNat c c' before image

/-- The generated enqueue effect establishes the grey payload layout. The
source suffix must lie outside the six-store footprint; the enclosing heap
geometry supplies that fact. This does not claim its fields are oldified. -/
theorem pendingPayload_enqueue {q qs pl cp root size c c' fields tag}
    (post : EnqueueRunPost q qs pl root size c c')
    (object : ObjAt c pl cp q.source.toNat (.block tag fields))
    (outside : ∀ i v, fields[i]? = some v → i ≠ 0 →
      OutLRange (Enqueue.effect q.source q.target root
        (bytesVal .ld ((enqueueLoads q root c).headD []))
        (bytesVal .ld ((enqueueLoads q root c).tail.headD [])))
        (q.source.toNat + 8 * i) 8) :
    (pendingPayload q fields).P pl q.target.toNat c' := by
  apply pendingPayload_of_observations object post.data.first
  intro i v hi zero
  change bytesT c'.σ.mem _ 8 = bytesT c.σ.mem _ 8
  rw [post.machine.memory, Enqueue.writes, bytesT_writeLog_out _ (outside i v hi zero)]

end OCaml.Vm.Gc
