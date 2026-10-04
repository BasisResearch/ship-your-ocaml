import OCaml.Vm.Gc.ForwardingPrefix

namespace OCaml.Vm.Gc.ForwardingTable
open Vsa.Machine Vsa.Sim Primitives Reloc

/-- Forwarding component of the partial relocation. Entries describe only
published zero headers and targets; pending payloads have separate Eqv views. -/
def eqv (copies : List PendingCopy) : Eqv :=
  Eqv.all fun q => Eqv.guard (q ∈ copies) (forwardingEqv q)

/-- The finite table acts as identity on sources not yet entered. Injectivity
and the status of pending fields belong to the enclosing heap invariant. -/
def relocation (copies : List PendingCopy) (a : Nat) : Nat :=
  ((copies.find? (fun q => q.source.toNat == a)).map (fun q => q.target.toNat)).getD a

def Outside (copies : List PendingCopy) (log : List WEntry) : Prop :=
  ∀ q ∈ copies, OutLRange log (q.source - 8#64).toNat 8 ∧ OutLRange log q.source.toNat 8

/-- Every already published forwarding entry survives a separate write log. -/
theorem frame {copies pl before after log}
    (view : (eqv copies).P pl 0 before)
    (memory : after.σ.mem = writeLog before.σ.mem log) (outside : Outside copies log) :
    (eqv copies).P pl 0 after := by
  have image : (eqv copies).Img id pl 0 0 before after := by
    intro q member
    constructor
    · change word after (q.source - 8#64).toNat = word before (q.source - 8#64).toNat
      simp only [word,memory,bytesT_writeLog_out _ (outside q member).1]
    · change word after q.source.toNat = word before q.source.toNat
      simp only [word,memory,bytesT_writeLog_out _ (outside q member).2]
  simpa only [placement_identity] using (eqv copies).transport id pl 0 0 before after view image

/-- A real forwarding prefix extends the partial table and preserves its
old entries under explicit source-header/pointer separation. -/
theorem publish {copies q root pl before after}
    (view : (eqv copies).P pl 0 before)
    (memory : after.σ.mem = writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root))
    (window : WriteWindow q.source 8) (outside : Outside copies (Enqueue.prefixLog q.source q.target root)) :
    (eqv (q :: copies)).P pl 0 after := by
  have first := forwarding_prefix (pl := pl) memory (by have lower := window.lower; omega)
  have old := frame view memory outside
  intro p member
  rcases List.mem_cons.mp member with equal | member
  · subst p; exact first
  · exact old p member

/-- Publishing a parent followed by a separate child-allocation log grows
the same table. The allocator's footprint must preserve all published entries. -/
theorem publish_then {copies q root pl before after log}
    (view : (eqv copies).P pl 0 before)
    (memory : after.σ.mem = writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root ++ log))
    (window : WriteWindow q.source 8) (outside : Outside copies (Enqueue.prefixLog q.source q.target root))
    (allocationOutside : Outside (q :: copies) log) : (eqv (q :: copies)).P pl 0 after := by
  have published := publish view
    (show (SingleField.forwardedSnapshot q root before).σ.mem =
      writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root) from rfl) window outside
  apply frame published ?_ allocationOutside
  simpa only [writeLog_append,SingleField.forwardedSnapshot] using memory

/-- A nonzero source header excludes that address from the published table. -/
theorem fresh_source {copies pl c source} (view : (eqv copies).P pl 0 c)
    (fresh : word c (source - 8#64).toNat ≠ 0) :
    ∀ q ∈ copies, q.source ≠ source := by
  intro q member equal
  have zero : word c (q.source - 8#64).toNat = 0 := (view q member).1
  exact fresh (equal ▸ zero)

/-- Publishing a source maps that source to its concrete destination. -/
theorem relocation_head (q : PendingCopy) (copies : List PendingCopy) :
    relocation (q :: copies) q.source.toNat = q.target.toNat := by
  simp [relocation]

/-- The sparse extension leaves every other original address unchanged. -/
theorem relocation_cons_of_ne {q copies a} (different : q.source.toNat ≠ a) :
    relocation (q :: copies) a = relocation copies a := by
  simp [relocation,different]

/-- Fresh source classification makes partial relocation growth monotone
on all already-published source addresses. -/
theorem extends_published {copies pl c q} (view : (eqv copies).P pl 0 c)
    (fresh : word c (q.source - 8#64).toNat ≠ 0) :
    ∀ p ∈ copies, relocation (q :: copies) p.source.toNat = relocation copies p.source.toNat := by
  intro p member
  apply relocation_cons_of_ne
  intro same
  exact fresh_source view fresh p member (BitVec.eq_of_toNat_eq same.symm)

/-- Two entries for the same source necessarily have the same actual target.
This follows from the machine word, rather than an extra functional-table premise. -/
theorem functional {copies pl c p q} (view : (eqv copies).P pl 0 c)
    (hp : p ∈ copies) (hq : q ∈ copies) (same : p.source = q.source) : p.target = q.target := by
  have left : word c p.source.toNat = p.target := (view p hp).2
  have right : word c q.source.toNat = q.target := (view q hq).2
  rw [same] at left
  exact left.symm.trans right

/-- The total action agrees with every published entry, even if a caller's
list repeats an entry: the concrete word enforces target agreement. -/
theorem relocation_member {copies pl c q} (view : (eqv copies).P pl 0 c)
    (member : q ∈ copies) : relocation copies q.source.toNat = q.target.toNat := by
  unfold relocation
  cases found : copies.find? (fun p => p.source.toNat == q.source.toNat) with
  | none =>
    have missing := List.find?_eq_none.mp found q member
    simp at missing
  | some p =>
    have sameNat : p.source.toNat = q.source.toNat := by simpa using List.find?_some found
    have same : p.source = q.source := BitVec.eq_of_toNat_eq sameNat
    have target := functional view (List.mem_of_find?_eq_some found) member same
    simp only [Option.map_some,Option.getD_some,target]

/-- The forwarding table supplies the typed action for an ordinary base
pointer. Infix offsets and Forward-tag shortcuts remain separate routes. -/
theorem pointer_action {copies pl c q l} (view : (eqv copies).P pl 0 c)
    (member : q ∈ copies) (placed : pl.φ l = some q.source.toNat) :
    word c q.source.toNat = relocWord (relocation copies) pl (.ptr l 0) q.source := by
  have target : word c q.source.toNat = q.target := (view q member).2
  rw [target]
  simp only [relocWord,placed,relocation_member view member,Nat.mul_zero,Nat.add_zero,
    BitVec.ofNat_toNat,BitVec.setWidth_eq]

end OCaml.Vm.Gc.ForwardingTable
