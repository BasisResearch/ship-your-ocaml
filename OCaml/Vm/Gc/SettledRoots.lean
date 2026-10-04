import OCaml.Vm.Gc.SingleTailState

namespace OCaml.Vm.Gc.SettledRoots
open Vsa.Machine Vsa.Sim Primitives Reloc

/-- A root or ancestor field already rewritten to its child's target. The
copy identifies the entry needed to interpret the word under the final map. -/
structure Cell where
  address : Nat
  copy : PendingCopy

/-- Frozen observations for roots completed by earlier forwarding prefixes. -/
def eqv (cells : List Cell) : Eqv :=
  Eqv.all fun cell => Eqv.guard (cell ∈ cells)
    (Eqv.rawW (fun _ => cell.address) (· = cell.copy.target))

def Outside (cells : List Cell) (log : List WEntry) : Prop :=
  ∀ cell ∈ cells, OutLRange log cell.address 8

/-- Already completed roots survive every subsequent disjoint store log. -/
theorem frame {cells pl before after log}
    (view : (eqv cells).P pl 0 before)
    (memory : after.σ.mem = writeLog before.σ.mem log) (outside : Outside cells log) :
    (eqv cells).P pl 0 after := by
  have image : (eqv cells).Img id pl 0 0 before after := by
    intro cell member
    change word after cell.address = word before cell.address
    simp only [word,memory,bytesT_writeLog_out _ (outside cell member)]
  simpa only [placement_identity] using (eqv cells).transport id pl 0 0 before after view image

/-- Ownership needed to publish the current caller root and retain older
completed fields. These are only finite store footprints, supplied by the
heap/free-list invariant; neither execution nor a post-invariant is assumed. -/
structure Footprint (cells : List Cell) (q : PendingCopy) (root : BitVec 64)
    (log : List WEntry) : Prop where
  prior : Outside cells (Enqueue.prefixLog q.source q.target root ++ log)
  forwarding : OutLRange ((Enqueue.prefixLog q.source q.target root).drop 1) root.toNat 8
  suffix : OutLRange log root.toNat 8

/-- The actual first forwarding store completes the current root, and the
rest of this iteration preserves it together with earlier completed roots. -/
theorem publish {cells q root pl before after log}
    (view : (eqv cells).P pl 0 before)
    (memory : after.σ.mem = writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root ++ log))
    (footprint : Footprint cells q root log) :
    (eqv (⟨root.toNat,q⟩ :: cells)).P pl 0 after := by
  have first : word after root.toNat = q.target := by
    change bytesT after.σ.mem root.toNat 8 = q.target
    rw [memory,writeLog_append,bytesT_writeLog_out _ footprint.suffix]
    exact word_writeLog_at _ _ 0 _ _ rfl footprint.forwarding
  have old := frame view memory footprint.prior
  intro cell member
  rcases List.mem_cons.mp member with equal | member
  · subst cell; exact first
  · exact old cell member

/-- Actual fresh-child back edges publish the caller root before allocation. -/
theorem backedge {cells q root sp payload copies sources log pl before after}
    (post : SingleField.BackEdgeResult q root sp payload copies sources log pl before after)
    (view : (eqv cells).P pl 0 before) (footprint : Footprint cells q root log) :
    (eqv (⟨root.toNat,q⟩ :: cells)).P pl 0 after :=
  publish view post.allocated.memory footprint

/-- All concrete terminal routes share the same root-publication proof. -/
theorem returned {cells q root sp log pl before after}
    (post : SingleTail.Returned q root sp log before after)
    (view : (eqv cells).P pl 0 before) (footprint : Footprint cells q root log) :
    (eqv (⟨root.toNat,q⟩ :: cells)).P pl 0 after :=
  publish view post.memory footprint

/-- The completed cell has its original typed base-pointer meaning under
any later consistent forwarding table containing the child's copy. -/
theorem represented {cells copies cell pl origin after l a}
    (view : (eqv cells).P pl 0 after) (member : cell ∈ cells)
    (table : (ForwardingTable.eqv copies).P pl 0 after) (published : cell.copy ∈ copies)
    (original : (Eqv.val (.ptr l 0) id).P pl a origin)
    (placed : pl.φ l = some cell.copy.source.toNat) :
    (Eqv.val (.ptr l 0) id).P (reloc (ForwardingTable.relocation copies) pl) cell.address after := by
  have encoded : some cell.copy.source = some (word origin a) := by
    simpa [Eqv.val,valWord,placed,BitVec.setWidth_eq] using original
  have source := (Option.some.inj encoded).symm
  apply (Eqv.val (.ptr l 0) id).transport (ForwardingTable.relocation copies) pl a cell.address origin after original
  change word after cell.address = relocWord (ForwardingTable.relocation copies) pl (.ptr l 0) (word origin a)
  rw [source,view cell member]
  exact (table cell.copy published).2.symm.trans (ForwardingTable.pointer_action table published placed)

end OCaml.Vm.Gc.SettledRoots
