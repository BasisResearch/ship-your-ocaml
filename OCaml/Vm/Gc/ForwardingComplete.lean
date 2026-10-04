import OCaml.Vm.Gc.ForwardingTable

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives

/-- Every other original source header survives the forwarding prefix and
a separate allocation/final-store suffix. Shared by exits and back edges. -/
theorem other_headers_preserved {q : PendingCopy} {root log} {sources : List (BitVec 64)} {before after : Config}
    (memory : after.σ.mem = writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root ++ log))
    (outside : ∀ source ∈ sources, source ≠ q.source →
      OutLRange (Enqueue.prefixLog q.source q.target root) (source - 8#64).toNat 8)
    (suffixOutside : ∀ source ∈ sources, OutLRange log (source - 8#64).toNat 8) :
    ∀ source ∈ sources, source ≠ q.source →
      word after (source - 8#64).toNat = word before (source - 8#64).toNat := by
  intro source member different
  simp only [word,memory,writeLog_append,bytesT_writeLog_out _ (suffixOutside source member),
    bytesT_writeLog_out _ (outside source member different)]

namespace ForwardingTable

/-- Coverage component of partial relocation: every forwarded source in the
finite original source set has a published table entry. Together with eqv,
this prevents the loop invariant from forgetting any forwarded source. -/
def Complete (sources : List (BitVec 64)) (copies : List PendingCopy) (c : Config) : Prop :=
  ∀ source ∈ sources, word c (source - 8#64).toNat = 0 → ∃ q ∈ copies, q.source = source

/-- Adding the newly forwarded parent preserves full source coverage when
all other source headers are unchanged by the concrete step. -/
theorem Complete.extend {sources copies q before after}
    (complete : Complete sources copies before)
    (preserved : ∀ source ∈ sources, source ≠ q.source →
      word after (source - 8#64).toNat = word before (source - 8#64).toNat) :
    Complete sources (q :: copies) after := by
  intro source member zero
  by_cases same : source = q.source
  · exact ⟨q,List.mem_cons_self ..,same.symm⟩
  · have oldZero : word before (source - 8#64).toNat = 0 := (preserved source member same).symm.trans zero
    obtain ⟨p,hp,equal⟩ := complete source member oldZero
    exact ⟨p,List.mem_cons_of_mem _ hp,equal⟩

/-- Before any copying, positive original headers give the empty complete
table, even when the nursery contains allocated objects. -/
theorem complete_empty {sources c} (fresh : ∀ source ∈ sources, word c (source - 8#64).toNat ≠ 0) :
    Complete sources [] c := by
  intro source member zero
  exact False.elim (fresh source member zero)

/-- Full table coverage resolves any zero-header source in the finite heap
set through the table's action, without a separately supplied entry witness. -/
theorem Complete.pointer_action {sources copies pl c source l}
    (complete : Complete sources copies c) (view : (eqv copies).P pl 0 c)
    (member : source ∈ sources) (forwarded : word c (source - 8#64).toNat = 0)
    (placed : pl.φ l = some source.toNat) :
    word c source.toNat = Reloc.relocWord (relocation copies) pl (.ptr l 0) source := by
  obtain ⟨q,published,equal⟩ := complete source member forwarded
  have address : pl.φ l = some q.source.toNat := by simpa only [equal] using placed
  simpa only [equal] using ForwardingTable.pointer_action view published address

end ForwardingTable
end OCaml.Vm.Gc
