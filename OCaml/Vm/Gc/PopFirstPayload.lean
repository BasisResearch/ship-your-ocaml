import OCaml.Vm.Gc.PopFirst
import OCaml.Vm.Gc.RelocatedPayload

namespace OCaml.Vm.Gc.WorkQueue
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc

/-- The composed queue-pop/first-field log preserves every separate word. -/
theorem PopFirstPost.word_frame {R q qs pl before after a}
    (post : PopFirstPost R q qs pl before after)
    (outside : OutLRange ([(Layout.sym_oldify_todo_list,8,head qs)] ++ firstEffect R q before) a 8) :
    word after a = word before a := by
  change bytesT after.σ.mem a 8 = _
  rw [post.memory, bytesT_writeLog_out _ outside]
  rfl

/-- Actual queue pop and first-field execution establish the represented
boundary needed to scan the suffix at the new placement. -/
theorem PopFirstPost.relocating_grey {R q qs pl before after μ fields}
    (post : PopFirstPost R q qs pl before after)
    (grey : (pendingPayload q fields).P pl q.target.toNat before)
    (forwarding : ∀ v, fields[0]? = some v →
      word before (word before q.target.toNat).toNat = relocWord μ pl v (word before q.target.toNat))
    (suffixOutside : ∀ i, 1 ≤ i → i < fields.length →
      OutLRange ([(Layout.sym_oldify_todo_list,8,head qs)] ++ firstEffect R q before)
        (q.source.toNat + 8 * i) 8) :
    FieldCopy.RelocatingGrey q.source.toNat q.target.toNat fields pl μ after := by
  apply FieldCopy.relocating_grey_of_pending grey
  · intro v member
    exact post.first.trans (forwarding v member)
  · intro i lower bound
    exact post.word_frame (suffixOutside i lower bound)

end OCaml.Vm.Gc.WorkQueue
