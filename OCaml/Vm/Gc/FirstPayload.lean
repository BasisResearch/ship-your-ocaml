import OCaml.Vm.Gc.FirstField
import OCaml.Vm.Gc.RelocatedPayload
import OCaml.Vm.Gc.PendingPayload

namespace OCaml.Vm.Gc.FirstField
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc

/-- Words outside the actual native-save/first-slot log are unchanged. -/
theorem Post.word_frame {R before after a} (post : Post R before after)
    (outside : OutLRange (ForwardedCall.effect (FirstCall.linked (args R)) before) a 8) :
    word after a = word before a := by
  change bytesT after.σ.mem a 8 = _
  rw [post.memory, bytesT_writeLog_out _ outside]
  rfl

/-- The actual first-slot store realizes the typed forwarding action. -/
theorem Post.first_relocates {R before after μ pl v} (post : Post R before after)
    (represented : (Eqv.val v id).P pl (R 19).toNat before)
    (loaded : word before (R 19).toNat = R 10)
    (forwarding : word before (R 10).toNat = relocWord μ pl v (R 10)) :
    (Eqv.val v id).P (reloc μ pl) (R 19).toNat after := by
  apply (Eqv.val v id).transport μ pl (R 19).toNat (R 19).toNat before after represented
  change word after (R 19).toNat = relocWord μ pl v (word before (R 19).toNat)
  rw [post.first, loaded, forwarding]

/-- First-field execution supplies the mixed-placement grey boundary used
by the typed suffix theorem. Source-suffix separation preserves those words;
Eqv transports the first slot through the observed forwarding action. -/
theorem Post.relocating_grey {R before after μ pl q fields}
    (post : Post R before after)
    (target : R 19 = q.target)
    (grey : (pendingPayload q fields).P pl q.target.toNat before)
    (loaded : word before q.target.toNat = R 10)
    (forwarding : ∀ v, fields[0]? = some v →
      word before (R 10).toNat = relocWord μ pl v (R 10))
    (suffixOutside : ∀ i, 1 ≤ i → i < fields.length →
      OutLRange (ForwardedCall.effect (FirstCall.linked (args R)) before) (q.source.toNat + 8 * i) 8) :
    FieldCopy.RelocatingGrey q.source.toNat q.target.toNat fields pl μ after := by
  apply FieldCopy.relocating_grey_of_pending grey
  · intro v member
    have stored : word after q.target.toNat = word before (R 10).toNat := by
      simpa only [target] using post.first
    rw [stored, loaded, forwarding v member]
  · intro i lower bound
    exact post.word_frame (suffixOutside i lower bound)

end OCaml.Vm.Gc.FirstField
