import OCaml.Vm.Sim.ClosurerecMetadataMemory
import OCaml.Vm.Sim.ClosurerecDone

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Complete recursive-closure layout from the actual nursery write log.
Captured words precede metadata writes; metadata and stack windows preserve them. -/
theorem closurerec_log_layout {before after : Config} {s : St}
    {pl : Place} {cp : ChanPlace} {a sp count dest domain : Nat} {accu : BitVec 64}
    {targets : List Nat}
    (room : 8 ≤ a) (stackRoom : 8 * targets.length ≤ closurerecStackStart sp count)
    (heapBelow : closurerecCaptureBase a (targets.length + 1) + 8 * count ≤
      closurerecStackStart sp count - 8 * targets.length)
    (small : closurerecSize (targets.length + 1) count < 2^32)
    (captures : ValueWords pl (closureCaptures s count) (closureWords before sp count accu))
    (memory : after.σ.mem = writeLog before.σ.mem
      (closurerecFullLog before pl sp count dest a domain accu targets)) :
    ObjAt after pl cp a (closurerecObject s count (dest :: targets)) := by
  have base : closurerecCaptureBase a (targets.length + 1) = a + 24 * targets.length + 16 := by
    unfold closurerecCaptureBase
    omega
  have countLength : (closureCaptures s count).length = count :=
    captures.length.symm.trans (closure_words_length before sp count accu)
  let metadata := closurerecFirstLog pl sp (targets.length + 1) count dest a ++
    (infixGroups pl a (closurerecStackStart sp count) targets).flatten
  have metaOutside (address width : Nat)
      (heapSeparate : address + width ≤ a ∨ a + 24 * targets.length + 16 ≤ address)
      (stackSeparate : address + width ≤ closurerecStackStart sp count - 8 * targets.length) :
      OutLRange metadata address width := by
    apply outLRange_append
    · change OutLRange [_ , _, _] address width
      exact ⟨Or.inl (by dsimp only; omega), by dsimp only; omega, by dsimp only; omega, trivial⟩
    · apply outLRange_of_windows (infix_groups_in pl a _ targets stackRoom)
      exact ⟨by dsimp only; omega, Or.inl stackSeparate, trivial⟩
  have headerOutside := metaOutside (a - 8) 8 (Or.inl (by omega)) (by rw [base] at heapBelow; omega)
  have captureOutside := metaOutside (closurerecCaptureBase a (targets.length + 1)) (8 * count)
    (Or.inr (by omega)) heapBelow
  have captureRead : ∀ i v, (closureCaptures s count)[i]? = some v →
      valWord pl v = some (word after (closurerecCaptureBase a (targets.length + 1) + 8 * i)) := by
    apply value_log_framed captures (front := closurerecSetupLog sp (targets.length + 1) count a domain accu)
      (back := metadata)
    · simpa only [closurerecFullLog, closurerecReadyLog, metadata, List.append_assoc] using memory
    · simpa only [closure_words_length] using captureOutside
  have header : word after (a - 8) = blockHeader (closurerecSize (targets.length + 1) count) closureTag := by
    have normalized : closurerecFullLog before pl sp count dest a domain accu targets =
        (closurePushLog sp count accu ++ grabReserveLog domain a) ++
          (closurerecHeaderLog a (targets.length + 1) count ++
            (valueLog (closurerecCaptureBase a (targets.length + 1)) (closureWords before sp count accu) ++ metadata)) := by
      simp only [closurerecFullLog, closurerecReadyLog, closurerecSetupLog, metadata, List.append_assoc]
    rw [word, memory, normalized, writeLog_append]
    apply word_writeLog_at _ _ 0 _ _ rfl
    change OutLRange (valueLog (closurerecCaptureBase a (targets.length + 1)) (closureWords before sp count accu) ++ metadata) (a - 8) 8
    apply outLRange_append
    · apply outLRange_of_windows (value_log_in _ _)
      exact ⟨Or.inl (by dsimp only; omega), trivial⟩
    · exact headerOutside
  constructor
  · change HeaderOk (word after (a - 8))
      ((closurerecFunctionValues (dest :: targets) ++ closureCaptures s count).length) closureTag
    rw [header, List.length_append, closurerec_function_values_length, countLength]
    exact block_header_ok _ _ small (by decide)
  · apply value_read_append
    · apply closurerec_metadata_memory (front := closurerecReadyLog before sp (targets.length + 1) count a domain accu)
        (by unfold closurerecSize at small; omega) stackRoom (by rw [base] at heapBelow; omega) memory
    · rw [closurerec_function_values_length]
      exact captureRead

end OCaml.Vm.Sim
