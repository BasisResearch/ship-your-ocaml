import OCaml.Vm.Sim.ForwardCopyLog
import OCaml.Vm.Sim.StackStore

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Any counted forward copy can reuse the original source snapshot while
its destination log remains disjoint from the complete source window. -/
theorem forward_copy_load {source target copied i : Nat} {words : List (BitVec 64)}
    {initial c : Config} {value : BitVec 64}
    (separate : OutLRange (valueLog target words) source (8 * words.length))
    (memory : c.σ.mem = writeLog initial.σ.mem (forwardCopyLog target words copied))
    (snapshot : word initial (source + 8 * i) = value) (bound : i < words.length) :
    LeanRV64DExecutable.Functions.sign_extend (m := 64) (bytesT8 c.σ.mem (source + 8 * i)) = value :=
  (word_read_writeLog_out (forward_copy_source_outside separate bound) memory).trans snapshot

/-- A selected destination store is an entry of the complete copy log. -/
theorem copy_store_entry {target i : Nat} {words : List (BitVec 64)} (bound : i < words.length) :
    (target + 8 * i, 8, words[i]) ∈ valueLog target words :=
  List.mem_iff_getElem.mpr ⟨i, by rw [value_log_length]; exact bound, value_log_getElem target words i bound⟩

/-- Advance an exact prefix log and its executable-image frame by one native
store. Both indexed-field and pointer-cursor copy loops use this rule. -/
theorem forward_copy_memory_step {target i : Nat} {words : List (BitVec 64)} {initial c d : Config}
    (bound : i < words.length) (image : ExecutableImage c)
    (outside : ImageOutside (valueLog target words))
    (memory : c.σ.mem = writeLog initial.σ.mem (forwardCopyLog target words i))
    (store : d.σ.mem = writeLog c.σ.mem [(target + 8 * i, 8, words[i])]) :
    ExecutableImage d ∧ d.σ.mem = writeLog initial.σ.mem (forwardCopyLog target words (i + 1)) := by
  have member : (target + 8 * i, 8, words[i]) ∈ valueLog target words :=
    copy_store_entry bound
  refine ⟨image_of_writeLog image (imageOutside_sublist (List.singleton_sublist.mpr member) outside) store, ?_⟩
  rw [store, memory, forward_copy_log_step target words i bound, writeLog_append]

end OCaml.Vm.Sim
