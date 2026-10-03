import OCaml.Vm.Sim.IndexedStores
import OCaml.Vm.Sim.ValueWords
import OCaml.Vm.Sim.FrameInsert

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Sequential word stores retain logical indices as a readback certificate. -/
def valueEntries (words : List (BitVec 64)) : List (Nat × BitVec 64) :=
  (List.range words.length).map fun i => (i, (words[i]?).getD 0)

/-- Concrete memory effects for copying a represented list to a contiguous span. -/
def valueLog (base : Nat) (words : List (BitVec 64)) : List WEntry :=
  indexedLog base (valueEntries words)

theorem value_entries_distinct (words : List (BitVec 64)) :
    ((valueEntries words).map Prod.fst).Nodup := by
  simpa [valueEntries, List.map_map, Function.comp_def] using (List.nodup_range (n := words.length))

theorem value_entries_selected {words : List (BitVec 64)} {i : Nat} {value : BitVec 64}
    (selected : words[i]? = some value) : (i, value) ∈ valueEntries words := by
  apply List.mem_map.mpr
  exact ⟨i, List.mem_range.mpr (List.getElem?_eq_some_iff.mp selected).1, by rw [selected]; rfl⟩

/-- A sequential copy touches exactly its destination word window. -/
theorem value_log_in (base : Nat) (words : List (BitVec 64)) :
    LogInW [⟨base, base + 8 * words.length⟩] (valueLog base words) := by
  apply indexed_log_in
  intro entry member
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp member
  exact List.mem_range.mp hi

/-- Copies have exact represented readbacks, independent of the source bytes. -/
theorem value_log_words {pl : Place} {values : List Val} {words : List (BitVec 64)}
    {before after : Config} {base : Nat} (represented : ValueWords pl values words)
    (memory : after.σ.mem = writeLog before.σ.mem (valueLog base words)) :
    ∀ i v, values[i]? = some v → valWord pl v = some (word after (base + 8 * i)) := by
  apply represented.readback
  intro i w selected
  exact indexed_stored (value_entries_distinct words) (value_entries_selected selected) memory

/-- Tail calls and restart copies replace a stack prefix through one word-log
certificate; all geometry and source-root obligations are separate. -/
theorem payload_copy_prefix {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp start high count : Nat} {front : List Val} {words : List (BitVec 64)}
    (h : VmPayload P s before pl cp sp high) (bound : count ≤ s.stack.length)
    (outside : StackEditOutside (valueLog start words) P s before pl cp high)
    (memory : after.σ.mem = writeLog before.σ.mem (valueLog start words))
    (out : after.σ.sailOutput = before.σ.sailOutput)
    (join : start + 8 * front.length = sp + 8 * count)
    (represented : ValueWords pl front words)
    (root : ∀ v ∈ front, ∀ l, v.loc? = some l → Live s.heap (roots P s) l) :
    VmPayload P {s with stack := front ++ s.stack.drop count} after pl cp start high := by
  apply payload_replace_prefix h bound outside _ memory out join (value_log_words represented memory) root
  simpa only [represented.length, join] using value_log_in start words

end OCaml.Vm.Sim
