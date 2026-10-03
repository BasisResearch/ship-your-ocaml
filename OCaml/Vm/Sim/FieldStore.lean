import OCaml.Vm.Sim.HeapEdit
import OCaml.Vm.Sim.LogRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The exact memory effect of replacing one block field. -/
def fieldLog (a i : Nat) (w : BitVec 64) : List WEntry := [(a + 8 * i, 8, w)]

/-- Replacing one field preserves the header and every other represented field.
The generated store supplies the exact log; no execution is assumed here. -/
theorem block_field_written {before after : Config} {pl : Place} {cp : ChanPlace}
    {a i tag : Nat} {fields : List Val} {value : Val} {w : BitVec 64}
    (object : ObjAt before pl cp a (.block tag fields)) (room : 8 ≤ a)
    (bound : i < fields.length) (represented : valWord pl value = some w)
    (memory : after.σ.mem = writeLog before.σ.mem (fieldLog a i w)) :
    ObjAt after pl cp a (.block tag (fields.set i value)) := by
  have headerOutside : OutLRange (fieldLog a i w) (a - 8) 8 := by
    simp only [fieldLog, OutLRange, and_true]
    omega
  have header : word after (a - 8) = word before (a - 8) := by
    rw [word, memory]
    exact bytesT_writeLog_out before.σ.mem headerOutside
  refine ⟨?_, ?_⟩
  · change HeaderOk (word after (a - 8)) (fields.set i value).length tag
    rw [header, List.length_set]
    exact object.1
  · intro j v selected
    by_cases equal : i = j
    · subst j
      have same : value = v := Option.some.inj (by simpa only [List.getElem?_set_self bound] using selected)
      subst v
      have stored : word after (a + 8 * i) = w :=
        word_after_writeLog_at memory 0 _ _ rfl trivial
      rw [stored]
      exact represented
    · have old : fields[j]? = some v := by simpa only [List.getElem?_set_ne equal] using selected
      have outside : OutLRange (fieldLog a i w) (a + 8 * j) 8 := by
        simp only [fieldLog, OutLRange, and_true]
        omega
      have unchanged : word after (a + 8 * j) = word before (a + 8 * j) := by
        rw [word, memory]
        exact bytesT_writeLog_out before.σ.mem outside
      rw [unchanged]
      exact object.2 j v old

/-- Heap separation puts every other object's observations outside the store. -/
theorem field_log_outside {a b count i : Nat} {other : Obj} (w : BitVec 64)
    (room : 8 ≤ a) (bound : i < count)
    (apart : a + 8 * count ≤ b - 8 ∨ b + 8 * other.wosize ≤ a - 8) :
    ObjectOutside (fieldLog a i w) b other := by
  constructor <;> simp only [fieldLog, OutLRange, and_true] <;> omega

/-- A represented block update supplies both the changed object and all its
framed neighbours to the shared heap-graph restoration theorem. -/
theorem heap_field_written {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {l a i tag : Nat} {fields : List Val} {value : Val} {w : BitVec 64}
    (heap : HeapRepr before pl cp P s) (live : Live s.heap (roots P s) l)
    (placed : pl.φ l = some a) (selected : s.heap.get? l = some (.block tag fields))
    (room : 8 ≤ a) (bound : i < fields.length) (represented : valWord pl value = some w)
    (root : ∀ loc, value.loc? = some loc → Live s.heap (roots P s) loc)
    (memory : after.σ.mem = writeLog before.σ.mem (fieldLog a i w)) :
    HeapRepr after pl cp P {s with heap := s.heap.set l (.block tag (fields.set i value))} := by
  apply heap_field_edit heap selected root
  intro q b o oldLive place lookup
  by_cases equal : q = l
  · subst q
    have address : b = a := Option.some.inj (place.symm.trans placed)
    rw [heap_set_here _ selected] at lookup
    cases lookup
    obtain ⟨a', original, place', select', object⟩ := heap.1 l live
    have sameAddress : a' = a := Option.some.inj (place'.symm.trans placed)
    have sameObject : original = .block tag fields := Option.some.inj (select'.symm.trans selected)
    subst a'; subst original
    rw [address]
    exact block_field_written object room bound represented memory
  · rw [heap_set_other s.heap l q _ (Ne.symm equal)] at lookup
    obtain ⟨b', original, place', select', object⟩ := heap.1 q oldLive
    have sameAddress : b' = b := Option.some.inj (place'.symm.trans place)
    have sameObject : original = o := Option.some.inj (select'.symm.trans lookup)
    subst b'; subst original
    have apart := heap.2 l q a b (.block tag fields) o live oldLive (Ne.symm equal) placed place selected lookup
    have outside := field_log_outside w room bound apart
    exact object_copied object (copied_of_writeLog memory outside.header)
      (copied_of_writeLog memory outside.payload)

end OCaml.Vm.Sim
