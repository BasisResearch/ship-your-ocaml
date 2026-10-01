import OCaml.Vm.Sim.Immediate
import OCaml.Vm.Primitives.Read
import OCaml.Vm.Primitives.MemoryFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine
open OCaml.Vm.Primitives

/-- A selected field and the placement of its source pointer. These are
abstract selection witnesses, not machine execution or return assumptions. -/
structure FieldSelection (heap : Heap) (pl : Place) (source : Val) (i : Nat)
    (v : Val) (l a k : Nat) : Prop where
  pointer : source = .ptr l k
  placed : pl.φ l = some a
  selected : field? heap source i = some v

/-- Every successful field selection from an existing VM root has such a
placement witness, by the represented live heap. -/
theorem field_selection {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high i : Nat} {source v : Val} (h : VmReprAt P s c pl cp sp high)
    (member : source ∈ roots P s) (selected : field? s.heap source i = some v) :
    ∃ l a k, FieldSelection s.heap pl source i v l a k := by
  cases source with
  | ptr l k =>
    obtain ⟨a, o, placed, _, _⟩ := h.heap.1 l (Live.root member rfl)
    exact ⟨l, a, k, rfl, placed, selected⟩
  | int n => simp [field?] at selected
  | atom t => simp [field?] at selected
  | code pc => simp [field?] at selected
  | raw w => simp [field?] at selected

/-- Memory and reachability observations for a selected heap field. -/
structure FieldValue (P : Prog) (s : St) (pl : Place) (c : Config) (v : Val) (a : Nat) : Prop where
  word : valWord pl v = some (OCaml.Vm.word c a)
  root : ∀ l, v.loc? = some l → Live s.heap (roots P s) l

theorem FieldSelection.sourceWord {heap : Heap} {pl : Place} {source v : Val}
    {i l a k : Nat} (h : FieldSelection heap pl source i v l a k) :
    valWord pl source = some (BitVec.ofNat 64 (a + 8 * k)) := by
  simp only [h.pointer, valWord, h.placed, Option.map_some]

/-- Resolve both the field word and its existing-root proof through the
primitive lane's object lookup and the shared Live graph. -/
theorem FieldSelection.read_payload {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high i l a k : Nat} {source v : Val} (h : VmPayload P s c pl cp sp high)
    (member : source ∈ roots P s) (f : FieldSelection s.heap pl source i v l a k) :
    FieldValue P s pl c v (a + 8 * (k + i)) := by
  have live : Live s.heap (roots P s) l := Live.root member (by simp [f.pointer, Val.loc?])
  have selected := f.selected
  rw [f.pointer] at selected
  cases object : s.heap.get? l with
  | none => simp [field?, object] at selected
  | some obj =>
    cases obj <;> simp only [field?, object] at selected
    case block tag fs =>
      have placed := h.object_at live f.placed object
      exact ⟨placed.2 (k + i) v selected,
        fun l' hl => Live.field live object (List.mem_of_getElem? selected) hl⟩
    all_goals cases selected

/-- Loop-head specialization of the common payload field observation. -/
theorem FieldSelection.read {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high i l a k : Nat} {source v : Val} (h : VmReprAt P s c pl cp sp high)
    (member : source ∈ roots P s) (f : FieldSelection s.heap pl source i v l a k) :
    FieldValue P s pl c v (a + 8 * (k + i)) :=
  f.read_payload (payload_of_repr h) member

/-- The payload's write-log frame preserves the selected field's unique word. -/
theorem FieldSelection.word_frame {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high i l a k : Nat} {source v : Val} {log : List Vsa.Sim.WEntry}
    (h : VmPayload P s c pl cp sp high) (member : source ∈ roots P s)
    (f : FieldSelection s.heap pl source i v l a k)
    (outside : PayloadOutside log P s c pl cp sp)
    (memory : after.σ.mem = Vsa.Sim.writeLog c.σ.mem log)
    (output : after.σ.sailOutput = c.σ.sailOutput) :
    word after (a + 8 * (k + i)) = word c (a + 8 * (k + i)) := by
  have beforeValue := f.read_payload h member
  have afterValue := f.read_payload (h.frame_log outside memory output) member
  exact Option.some.inj (afterValue.word.symm.trans beforeValue.word)

end OCaml.Vm.Sim
