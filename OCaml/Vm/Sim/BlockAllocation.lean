import OCaml.Vm.Sim.ValueLog
import OCaml.Vm.Sim.LogWindow
import OCaml.Vm.Primitives.Allocation

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A freshly allocated ordinary block has the white header used by the
interpreter's G1 allocation paths. -/
def blockHeader (count tag : Nat) : BitVec 64 :=
  (BitVec.ofNat 64 count <<< (10 : Nat)) + BitVec.ofNat 64 tag

/-- The native size/tag encoding agrees with the represented block header. -/
theorem block_header_ok (count tag : Nat) (small : count < 2^32) (tagBound : tag < 256) :
    HeaderOk (blockHeader count tag) count tag := by
  unfold HeaderOk blockHeader
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  constructor <;> omega

/-- Field-copy readbacks and the header are enough to establish an ordinary
block, independently of store order or machine execution. -/
theorem block_layout_of_words {pl : Place} {cp : ChanPlace} {after : Config}
    {a tag : Nat} {fields : List Val} {words : List (BitVec 64)}
    (represented : ValueWords pl fields words)
    (header : HeaderOk (word after (a - 8)) fields.length tag)
    (read : ∀ i w, words[i]? = some w → word after (a + 8 * i) = w) :
    ObjAt after pl cp a (.block tag fields) :=
  ⟨header, represented.readback read⟩

/-- Canonical initializer effect for a header followed by its field words. -/
def blockLog (a tag : Nat) (words : List (BitVec 64)) : List WEntry :=
  (a - 8, 8, blockHeader words.length tag) :: valueLog a words

/-- The canonical block initializer establishes layout from its exact log. -/
theorem block_log_layout {pl : Place} {cp : ChanPlace} {before after : Config}
    {a tag : Nat} {fields : List Val} {words : List (BitVec 64)}
    (represented : ValueWords pl fields words) (room : 8 ≤ a)
    (small : words.length < 2^32) (tagBound : tag < 256)
    (memory : after.σ.mem = writeLog before.σ.mem (blockLog a tag words)) :
    ObjAt after pl cp a (.block tag fields) := by
  have outside : OutLRange (valueLog a words) (a - 8) 8 := by
    apply outLRange_of_windows (value_log_in a words)
    exact ⟨Or.inl (by dsimp only; omega), trivial⟩
  have header := word_after_writeLog_at memory 0 (a - 8) (blockHeader words.length tag) rfl outside
  let initialized : Config := {before with σ := {before.σ with
    mem := writeLog before.σ.mem [(a - 8, 8, blockHeader words.length tag)]}}
  have fieldsMemory : after.σ.mem = writeLog initialized.σ.mem (valueLog a words) := by
    rw [memory]
    exact writeLog_append before.σ.mem [(a - 8, 8, blockHeader words.length tag)] (valueLog a words)
  refine ⟨?_, value_log_words represented fieldsMemory⟩
  change HeaderOk (word after (a - 8)) fields.length tag
  rw [header, ← represented.length]
  exact block_header_ok _ _ small tagBound

/-- Root reachability for ordinary constructors is shared by GRAB, closure
creation and MAKEBLOCK: every captured field was an old live value. -/
theorem block_allocation_roots {P : Prog} {s : St} {tag : Nat} {fields : List Val}
    (roots : ∀ v ∈ fields, ∀ l, v.loc? = some l → Live s.heap (OCaml.Vm.roots P s) l) :
    AllocationRoots P s (.block tag fields) := by
  intro t fs equal v member l loc
  cases equal
  exact roots v member l loc

end OCaml.Vm.Sim
