import OCaml.Bytecode.GcSafe

/-! `GcSafe` for programs that never create a `Forward_tag` block (F1).

Every directed collection edit (`FwdEdit`) needs a `Forward_tag` block in the
heap. If no reachable state has one, the collector's shortcut is the identity,
collection-closed reachability (`GcReach`) is ordinary reachability, and the
observation obligation is reflexive. -/
namespace OCaml.Bytecode

/-- The heap holds no `Forward_tag` block (a `Bool`, for kernel checks). -/
def Heap.noForward (h : Heap) : Bool := h.objs.all fun o => o.tag != forwardTag

/-- No reachable state of `P` holds a `Forward_tag` block: the program never
forces a lazy value (CamlinternalLazy's `caml_obj_set_tag`/`make_forward`). -/
def NoForward (P : Prog) : Prop := ∀ s, Reach P s → s.heap.noForward = true

/-- A forwarding edit exhibits a `Forward_tag` block in its source heap. -/
theorem FwdEdit.forward {s t : St} (edit : FwdEdit s t) : s.heap.noForward = false := by
  cases edit with
  | replace _ _ v block _ _ =>
    have member : Obj.block 250 [v] ∈ s.heap.objs := List.mem_of_getElem? block
    rw [Heap.noForward, Bool.eq_false_iff]
    intro all
    have := List.all_eq_true.1 all _ member
    simp [Obj.tag, forwardTag] at this

/-- Without `Forward_tag` blocks, a directed collection reduction is the identity. -/
theorem FwdReduction.eq_of_noForward {s t : St} (edits : FwdReduction s t)
    (none : s.heap.noForward = true) : t = s := by
  induction edits with
  | refl => rfl
  | tail _ edit ih =>
    have same := ih
    subst same
    rw [edit.forward] at none
    cases none

/-- Under `NoForward`, collection-closed reachability is ordinary reachability. -/
theorem GcReach.reach_of_noForward {P : Prog} (safe : NoForward P) {s : St} (reach : GcReach P s) :
    Reach P s := by
  -- discipline: allow(O5-run-induction) presentation transport GcReach → Reach; each collect edge is the identity
  induction reach with
  | init => exact ⟨0, .zero _⟩
  | next _ step ih =>
    obtain ⟨n, run⟩ := ih
    exact ⟨n + 1, run.snoc step⟩
  | collect _ _ edits ih =>
    rw [edits.eq_of_noForward (safe _ ih)]
    exact ih

/-- **F1 GC-safety**: a program that never creates a `Forward_tag` block is GC-safe. -/
theorem gcSafe_of_noForward {P : Prog} (safe : NoForward P) : GcSafe P := by
  intro s t reach _ edits
  rw [edits.eq_of_noForward (safe s (reach.reach_of_noForward safe))]
  exact ⟨fun _ _ => Iff.rfl, Iff.rfl⟩

end OCaml.Bytecode
