import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Logic.Symbolic
import OCaml.Vm.Primitives.ImmediateContract

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- A represented live object is an existing abstract heap entry. -/
theorem VmPayload.live_bound {P s c pl cp sp high l}
    (h : VmPayload P s c pl cp sp high) (hl : Live s.heap (roots P s) l) :
    l < s.heap.objs.length := by
  obtain ⟨a, o, hp, hg, layout⟩ := h.heap.1 l hl
  exact (List.getElem?_eq_some_iff.mp hg).1

/-- Any pointers in the freshly allocated object refer to old live objects.
The concrete allocator and initialization code will establish its layout. -/
def AllocationRoots (P : Prog) (s : St) (o : Obj) : Prop :=
  ∀ t fs, o = .block t fs → ∀ v ∈ fs, ∀ l, v.loc? = some l → Live s.heap (roots P s) l

/-- After allocation every reachable object is either the fresh object or an
old reachable object. This is heap-graph reasoning, independent of execution. -/
theorem live_after_alloc {P s c pl cp sp high o l}
    (h : VmPayload P s c pl cp sp high) (fields : AllocationRoots P s o)
    (live : Live (s.heap.alloc o).1
      (roots P {s with heap := (s.heap.alloc o).1, accu := .ptr (s.heap.alloc o).2 0}) l) :
    l = (s.heap.alloc o).2 ∨ Live s.heap (roots P s) l := by
  -- discipline: allow(O5-run-induction) induction on heap-graph reachability, not a machine or bytecode run
  induction live with
  | root hv hl =>
    change _ ∈ Val.ptr (s.heap.alloc o).2 0 :: _ at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Or.inl (Option.some.inj hl).symm
    · exact Or.inr (Live.root (List.mem_cons_of_mem _ hv) hl)
  | @field parent child t fs v hp hg hv hl ih =>
    rcases ih with fresh | old
    · rw [fresh, Heap.get_alloc_fresh] at hg
      exact Or.inr (fields t fs (Option.some.inj hg) v hv child hl)
    · rw [Heap.get_alloc_old _ _ _ (h.live_bound old)] at hg
      exact Or.inr (Live.field old hg hv hl)

/-- Separation of a reserved result allocation from all old reachable objects.
The caller supplies this from nursery/major-allocation freshness. -/
def AllocationOutside (P : Prog) (s : St) (pl : Place) (a : Nat) (o : Obj) : Prop :=
  ∀ l b old, Live s.heap (roots P s) l → pl.φ l = some b → s.heap.get? l = some old →
    a + 8 * o.wosize ≤ b - 8 ∨ b + 8 * old.wosize ≤ a - 8

/-- Extend a represented heap with an initialized fresh object. A placement
may reserve the fresh location before the call: unreachable keys are unconstrained. -/
theorem VmPayload.allocate {P s c pl cp sp high o a}
    (h : VmPayload P s c pl cp sp high) (fields : AllocationRoots P s o)
    (placed : pl.φ (s.heap.alloc o).2 = some a) (layout : ObjAt c pl cp a o)
    (outside : AllocationOutside P s pl a o) :
    VmPayload P {s with heap := (s.heap.alloc o).1, accu := .ptr (s.heap.alloc o).2 0}
      c pl cp sp high := by
  refine { h with heap := ?_ }
  constructor
  · intro l hl
    rcases live_after_alloc h fields hl with fresh | old
    · subst l
      exact ⟨a, o, placed, Heap.get_alloc_fresh _ _, layout⟩
    · obtain ⟨b, oldObj, hp, hg, ho⟩ := h.heap.1 l old
      exact ⟨b, oldObj, hp, (Heap.get_alloc_old _ _ _ (h.live_bound old)).trans hg, ho⟩
  · intro l l' b b' ob ob' hl hl' ne hp hp' hg hg'
    rcases live_after_alloc h fields hl with fresh | old <;>
      rcases live_after_alloc h fields hl' with fresh' | old'
    · exact False.elim (ne (fresh.trans fresh'.symm))
    · subst l
      have addr : b = a := Option.some.inj (hp.symm.trans placed)
      have obj : ob = o := Option.some.inj (hg.symm.trans (Heap.get_alloc_fresh _ _))
      rw [Heap.get_alloc_old _ _ _ (h.live_bound old')] at hg'
      simpa only [addr, obj] using outside l' b' ob' old' hp' hg'
    · subst l'
      have addr : b' = a := Option.some.inj (hp'.symm.trans placed)
      have obj : ob' = o := Option.some.inj (hg'.symm.trans (Heap.get_alloc_fresh _ _))
      rw [Heap.get_alloc_old _ _ _ (h.live_bound old)] at hg
      simpa only [addr, obj] using (outside l b ob old hp hg).symm
    · rw [Heap.get_alloc_old _ _ _ (h.live_bound old)] at hg
      rw [Heap.get_alloc_old _ _ _ (h.live_bound old')] at hg'
      exact h.heap.2 l l' b b' ob ob' old old' ne hp hp' hg hg'

/-- An allocating call consumes a fresh placement reservation and preserves
all old observations outside its concrete write log. -/
structure AllocationInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra : BitVec 64)
    (args : List Val) (o : Obj) (a : Nat) (log : List WEntry) (c : Config) : Prop
    extends ImmediateInput runtimeOk P s pl cp sp high ra args c where
  fields : AllocationRoots P s o
  placed : pl.φ (s.heap.alloc o).2 = some a
  separate : AllocationOutside P s pl a o
  payloadOutside : PayloadOutside log P s c pl cp sp
  bindingsOutside : BindingsOutside log P c

/-- The runtime invariant's supplier checks the exact allocation memory effect,
including the decreased young_ptr and untouched free-list metadata. No run is
assumed; this is the memory-only frame law for the chosen runtime predicate. -/
def AllocationRuntime (runtimeOk : Config → Prop) (before : Config) (log : List WEntry) : Prop :=
  ∀ after : Config, after.σ.mem = writeLog before.σ.mem log → runtimeOk before → runtimeOk after

/-- One allocation bridge for all generated constructors. Layout and platform
suppliers concern only the first-order memory effect; the function summary
must prove the actual machine execution separately. -/
theorem allocation_contract {runtimeOk P s pl cp sp high ra entry args name o a log c writes}
    (h : AllocationInput runtimeOk P s pl cp sp high ra args o a log c)
    (S : FnSummary entry (fun d => d = c)
      (WritePost writes log c ra (BitVec.ofNat 64 a)))
    (layout : ∀ after : Config, after.σ.mem = writeLog c.σ.mem log → ObjAt after pl cp a o)
    (runtime : AllocationRuntime runtimeOk c log)
    (frame : PreservesLoopRegisters writes)
    (model : primF1Impl name args s.heap s.world =
      .ok (.ptr (s.heap.alloc o).2 0) (s.heap.alloc o).1 s.world) :
    FnSummary entry (fun d => d = c)
      (PrimitivePost runtimeOk P s pl cp sp high name args (.ptr (s.heap.alloc o).2 0)
        (BitVec.ofNat 64 a) (s.heap.alloc o).1 s.world writes (writeLog c.σ.mem log) c ra) := by
  apply S.weaken (fun _ h => h)
  intro after post
  refine ⟨post, ?_, bindings_frame_log h.primitives h.bindingsOutside post.memory,
    ⟨post.good, post.image, runtime after post.memory h.runtime⟩, post.loop frame h.loop, ?_, model⟩
  · exact (h.data.frame_log h.payloadOutside post.memory post.output).allocate
      h.fields h.placed (layout after post.memory) h.separate
  · simp [valWord, h.placed]

end OCaml.Vm.Primitives
