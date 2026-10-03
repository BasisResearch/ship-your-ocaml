import OCaml.Vm.Gc.Generated.MopupPop
import OCaml.Vm.Primitives.Write
import OCaml.Vm.Primitives.MemoryFrame

/-! The intrusive oldify queue stores source addresses in copied payloads.
These links are raw words, not values to which the placement action applies.
This view describes the queue's links only; copied object contents and allocator
ownership belong to the partial-relocation invariant. -/
namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Reloc Primitives

structure PendingCopy where
  source : BitVec 64
  target : BitVec 64

namespace PendingCopy

/-- The source is forwarded; the copied block's second field links to the
next SOURCE. Its first field still holds the first value awaiting scanning. -/
def cells (p : PendingCopy) (next : BitVec 64) : List (Nat × BitVec 64) :=
  [((p.source - 8#64).toNat, 0), (p.source.toNat, p.target),
   ((p.target + 8#64).toNat, next)]

def eqv (p : PendingCopy) (next : BitVec 64) : Eqv :=
  Eqv.list (p.cells next) fun _ cell => Eqv.rawW (fun _ => cell.1) (· = cell.2)

/-- Named projections for the raw-link assertion. -/
structure Links (p : PendingCopy) (next : BitVec 64) (c : Config) : Prop where
  forwardedHeader : word c (p.source - 8#64).toNat = 0
  target : word c p.source.toNat = p.target
  nextSource : word c (p.target + 8#64).toNat = next

theorem links {p next pl c} (h : (p.eqv next).P pl 0 c) : Links p next c :=
  ⟨h 0 ((p.source - 8#64).toNat, 0) rfl, h 1 (p.source.toNat, p.target) rfl,
   h 2 ((p.target + 8#64).toNat, next) rfl⟩

/-- Build the raw-word assertion from its named link fields. -/
theorem of_links {p next pl c} (h : Links p next c) : (p.eqv next).P pl 0 c := by
  intro i cell hc
  have member := List.mem_of_getElem? hc
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact h.forwardedHeader
  · exact h.target
  · exact h.nextSource

end PendingCopy

namespace WorkQueue

def head (qs : List PendingCopy) : BitVec 64 := (qs.head?.map PendingCopy.source).getD 0

def next (qs : List PendingCopy) (i : Nat) : BitVec 64 :=
  ((qs[i + 1]?).map PendingCopy.source).getD 0

def body (qs : List PendingCopy) : Eqv :=
  Eqv.list qs fun i p => p.eqv (next qs i)

/-- Exact finite work-list view. Disjointness from writes and allocation
geometry are separate obligations, rather than hidden ownership assumptions. -/
structure View (qs : List PendingCopy) (pl : Place) (c : Config) : Prop where
  root : word c Layout.sym_oldify_todo_list = head qs
  links : (body qs).P pl 0 c

/-- Readback facts for the queue's current head, before it is removed. -/
theorem View.first {q qs pl c} (h : View (q :: qs) pl c) :
    PendingCopy.Links q (head qs) c := by
  have node := PendingCopy.links (h.links 0 q rfl)
  simpa [next, head, List.head?_eq_getElem?] using node

/-- The machine reads the global head, forwarding target, next-source link,
and first field, all before its sole store. Total reads need no density premise. -/
def loads (q : PendingCopy) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem Layout.sym_oldify_todo_list, read8 c.σ.mem q.source.toNat,
   read8 c.σ.mem (q.target + 8#64).toNat, read8 c.σ.mem q.target.toNat]

theorem View.loadedNext {q qs pl c} (h : View (q :: qs) pl c) :
    bytesVal .ld ((loads q c).tail.tail.headD []) = head qs := by
  change bytesVal .ld (read8 c.σ.mem (q.target + 8#64).toNat) = _
  rw [read8_value]
  exact h.first.nextSource

/-- Dropping the head retains the same link expectations in every tail node. -/
theorem body_tail {q qs pl c} (h : (body (q :: qs)).P pl 0 c) :
    (body qs).P pl 0 c := by
  intro i p hp
  have entry := h (i + 1) p (by simpa using hp)
  simpa only [next, List.getElem?_cons_succ] using entry

/-- Adding a node uses its link to the old head and preserves the tail indices. -/
theorem body_cons {q qs pl c} (front : (q.eqv (head qs)).P pl 0 c)
    (tail : (body qs).P pl 0 c) : (body (q :: qs)).P pl 0 c := by
  intro i p hp
  cases i with
  | zero =>
      have same : q = p := Option.some.inj hp
      subst p
      simpa [next, head, List.head?_eq_getElem?] using front
  | succ i =>
      have node := tail i p hp
      simpa only [next, List.getElem?_cons_succ] using node

/-- A write log leaves every intrusive-link observation window disjoint.
Allocation and stack/heap separation supply these finite footprint facts. -/
structure LinksOutside (qs : List PendingCopy) (log : List WEntry) : Prop where
  cells : ∀ (i : Nat) (p : PendingCopy), qs[i]? = some p →
    ∀ (j : Nat) (cell : Nat × BitVec 64), (p.cells (next qs i))[j]? = some cell →
      OutLRange log cell.1 8

/-- Transport queue links from preserved scalar observations, independently
of whether the memory effect is one store or a whole scan. -/
theorem body_frame_words {qs pl c c'}
    (h : (body qs).P pl 0 c)
    (same : ∀ (i : Nat) (p : PendingCopy), qs[i]? = some p →
      ∀ (j : Nat) (cell : Nat × BitVec 64), (p.cells (next qs i))[j]? = some cell →
        word c' cell.1 = word c cell.1) : (body qs).P pl 0 c' := by
  have image : (body qs).Img id pl 0 0 c c' := same
  simpa only [placement_identity] using (body qs).transport id pl 0 0 c c' h image

/-- A read-only native epilogue preserves the queue's memory observations. -/
theorem View.memory_eq {qs pl before after} (queue : View qs pl before)
    (memory : after.σ.mem = before.σ.mem) : View qs pl after := by
  refine ⟨?_, body_frame_words queue.links ?_⟩
  · simpa only [word, memory] using queue.root
  · intro i p hp j cell hc
    simp only [word, memory]

/-- Any disjoint write log transports the queue links by the identity action. -/
theorem body_frame_log {qs pl c c' log}
    (h : (body qs).P pl 0 c) (outside : LinksOutside qs log)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : (body qs).P pl 0 c' := by
  apply body_frame_words h
  intro i p hp j cell hc
  change bytesT c'.σ.mem cell.1 8 = bytesT c.σ.mem cell.1 8
  rw [memory]
  exact bytesT_writeLog_out _ (outside.cells i p hp j cell hc)

/-- A disjoint exact log preserves both the queue head and its Eqv links. -/
theorem View.frame_log {qs pl before after log} (queue : View qs pl before)
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (links : LinksOutside qs log) (root : OutLRange log Layout.sym_oldify_todo_list 8) :
    View qs pl after := by
  refine ⟨?_, body_frame_log queue.links links memory⟩
  change bytesT after.σ.mem _ 8 = _
  rw [memory, bytesT_writeLog_out _ root]
  exact queue.root

/-- Queue-link cells must not overlap the global head word. The machine
layout and allocator separation will supply this footprint fact. -/
def Separate (qs : List PendingCopy) : Prop :=
  ∀ (i : Nat) (p : PendingCopy), qs[i]? = some p → ∀ (j : Nat) (cell : Nat × BitVec 64), (p.cells (next qs i))[j]? = some cell →
    cell.1 + 8 ≤ Layout.sym_oldify_todo_list ∨
      Layout.sym_oldify_todo_list + 8 ≤ cell.1

/-- Changing only the head word preserves all disjoint intrusive links.
The proof uses the relocation combinators with the identity placement action. -/
theorem body_frame {qs pl c c' value}
    (h : (body qs).P pl 0 c) (separate : Separate qs)
    (memory : c'.σ.mem = writeLog c.σ.mem [(Layout.sym_oldify_todo_list, 8, value)]) :
    (body qs).P pl 0 c' := by
  apply body_frame_log h ?_ memory
  exact ⟨fun i p hp j cell hc => ⟨separate i p hp j cell hc, True.intro⟩⟩

/-- The real generated queue-pop store removes the ghost head. The load
witness identifies the next-source word; it will be supplied by concrete
load windows and this queue's link equations. No child call is assumed. -/
theorem pop {q qs pl c c' immediate lds}
    (before : View (q :: qs) pl c)
    (post : MopupPop.Post immediate lds c.σ.mem c')
    (loadedNext : bytesVal .ld (lds.tail.tail.headD []) = head qs)
    (separate : Separate qs) : View qs pl c' := by
  have memory : c'.σ.mem = writeLog c.σ.mem
      [(Layout.sym_oldify_todo_list, 8, head qs)] := by
    rw [post.memory]
    change writeLog c.σ.mem (MopupPop.outcome immediate lds).log = _
    rw [MopupPop.queue_write, loadedNext]
  refine ⟨?_, body_frame (body_tail before.links) separate memory⟩
  change bytesT c'.σ.mem Layout.sym_oldify_todo_list 8 = _
  rw [memory, word_writeLog]

/-- Concrete byte observations discharge the pop theorem's next-link premise. -/
theorem pop_loaded {q qs pl c c' immediate}
    (before : View (q :: qs) pl c)
    (post : MopupPop.Post immediate (loads q c) c.σ.mem c')
    (separate : Separate qs) : View qs pl c' :=
  pop before post before.loadedNext separate

end WorkQueue
end OCaml.Vm.Gc
