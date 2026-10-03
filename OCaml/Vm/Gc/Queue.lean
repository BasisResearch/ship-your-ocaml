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
  have image : (body qs).Img id pl 0 0 c c' := by
    intro i p hp j cell hc
    change bytesT c'.σ.mem cell.1 8 = bytesT c.σ.mem cell.1 8
    rw [memory]
    exact bytesT_writeLog_out _ ⟨separate i p hp j cell hc, True.intro⟩
  simpa only [placement_identity] using (body qs).transport id pl 0 0 c c' h image

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
