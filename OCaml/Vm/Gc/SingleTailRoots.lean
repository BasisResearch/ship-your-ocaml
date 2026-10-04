import OCaml.Vm.Gc.SingleTailLoop
import OCaml.Vm.Gc.SettledRoots

namespace OCaml.Vm.Gc.SingleTail
open Vsa.Machine Vsa.Sim Vsa.Logic Primitives

/-- The ownership supplier for roots already published before this loop.
It checks the finite logs at each head; it does not assume a machine run. -/
structure RootFrame (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (cells : List SettledRoots.Cell) : Prop where
  outside : ∀ copies q root c log, Head sp sources pl initial copies q root c → track copies →
    IterationLog q root sp c log → SettledRoots.Outside cells (Enqueue.prefixLog q.source q.target root ++ log)

/-- Actual loop preservation of completed roots and ancestor fields. The
operational proof is shared with run_loop; Eqv transport supplies its frame. -/
theorem run_loop_roots {sp sources pl initial track cells}
    (coverage : Coverage sp sources pl initial) (footprint : RootFrame sp sources pl initial track cells)
    (extend : ∀ copies q root c, Head sp sources pl initial copies q root c → track copies → track (q :: copies)) :
    Triple (ObservedAt sp sources pl initial track (fun c => (SettledRoots.eqv cells).P pl 0 c))
      (ObservedDone sp sources pl initial track (fun c => (SettledRoots.eqv cells).P pl 0 c)) := by
  apply run_loop_observed coverage extend
  intro copies q root before after log head tracked allowed memory view
  exact SettledRoots.frame view memory (footprint.outside copies q root before log head tracked allowed)

/-- The initial root survives every later iteration once the first prefix
has published it. The final table still contains its copy entry. -/
structure RootReturned (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (q : PendingCopy) (root : BitVec 64) (c : Config) : Prop where
  returned : ObservedDone sp sources pl initial (fun copies => q ∈ copies)
    (fun c => (SettledRoots.eqv [⟨root.toNat,q⟩]).P pl 0 c) c

/-- A whole ordinary single-field call preserves its original caller root.
The initial footprints protect the first publication; RootFrame protects that
cell through all later concrete stores. These ownership suppliers remain open. -/
theorem run_from_head_root {sp sources pl initial copies q root}
    (head : Head sp sources pl initial copies q root initial)
    (coverage : Coverage sp sources pl initial)
    (first : ∀ log, IterationLog q root sp initial log → SettledRoots.Footprint [] q root log)
    (later : RootFrame sp sources pl initial (fun copies => q ∈ copies) [⟨root.toNat,q⟩]) :
    FnSummary SingleField.pc (fun c => c = initial) (RootReturned sp sources pl initial q root) := by
  constructor
  intro c pre
  rcases pre with ⟨_,equal⟩
  subst c
  obtain ⟨middle,run,⟨log,allowed,memory⟩,post,_⟩ :=
    head.step_effect (Steps.refl initial) (coverage.choices copies q root initial (Steps.refl initial) head)
  have empty : (SettledRoots.eqv []).P pl 0 initial := by intro cell member; simp at member
  have written := SettledRoots.publish empty memory (first log allowed)
  have member : q ∈ q :: copies := List.mem_cons_self
  rcases post with ⟨next,nextRoot,nextHead,reached⟩ | finished
  · have extend : ∀ copies next root c, Head sp sources pl initial copies next root c → q ∈ copies → q ∈ next :: copies := by
      intro copies next root c head member
      exact List.mem_cons_of_mem next member
    obtain ⟨after,rest,result⟩ := run_loop_roots coverage later extend middle
      ⟨⟨_,next,nextRoot,nextHead,reached,member⟩,written⟩
    exact ⟨after,run.trans rest,⟨result⟩⟩
  · exact ⟨middle,run,⟨⟨⟨_,finished,member⟩,written⟩⟩⟩

/-- The returned caller root has the same logical base-pointer value under
the final placement, derived from the retained table and actual root word. -/
theorem RootReturned.represented {sp sources pl initial q root after origin l a}
    (post : RootReturned sp sources pl initial q root after)
    (original : (Reloc.Eqv.val (.ptr l 0) id).P pl a origin)
    (placed : pl.φ l = some q.source.toNat) :
    ∃ copies, Finished sp sources pl initial copies after ∧
      (Reloc.Eqv.val (.ptr l 0) id).P (Reloc.reloc (ForwardingTable.relocation copies) pl) root.toNat after := by
  obtain ⟨copies,finished,member⟩ := post.returned.operational
  exact ⟨copies,finished,SettledRoots.represented (cell := ⟨root.toNat,q⟩) (copies := copies)
    (pl := pl) (origin := origin) (after := after) (l := l) (a := a) post.returned.observation
    (List.mem_cons_self) finished.table member original placed⟩

end OCaml.Vm.Gc.SingleTail
