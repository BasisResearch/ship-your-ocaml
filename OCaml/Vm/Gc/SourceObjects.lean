import OCaml.Vm.Gc.ForwardingTable

namespace OCaml.Vm.Gc.SourceObjects
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives

/-- Original young-object metadata. Objects remain interpreted under the
original placement until their source header is published as forwarded. -/
structure Entry where
  source : BitVec 64
  object : Obj

/-- Only unforwarded source objects retain their original in-memory shape.
Forwarded sources have deliberately lost their header and first field. -/
structure View (objects : List Entry) (copies : List PendingCopy) (pl : Place) (cp : ChanPlace) (c : Config) : Prop where
  represented : ∀ entry ∈ objects, (∀ q ∈ copies, q.source ≠ entry.source) →
    ObjAt c pl cp entry.source.toNat entry.object

/-- Remaining source objects are separate from the actual store log. New
publications are excluded; their overwritten fields are represented elsewhere. -/
def Outside (objects : List Entry) (copies : List PendingCopy) (log : List WEntry) : Prop :=
  ∀ entry ∈ objects, (∀ q ∈ copies, q.source ≠ entry.source) →
    ObjectOutside log entry.source.toNat entry.object

/-- Growing the table removes newly forwarded objects from this view. Every
remaining object transports through the concrete disjoint log using the
existing object Eqv frame; no whole-collector correctness is assumed. -/
theorem View.frame {objects copies next pl cp before after log}
    (view : View objects copies pl cp before)
    (retained : ∀ q ∈ copies, q ∈ next)
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (outside : Outside objects next log) : View objects next pl cp after := by
  constructor
  intro entry member unforwarded
  have old := view.represented entry member (fun q hq => unforwarded q (retained q hq))
  have windows := outside entry member unforwarded
  exact object_copied old (copied_of_writeLog memory windows.header) (copied_of_writeLog memory windows.payload)

/-- The actual nonzero header at a copying head excludes every table entry,
so that source still has its original typed object and fields. -/
theorem View.fresh_object {objects copies pl cp c entry}
    (view : View objects copies pl cp c)
    (table : (ForwardingTable.eqv copies).P pl 0 c)
    (member : entry ∈ objects) (fresh : word c (entry.source - 8#64).toNat ≠ 0) :
    ObjAt c pl cp entry.source.toNat entry.object :=
  view.represented entry member (fun q hq => ForwardingTable.fresh_source table fresh q hq)

/-- Initialize the view from a represented nonempty nursery as well as an
empty one. No empty-nursery hypothesis enters this invariant. -/
theorem initial {objects pl cp c} (represented : ∀ entry ∈ objects, ObjAt c pl cp entry.source.toNat entry.object) :
    View objects [] pl cp c :=
  ⟨fun entry member _ => represented entry member⟩

end OCaml.Vm.Gc.SourceObjects
