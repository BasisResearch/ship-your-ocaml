import OCaml.Vm.Gc.FreshSingleData
import OCaml.Vm.Gc.SingleObject
import OCaml.Vm.Gc.ForwardingDomain

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives Reloc

/-- A terminal field unchanged by the partial relocation remains represented
under the final placement. The source observation precedes forwarding stores. -/
theorem SingleResult.payload_fixed {R target log before after pl cp tag value μ}
    (post : SingleResult R target log before after)
    (object : ObjAt before pl cp (R 10).toNat (.block tag [value]))
    (allocationOutside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R ++ log) (R 10).toNat 8)
    (rootOutside : OutLRange [((R 11).toNat,8,target)] (R 10).toNat 8)
    (fixed : relocWord μ pl value (word before (R 10).toNat) = word before (R 10).toNat) :
    (Eqv.val value id).P (reloc μ pl) target.toNat after := by
  have represented : (Eqv.val value id).P pl (R 10).toNat before := by
    simpa [Eqv.val] using object.2 0 value rfl
  apply (Eqv.val value id).transport μ pl (R 10).toNat target.toNat before after represented
  change word after target.toNat = relocWord μ pl value (word before (R 10).toNat)
  rw [fixed,post.value,single_child_original allocationOutside rootOutside]

/-- Non-pointer terminal values are stable under every relocation. -/
theorem SingleResult.payload_nonpointer {R target log before after pl cp tag value μ}
    (post : SingleResult R target log before after)
    (object : ObjAt before pl cp (R 10).toNat (.block tag [value]))
    (allocationOutside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R ++ log) (R 10).toNat 8)
    (rootOutside : OutLRange [((R 11).toNat,8,target)] (R 10).toNat 8)
    (nonpointer : value.loc? = none) :
    (Eqv.val value id).P (reloc μ pl) target.toNat after :=
  post.payload_fixed object allocationOutside rootOutside (relocWord_fix _ nonpointer)

/-- A represented old-generation base pointer remains valid under any final
forwarding table bounded by the young source set. No forwarding-word premise
is required for this terminal branch. -/
theorem SingleResult.payload_outside {R target log before after pl cp tag l copies sources source}
    (post : SingleResult R target log before after)
    (object : ObjAt before pl cp (R 10).toNat (.block tag [.ptr l 0]))
    (allocationOutside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R ++ log) (R 10).toNat 8)
    (rootOutside : OutLRange [((R 11).toNat,8,target)] (R 10).toNat 8)
    (bounded : ForwardingTable.Bounded copies sources)
    (outside : source ∉ sources) (placed : pl.φ l = some source.toNat) :
    (Eqv.val (.ptr l 0) id).P (reloc (ForwardingTable.relocation copies) pl) target.toNat after := by
  have represented := object.2 0 (.ptr l 0) rfl
  have original : word before (R 10).toNat = source := by
    have encoded : some source = some (word before (R 10).toNat) := by
      simpa [valWord,placed,BitVec.setWidth_eq] using represented
    exact (Option.some.inj encoded).symm
  apply post.payload_fixed object allocationOutside rootOutside
  rw [original]
  exact bounded.pointer_fixed outside placed

/-- Fixed terminal payloads and an allocated header give a complete singleton
object at the relocated placement, for either supported allocator route. -/
theorem SingleResult.object_fixed {R target log before after pl cp tag value μ}
    (post : SingleResult R target log before after)
    (object : ObjAt before pl cp (R 10).toNat (.block tag [value]))
    (allocationOutside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R ++ log) (R 10).toNat 8)
    (rootOutside : OutLRange [((R 11).toNat,8,target)] (R 10).toNat 8)
    (fixed : relocWord μ pl value (word before (R 10).toNat) = word before (R 10).toNat)
    (header : HeaderOk (word after (target.toNat - Layout.header_bytes)) 1 tag) :
    ObjAt after (reloc μ pl) cp target.toNat (.block tag [value]) :=
  single_object_of_payload header (post.payload_fixed object allocationOutside rootOutside fixed)

end OCaml.Vm.Gc.Fresh
