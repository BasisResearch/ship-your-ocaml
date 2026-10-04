import OCaml.Vm.Gc.WordFamily
import OCaml.Vm.Gc.SettledRoots
import OCaml.Vm.Gc.SingleObject

namespace OCaml.Vm.Gc.CopiedHeaders
open Vsa.Machine Vsa.Sim Primitives Reloc

/-- Typed metadata of an allocated copy. Forwarding can overwrite the old
header, so the original size/tag are retained as ghost data. -/
structure Entry where
  copy : PendingCopy
  size : Nat
  tag : Nat

def address (entry : Entry) := entry.copy.target.toNat - Layout.header_bytes

def eqv (entries : List Entry) : Eqv :=
  wordFamily entries address (fun entry w => HeaderOk w entry.size entry.tag)

def Outside (entries : List Entry) (log : List WEntry) : Prop :=
  ∀ entry ∈ entries, OutLRange log (address entry) 8

/-- Subsequent disjoint collector stores preserve already allocated headers. -/
theorem frame {entries pl before after log} (view : (eqv entries).P pl 0 before)
    (memory : after.σ.mem = writeLog before.σ.mem log) (outside : Outside entries log) :
    (eqv entries).P pl 0 after :=
  wordFamily_frame view memory outside

/-- Add an actually allocated header after framing the earlier copies. The
concrete tail allocator/header theorems supply the new header observation. -/
theorem insert {entries entry pl before after log} (view : (eqv entries).P pl 0 before)
    (memory : after.σ.mem = writeLog before.σ.mem log) (outside : Outside entries log)
    (header : HeaderOk (word after (address entry)) entry.size entry.tag) :
    (eqv (entry :: entries)).P pl 0 after := by
  have old := frame view memory outside
  intro e member
  rcases List.mem_cons.mp member with same | member
  · subst e; exact header
  · exact old e member

/-- Retained header plus the typed final field is a complete singleton copy. -/
theorem singleton {entries pl after cp parent tag value μ}
    (headers : (eqv entries).P pl 0 after) (member : ⟨parent,1,tag⟩ ∈ entries)
    (field : (Eqv.val value id).P (reloc μ pl) parent.target.toNat after) :
    ObjAt after (reloc μ pl) cp parent.target.toNat (.block tag [value]) :=
  single_object_of_payload (headers ⟨parent,1,tag⟩ member) field

/-- A child publication completes its ancestor's field. The retained header,
actual rewritten cell and final forwarding table together represent the
entire ancestor object under the final placement, even in cyclic graphs. -/
theorem ancestor {entries cells copies pl cp origin after parent child tag l}
    (headers : (eqv entries).P pl 0 after) (headerMember : ⟨parent,1,tag⟩ ∈ entries)
    (roots : (SettledRoots.eqv cells).P pl 0 after)
    (fieldMember : (⟨parent.target.toNat,child⟩ : SettledRoots.Cell) ∈ cells)
    (table : (ForwardingTable.eqv copies).P pl 0 after) (childMember : child ∈ copies)
    (object : ObjAt origin pl cp parent.source.toNat (.block tag [.ptr l 0]))
    (placed : pl.φ l = some child.source.toNat) :
    ObjAt after (reloc (ForwardingTable.relocation copies) pl) cp parent.target.toNat (.block tag [.ptr l 0]) := by
  have original : (Eqv.val (.ptr l 0) id).P pl parent.source.toNat origin := by
    simpa [Eqv.val] using object.2 0 (.ptr l 0) rfl
  apply singleton headers headerMember
  exact SettledRoots.represented (cell := ⟨parent.target.toNat,child⟩)
    (copies := copies) (pl := pl) (origin := origin) (after := after) (l := l) (a := parent.source.toNat)
    roots fieldMember table childMember original placed

end OCaml.Vm.Gc.CopiedHeaders
