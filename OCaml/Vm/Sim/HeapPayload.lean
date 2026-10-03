import OCaml.Vm.Sim.FieldStore
import OCaml.Vm.Sim.PayloadRestore

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Separation of all non-heap observations from a heap-write log. The edited
heap is restored separately from object readbacks and reachability facts. -/
structure HeapWriteOutside (log : List WEntry) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (sp : Nat) : Prop extends PayloadCoreOutside log P s c pl cp where
  trapsp : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) 8
  stack : ∀ i v, s.stack[i]? = some v → OutLRange log (sp + 8 * i) 8

/-- Frame the common payload while a separate heap theorem describes the
objects changed by the log. All copied observations use the existing byte
and relocation combinators. -/
theorem payload_heap_frame {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {log : List WEntry} {heap : Heap}
    (h : VmPayload P s before pl cp sp high)
    (outside : HeapWriteOutside log P s before pl cp sp)
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (out : after.σ.sailOutput = before.σ.sailOutput)
    (objects : HeapRepr after pl cp P {s with heap := heap}) :
    VmPayload P {s with heap := heap} after pl cp sp high := by
  apply payload_rebuild h outside.toPayloadCoreOutside memory out
  · have domain : word after Layout.sym_Caml_state = word before Layout.sym_Caml_state :=
      Reloc.bytesT_congr (copied_of_writeLog memory outside.domain)
    have trap : word after ((word before Layout.sym_Caml_state).toNat + Layout.off_trapsp) =
        word before ((word before Layout.sym_Caml_state).toNat + Layout.off_trapsp) :=
      Reloc.bytesT_congr (copied_of_writeLog memory outside.trapsp)
    rw [domain, trap]
    exact h.trapsp
  · exact stack_frame_log h.stack outside.stack memory
  · exact objects

/-- A field replacement keeps the common memory payload and reconstructs
its changed heap through the shared exact-write theorem. -/
theorem payload_field_written {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a i tag : Nat} {fields : List Val} {value : Val} {w : BitVec 64}
    (h : VmPayload P s before pl cp sp high)
    (live : Live s.heap (roots P s) l) (placed : pl.φ l = some a)
    (selected : s.heap.get? l = some (.block tag fields))
    (room : 8 ≤ a) (bound : i < fields.length) (represented : valWord pl value = some w)
    (root : ∀ loc, value.loc? = some loc → Live s.heap (roots P s) loc)
    (outside : HeapWriteOutside (fieldLog a i w) P s before pl cp sp)
    (memory : after.σ.mem = writeLog before.σ.mem (fieldLog a i w))
    (out : after.σ.sailOutput = before.σ.sailOutput) :
    VmPayload P {s with heap := s.heap.set l (.block tag (fields.set i value))} after pl cp sp high :=
  payload_heap_frame h outside memory out
    (heap_field_written h.heap live placed selected room bound represented root memory)

end OCaml.Vm.Sim
