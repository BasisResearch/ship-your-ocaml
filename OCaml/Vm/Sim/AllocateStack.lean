import OCaml.Vm.Primitives.Allocation
import OCaml.Vm.Sim.PayloadRestore
import OCaml.Vm.Sim.StackPayload

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Allocation may overwrite consumed stack slots. Preserve the old heap,
extend it with the initialized object, then rebuild only the resulting stack.
The stack roots may include any interior pointer into the fresh object. -/
theorem payload_allocate_stack {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp newSp high a : Nat} {o : Obj}
    {log : List WEntry} {stack : List Val}
    (h : VmPayload P s before pl cp sp high)
    (outside : PayloadCoreOutside log P s before pl cp)
    (heapOutside : ∀ l b old, Live s.heap (roots P s) l →
      pl.φ l = some b → s.heap.get? l = some old → ObjectOutside log b old)
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (out : after.σ.sailOutput = before.σ.sailOutput)
    (trapWord : (word after ((word after Layout.sym_Caml_state).toNat + Layout.off_trapsp)).toNat =
      high - 8 * s.trap)
    (fields : AllocationRoots P s o)
    (placed : pl.φ (s.heap.alloc o).2 = some a)
    (layout : ObjAt after pl cp a o)
    (separate : AllocationOutside P s pl a o)
    (words : StackRepr after pl newSp high stack)
    (root : ∀ v ∈ stack, ∀ l, v.loc? = some l →
      Live (s.heap.alloc o).1
        (roots P {s with heap := (s.heap.alloc o).1, accu := .ptr (s.heap.alloc o).2 0}) l) :
    VmPayload P {s with heap := (s.heap.alloc o).1, accu := .ptr (s.heap.alloc o).2 0, stack := stack} after pl cp newSp high := by
  have framed := heap_frame_log h.heap heapOutside memory
  have allocated := heap_allocate framed fields placed layout separate
  have objects : HeapRepr after pl cp P
      {s with heap := (s.heap.alloc o).1, accu := .ptr (s.heap.alloc o).2 0, stack := stack} :=
    heap_of_live allocated rfl (fun _ hl => live_stack_of_root root hl)
  exact payload_rebuild_accu h outside memory out trapWord words objects

end OCaml.Vm.Sim
