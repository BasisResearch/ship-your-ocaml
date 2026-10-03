import OCaml.Vm.Sim.FieldStore

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Separation of all non-heap observations from a heap-write log. The edited
heap is restored separately from object readbacks and reachability facts. -/
structure HeapWriteOutside (log : List WEntry) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (sp : Nat) : Prop where
  domain : OutLRange log Layout.sym_Caml_state 8
  stackHigh : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) 8
  trapsp : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) 8
  codeBase : OutLRange log Layout.sym_caml_start_code 8
  atomBase : OutLRange log Layout.sym_caml_atom_table 8
  globals : OutLRange log Layout.sym_caml_global_data 8
  code : ∀ i w, P.code[i]? = some w → OutLRange log (pl.codeBase + 4 * i) 4
  stack : ∀ i v, s.stack[i]? = some v → OutLRange log (sp + 8 * i) 8
  channels : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    OutLRange log a (chanOffBuff + ch.buffer.length)

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
  have copy := fun a n (ho : OutLRange log a n) => copied_of_writeLog memory ho
  have hw : ∀ a, OutLRange log a 8 → word after a = word before a :=
    fun a ho => Reloc.bytesT_congr (copy a 8 ho)
  have domain := hw Layout.sym_Caml_state outside.domain
  constructor
  · rw [domain, hw _ outside.stackHigh]
    exact h.stackHigh
  · rw [domain, hw _ outside.trapsp]
    exact h.trapsp
  · rw [hw _ outside.codeBase]
    exact h.codeBase
  · intro i w hi
    have he : word32 after (pl.codeBase + 4 * i) = word32 before (pl.codeBase + 4 * i) :=
      Reloc.bytesT_congr (copy _ 4 (outside.code i w hi))
    simpa only [he] using h.code i w hi
  · rw [hw _ outside.globals]
    exact h.globals
  · refine ⟨h.stack.1, ?_⟩
    intro i v hi
    rw [hw _ (outside.stack i v hi)]
    exact h.stack.2 i v hi
  · exact objects
  · refine ⟨?_, ?_⟩
    · have same : output after.σ = output before.σ := by simp only [output, out]
      simpa only [same] using h.world.1
    · intro id ch hc
      obtain ⟨a, ha, layout⟩ := h.world.2 id ch hc
      exact ⟨a, ha, channel_copied layout (copy _ _ (outside.channels id ch a hc ha))⟩
  · rw [hw _ outside.atomBase]
    exact h.atomBase

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
