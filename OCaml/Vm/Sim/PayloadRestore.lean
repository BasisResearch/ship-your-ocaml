import OCaml.Vm.Sim.FieldRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Observations unchanged by local stack, trap and heap edits. Mutable
components have separate readback proofs rather than duplicated whole-payload frames. -/
structure PayloadCoreOutside (log : List WEntry) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) : Prop where
  domain : OutLRange log Layout.sym_Caml_state 8
  stackHigh : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) 8
  codeBase : OutLRange log Layout.sym_caml_start_code 8
  atomBase : OutLRange log Layout.sym_caml_atom_table 8
  globals : OutLRange log Layout.sym_caml_global_data 8
  code : ∀ i w, P.code[i]? = some w → OutLRange log (pl.codeBase + 4 * i) 4
  channels : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    OutLRange log a (chanOffBuff + ch.buffer.length)

/-- Rebuild mutable payload components after a log, copying the fixed
observations once through total-byte and relocation combinators. -/
theorem payload_rebuild_accu {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp newSp high trap : Nat} {log : List WEntry}
    {heap : Heap} {stack : List Val} {accu : Val}
    (h : VmPayload P s before pl cp sp high)
    (outside : PayloadCoreOutside log P s before pl cp)
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (out : after.σ.sailOutput = before.σ.sailOutput)
    (trapWord : (word after ((word after Layout.sym_Caml_state).toNat + Layout.off_trapsp)).toNat = high - 8 * trap)
    (words : StackRepr after pl newSp high stack)
    (objects : HeapRepr after pl cp P {s with heap := heap, stack := stack, trap := trap, accu := accu}) :
    VmPayload P {s with heap := heap, stack := stack, trap := trap, accu := accu} after pl cp newSp high := by
  have copy := fun a n (ho : OutLRange log a n) => copied_of_writeLog memory ho
  have hw : ∀ a, OutLRange log a 8 → word after a = word before a :=
    fun a ho => Reloc.bytesT_congr (copy a 8 ho)
  have domain := hw Layout.sym_Caml_state outside.domain
  constructor
  · rw [domain, hw _ outside.stackHigh]
    exact h.stackHigh
  · exact trapWord
  · rw [hw _ outside.codeBase]
    exact h.codeBase
  · intro i w hi
    have he : word32 after (pl.codeBase + 4 * i) = word32 before (pl.codeBase + 4 * i) :=
      Reloc.bytesT_congr (copy _ 4 (outside.code i w hi))
    simpa only [he] using h.code i w hi
  · rw [hw _ outside.globals]
    exact h.globals
  · exact words
  · exact objects
  · refine ⟨?_, ?_⟩
    · have same : output after.σ = output before.σ := by simp only [output, out]
      simpa only [same] using h.world.1
    · intro id ch hc
      obtain ⟨a, ha, layout⟩ := h.world.2 id ch hc
      exact ⟨a, ha, channel_copied layout (copy _ _ (outside.channels id ch a hc ha))⟩
  · rw [hw _ outside.atomBase]
    exact h.atomBase

/-- Existing rebuilding interface for arms that retain the accumulator. -/
theorem payload_rebuild {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp newSp high trap : Nat} {log : List WEntry}
    {heap : Heap} {stack : List Val}
    (h : VmPayload P s before pl cp sp high)
    (outside : PayloadCoreOutside log P s before pl cp)
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (out : after.σ.sailOutput = before.σ.sailOutput)
    (trapWord : (word after ((word after Layout.sym_Caml_state).toNat + Layout.off_trapsp)).toNat = high - 8 * trap)
    (words : StackRepr after pl newSp high stack)
    (objects : HeapRepr after pl cp P {s with heap := heap, stack := stack, trap := trap}) :
    VmPayload P {s with heap := heap, stack := stack, trap := trap} after pl cp newSp high :=
  payload_rebuild_accu h outside memory out trapWord words objects

/-- Copy the represented heap when all live objects lie outside the log. -/
theorem heap_frame_log {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {log : List WEntry}
    (h : HeapRepr before pl cp P s)
    (outside : ∀ l a o, Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some o →
      ObjectOutside log a o)
    (memory : after.σ.mem = writeLog before.σ.mem log) : HeapRepr after pl cp P s := by
  constructor
  · intro l live
    obtain ⟨a, o, placed, selected, object⟩ := h.1 l live
    have separate := outside l a o live placed selected
    exact ⟨a, o, placed, selected, object_copied object
      (copied_of_writeLog memory separate.header) (copied_of_writeLog memory separate.payload)⟩
  · exact h.2

/-- Copy stack slots without imposing separation on other payload components. -/
theorem stack_frame_log {before after : Config} {pl : Place} {sp high : Nat}
    {stack : List Val} {log : List WEntry}
    (h : StackRepr before pl sp high stack)
    (outside : ∀ i v, stack[i]? = some v → OutLRange log (sp + 8 * i) 8)
    (memory : after.σ.mem = writeLog before.σ.mem log) : StackRepr after pl sp high stack := by
  refine ⟨h.1, ?_⟩
  intro i v selected
  have same : word after (sp + 8 * i) = word before (sp + 8 * i) :=
    Reloc.bytesT_congr (copied_of_writeLog memory (outside i v selected))
  rw [same]
  exact h.2 i v selected

end OCaml.Vm.Sim
