import OCaml.Vm.Primitives.Read
import OCaml.Vm.Primitives.Payload
import OCaml.Vm.Reloc

/-! Observation frames for primitive writes. The write-log frame supplies byte
agreement; the existing relocation combinators transport represented objects
with the identity action. -/
namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- A write log preserves every byte of a disjoint observation window. -/
theorem copied_of_writeLog {c c' : Config} {log : List WEntry} {a n : Nat}
    (memory : c'.σ.mem = writeLog c.σ.mem log) (outside : OutLRange log a n) :
    Reloc.Copied c c' a a n := by
  intro j hj
  rw [byte_total, byte_total, memory,
    writeLog_out _ _ _ (outL_of_range outside (by omega) (by omega))]

/-- Identity law for the placement action, reused by every fixed-address frame. -/
theorem placement_identity (pl : Place) : Reloc.reloc id pl = pl := by
  -- discipline: allow(O6-hand-relocation) generic identity law for the action; component frames below use Eqv.transport
  simp [Reloc.reloc]

/-- Copying an object's header and payload preserves its representation.
Pointer fields use the existing typed relocation action at identity. -/
theorem object_copied {c c' : Config} {pl : Place} {cp : ChanPlace} {a : Nat} {o : Obj}
    (h : ObjAt c pl cp a o) (header : Reloc.Copied c c' (a - 8) (a - 8) 8)
    (payload : Reloc.Copied c c' a a (8 * o.wosize)) : ObjAt c' pl cp a o := by
  have hw : word c' (a - 8) = word c (a - 8) := Reloc.bytesT_congr header
  have moved : Reloc.ObjMoved c c' pl id a o := by
    refine ⟨congrArg Reloc.headerView hw, ?_, fun _ => payload⟩
    intro t fs ho i v hi
    subst o
    have hn := (List.getElem?_eq_some_iff.mp hi).1
    have field : word c' (a + 8 * i) = word c (a + 8 * i) :=
      Reloc.bytesT_congr (payload.mono (8 * i) 8 (by simp only [Obj.wosize]; omega))
    rw [placement_identity]
    change valWord pl v = some (word c' (a + 8 * i))
    rw [field]
    exact h.2 i v hi
  have result := (Reloc.objEqv cp o).transport id pl a a c c'
    ((Reloc.objAt_eq c pl cp a o).mp h) (Reloc.objImg h moved)
  simpa only [placement_identity, ← Reloc.objAt_eq] using result

/-- Channels stay at their malloc address; only their observed window matters. -/
theorem channel_copied {c c' : Config} {a : Nat} {ch : Chan}
    (h : ChanAt c a ch)
    (copied : Reloc.Copied c c' a a (chanOffBuff + ch.buffer.length)) : ChanAt c' a ch := by
  let pl : Place := ⟨fun _ => none, 0⟩
  have img : (Reloc.chanEqv a ch).Img id pl 0 0 c c' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact Reloc.bytesT_congr (copied.mono chanOffFd 4 (by simp only [chanOffFd, chanOffBuff]; omega))
    · exact Reloc.bytesT_congr (copied.mono chanOffOffset 8 (by simp only [chanOffOffset, chanOffBuff]; omega))
    · exact Reloc.bytesT_congr (copied.mono chanOffCurr 8 (by simp only [chanOffCurr, chanOffBuff]; omega))
    · exact Reloc.bytesT_congr (copied.mono chanOffMax 8 (by simp only [chanOffMax, chanOffBuff]; omega))
    · intro i b hb
      have hi := (List.getElem?_eq_some_iff.mp hb).1
      change byte c' (a + chanOffBuff + i) = byte c (a + chanOffBuff + i)
      simpa only [Nat.add_assoc] using copied (chanOffBuff + i) (by omega)
  exact (Reloc.chanEqv a ch).transport id pl 0 0 c c' h img

structure ObjectOutside (log : List WEntry) (a : Nat) (o : Obj) : Prop where
  header : OutLRange log (a - 8) 8
  payload : OutLRange log a (8 * o.wosize)

/-- Static separation of a callee's writes from the VM's observations.
The caller supplies this from stack/code/global separation and allocator
placement invariants; it makes no assumption about machine execution. -/
structure PayloadOutside (log : List WEntry) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (sp : Nat) : Prop where
  domain : OutLRange log Layout.sym_Caml_state 8
  stackHigh : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) 8
  trapsp : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) 8
  codeBase : OutLRange log Layout.sym_caml_start_code 8
  globals : OutLRange log Layout.sym_caml_global_data 8
  code : ∀ i w, P.code[i]? = some w → OutLRange log (pl.codeBase + 4 * i) 4
  stack : ∀ i v, s.stack[i]? = some v → OutLRange log (sp + 8 * i) 8
  heap : ∀ l a o, Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some o →
    ObjectOutside log a o
  channels : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    OutLRange log a (chanOffBuff + ch.buffer.length)

/-- Transport the complete VM payload using only the checked write log. -/
theorem VmPayload.frame_log {P s c c' pl cp sp high log}
    (h : VmPayload P s c pl cp sp high) (outside : PayloadOutside log P s c pl cp sp)
    (memory : c'.σ.mem = writeLog c.σ.mem log) (outputEq : c'.σ.sailOutput = c.σ.sailOutput) :
    VmPayload P s c' pl cp sp high := by
  have copy := fun a n (ho : OutLRange log a n) => copied_of_writeLog memory ho
  have hw : ∀ a, OutLRange log a 8 → word c' a = word c a :=
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
    have he : word32 c' (pl.codeBase + 4 * i) = word32 c (pl.codeBase + 4 * i) :=
      Reloc.bytesT_congr (copy _ 4 (outside.code i w hi))
    simpa only [he] using h.code i w hi
  · rw [hw _ outside.globals]
    exact h.globals
  · refine ⟨h.stack.1, ?_⟩
    intro i v hi
    rw [hw _ (outside.stack i v hi)]
    exact h.stack.2 i v hi
  · constructor
    · intro l hl
      obtain ⟨a, o, ha, ho, layout⟩ := h.heap.1 l hl
      have iso := outside.heap l a o hl ha ho
      exact ⟨a, o, ha, ho, object_copied layout (copy _ 8 iso.header) (copy _ _ iso.payload)⟩
    · exact h.heap.2
  · refine ⟨?_, ?_⟩
    · simpa only [output, outputEq] using h.world.1
    · intro id ch hc
      obtain ⟨a, ha, layout⟩ := h.world.2 id ch hc
      exact ⟨a, ha, channel_copied layout (copy _ _ (outside.channels id ch a hc ha))⟩

/-- The object-ID counter does not change roots, channels or console state. -/
theorem VmPayload.ooId {P s c pl cp sp high} (h : VmPayload P s c pl cp sp high) (n : Nat) :
    VmPayload P {s with world := {s.world with ooId := n}} c pl cp sp high :=
  ⟨h.stackHigh, h.trapsp, h.codeBase, h.code, h.globals, h.stack, h.heap, h.world⟩

/-- The primitive-table pointer and all referenced entries are outside a write
log. The caller supplies this from its table allocation and write separation. -/
structure BindingsOutside (log : List WEntry) (P : Prog) (c : Config) : Prop where
  contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8
  entries : ∀ i name, P.prims[i]? = some name →
    OutLRange log ((word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i) 8

/-- Preserve the ELF binding of bytecode primitive names across disjoint writes. -/
theorem bindings_frame_log {P c c' log} (h : PrimitiveBindings P c)
    (outside : BindingsOutside log P c)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : PrimitiveBindings P c' := by
  have contents : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents) :=
    Reloc.bytesT_congr (copied_of_writeLog memory outside.contents)
  constructor
  intro i name hi
  obtain ⟨entry, he, target⟩ := h.targets i name hi
  refine ⟨entry, he, ?_⟩
  unfold primitiveTarget
  rw [contents]
  exact (Reloc.bytesT_congr (copied_of_writeLog memory (outside.entries i name hi))).trans target

end OCaml.Vm.Primitives
