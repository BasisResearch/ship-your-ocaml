import OCaml.Vm.Primitives.Read
import OCaml.Vm.Primitives.Payload
import OCaml.Vm.Reloc
import Vsa.Sim.Boot.Bytes

/-! Observation frames for primitive writes. The write-log frame supplies byte
agreement; the existing relocation combinators transport represented objects
with the identity action. -/
namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- A footprint frame supplies every disjoint observation window. Values in
this log are irrelevant: only the recorded addresses and widths are used. -/
theorem copied_of_outsideLog {c c' : Config} {log : List WEntry} {a n : Nat}
    (memory : ∀ x, OutL log x → byte c' x = byte c x) (outside : OutLRange log a n) :
    Reloc.Copied c c' a a n :=
  fun i hi => memory _ (outL_of_range outside (by omega) (by omega))

/-- An exact observed write log supplies a footprint frame. -/
theorem outsideLog_of_observedLog {c c' : Config} {log : List WEntry}
    (memory : Vsa.Densify.MemEqv c'.σ.mem (writeLog c.σ.mem log)) :
    ∀ x, OutL log x → byte c' x = byte c x := by
  intro x outside
  rw [byte_total, byte_total]
  have same : (c'.σ.mem[x]?).getD 0 = ((writeLog c.σ.mem log)[x]?).getD 0 := memory x
  rw [writeLog_out _ _ _ outside] at same
  exact same

/-- A write log preserves every byte of a disjoint observation window. -/
theorem copied_of_writeLog {c c' : Config} {log : List WEntry} {a n : Nat}
    (memory : c'.σ.mem = writeLog c.σ.mem log) (outside : OutLRange log a n) :
    Reloc.Copied c c' a a n := by
  intro j hj
  rw [byte_total, byte_total, memory,
    writeLog_out _ _ _ (outL_of_range outside (by omega) (by omega))]

/-- The library model's total-byte write-log observation suffices for copying. -/
theorem copied_of_observedLog {c c' : Config} {log : List WEntry} {a n : Nat}
    (memory : Vsa.Densify.MemEqv c'.σ.mem (writeLog c.σ.mem log))
    (outside : OutLRange log a n) : Reloc.Copied c c' a a n := by
  intro j hj
  rw [byte_total, byte_total]
  have same : (c'.σ.mem[a + j]?).getD 0 = ((writeLog c.σ.mem log)[a + j]?).getD 0 := memory _
  rw [same, writeLog_out _ _ _ (outL_of_range outside (by omega) (by omega))]

/-- Total scalar observations are unchanged outside a first-order write log. -/
theorem bytesT_writeLog_out (m : Std.ExtHashMap Nat (BitVec 8)) {log : List WEntry} {a n : Nat}
    (outside : OutLRange log a n) : bytesT (writeLog m log) a n = bytesT m a n := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_bytesT _ _ _ _ hk, getLsbD_bytesT _ _ _ _ hk,
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
  let pl : Place := ⟨fun _ => none, 0, 0⟩
  have img : (Reloc.chanEqv a ch).Img id pl 0 0 c c' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Reloc.bytesT_congr (copied.mono chanOffFd 4 (by simp only [chanOffFd, chanOffBuff]; omega))
    · exact Reloc.bytesT_congr (copied.mono chanOffOffset 8 (by simp only [chanOffOffset, chanOffBuff]; omega))
    · exact Reloc.bytesT_congr (copied.mono chanOffCurr 8 (by simp only [chanOffCurr, chanOffBuff]; omega))
    · exact Reloc.bytesT_congr (copied.mono chanOffMax 8 (by simp only [chanOffMax, chanOffBuff]; omega))
    · exact Reloc.bytesT_congr (copied.mono chanOffEnd 8 (by simp only [chanOffEnd, chanOffBuff]; omega))
    · exact Reloc.bytesT_congr (copied.mono chanOffFlags 4 (by simp only [chanOffFlags, chanOffBuff]; omega))
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
structure PayloadObsOutside (log : List WEntry) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (sp : Nat) : Prop where
  domain : OutLRange log Layout.sym_Caml_state 8
  stackHigh : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) 8
  trapsp : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) 8
  codeBase : OutLRange log Layout.sym_caml_start_code 8
  atomBase : OutLRange log Layout.sym_caml_atom_table 8
  globals : OutLRange log Layout.sym_caml_global_data 8
  code : ∀ i w, P.code[i]? = some w → OutLRange log (pl.codeBase + 4 * i) 4
  stack : ∀ i v, s.stack[i]? = some v → OutLRange log (sp + 8 * i) 8
  heap : ∀ l a o, Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some o →
    ObjectOutside log a o
  channels : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    OutLRange log a (chanOffBuff + ch.buffer.length)

/-- `PayloadObsOutside` and the object-ID counter word. -/
structure PayloadOutside (log : List WEntry) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (sp : Nat) : Prop where
  domain : OutLRange log Layout.sym_Caml_state 8
  stackHigh : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) 8
  trapsp : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) 8
  codeBase : OutLRange log Layout.sym_caml_start_code 8
  atomBase : OutLRange log Layout.sym_caml_atom_table 8
  globals : OutLRange log Layout.sym_caml_global_data 8
  code : ∀ i w, P.code[i]? = some w → OutLRange log (pl.codeBase + 4 * i) 4
  stack : ∀ i v, s.stack[i]? = some v → OutLRange log (sp + 8 * i) 8
  heap : ∀ l a o, Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some o →
    ObjectOutside log a o
  channels : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    OutLRange log a (chanOffBuff + ch.buffer.length)
  ooId : OutLRange log Layout.sym_oo_last_id 8

theorem PayloadOutside.obs {log : List WEntry} {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp : Nat} (h : PayloadOutside log P s c pl cp sp) : PayloadObsOutside log P s c pl cp sp :=
  ⟨h.domain, h.stackHigh, h.trapsp, h.codeBase, h.atomBase, h.globals, h.code, h.stack, h.heap, h.channels⟩

/-- Transport the VM payload across a write footprint that may write the
object-ID counter: the counter word afterwards represents `n`. -/
theorem VmPayload.frame_obs {P s c c' pl cp sp high log}
    (h : VmPayload P s c pl cp sp high) (outside : PayloadObsOutside log P s c pl cp sp)
    (memory : ∀ x, OutL log x → byte c' x = byte c x)
    (outputEq : output c'.σ = output c.σ) (n : Nat)
    (counter : word c' Layout.sym_oo_last_id = tag64 (BitVec.ofNat 63 n)) :
    VmPayload P {s with world := {s.world with ooId := n}} c' pl cp sp high := by
  have copy := fun a n (ho : OutLRange log a n) => copied_of_outsideLog memory ho
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
  · refine ⟨?_, ?_, ?_⟩
    · rw [outputEq]; exact h.world.output
    · intro id ch hc
      obtain ⟨a, ha, layout⟩ := h.world.chans id ch hc
      exact ⟨a, ha, channel_copied layout (copy _ _ (outside.channels id ch a hc ha))⟩
    · exact counter
  · rw [hw _ outside.atomBase]
    exact h.atomBase

/-- Transport the complete VM payload across a checked write footprint. -/
theorem VmPayload.frame_outsideLog {P s c c' pl cp sp high log}
    (h : VmPayload P s c pl cp sp high) (outside : PayloadOutside log P s c pl cp sp)
    (memory : ∀ x, OutL log x → byte c' x = byte c x)
    (outputEq : output c'.σ = output c.σ) :
    VmPayload P s c' pl cp sp high := by
  have keep := h.frame_obs outside.obs memory outputEq s.world.ooId (by
    have e : word c' Layout.sym_oo_last_id = word c Layout.sym_oo_last_id :=
      Reloc.bytesT_congr (copied_of_outsideLog memory outside.ooId)
    rw [e]; exact h.world.ooId)
  exact keep

/-- Total-byte agreement with a write log specializes the footprint frame. -/
theorem VmPayload.frame_observedLog {P s c c' pl cp sp high log}
    (h : VmPayload P s c pl cp sp high) (outside : PayloadOutside log P s c pl cp sp)
    (memory : Vsa.Densify.MemEqv c'.σ.mem (writeLog c.σ.mem log))
    (outputEq : output c'.σ = output c.σ) : VmPayload P s c' pl cp sp high :=
  h.frame_outsideLog outside (outsideLog_of_observedLog memory) outputEq

/-- Exact write logs are a specialization of the observational frame. -/
theorem VmPayload.frame_log {P s c c' pl cp sp high log}
    (h : VmPayload P s c pl cp sp high) (outside : PayloadOutside log P s c pl cp sp)
    (memory : c'.σ.mem = writeLog c.σ.mem log) (outputEq : c'.σ.sailOutput = c.σ.sailOutput) :
    VmPayload P s c' pl cp sp high :=
  h.frame_observedLog outside (fun a => by rw [memory]) (by simp only [output, outputEq])

/-- Library readers preserve the complete VM payload through total observations. -/
theorem VmPayload.frame_observed {P s c c' pl cp sp high}
    (h : VmPayload P s c pl cp sp high) (memory : Vsa.Densify.MemEqv c'.σ.mem c.σ.mem)
    (outputEq : output c'.σ = output c.σ) : VmPayload P s c' pl cp sp high := by
  apply h.frame_observedLog (log := []) _ memory outputEq
  constructor
  all_goals first | trivial | (intros; trivial) | (intros; exact ⟨True.intro, True.intro⟩)

/-- The object-ID counter does not change roots, channels or console state;
its word represents the new counter. -/
theorem VmPayload.ooId {P s c pl cp sp high} (h : VmPayload P s c pl cp sp high) (n : Nat)
    (counter : word c Layout.sym_oo_last_id = tag64 (BitVec.ofNat 63 n)) :
    VmPayload P {s with world := {s.world with ooId := n}} c pl cp sp high :=
  ⟨h.stackHigh, h.trapsp, h.codeBase, h.code, h.globals, h.stack, h.heap,
    ⟨h.world.output, h.world.chans, counter⟩, h.atomBase⟩

/-- The primitive-table pointer and all referenced entries are outside a write
log. The caller supplies this from its table allocation and write separation. -/
structure BindingsOutside (log : List WEntry) (P : Prog) (c : Config) : Prop where
  contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8
  entries : ∀ i name, P.prims[i]? = some name →
    OutLRange log ((word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i) 8

/-- Preserve the ELF binding of bytecode primitive names across disjoint writes. -/
theorem bindings_frame_outsideLog {P c c' log} (h : PrimitiveBindings P c)
    (outside : BindingsOutside log P c)
    (memory : ∀ x, OutL log x → byte c' x = byte c x) : PrimitiveBindings P c' := by
  have contents : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents) :=
    Reloc.bytesT_congr (copied_of_outsideLog memory outside.contents)
  constructor
  intro i name hi
  obtain ⟨entry, he, target⟩ := h.targets i name hi
  refine ⟨entry, he, ?_⟩
  unfold primitiveTarget
  rw [contents]
  exact (Reloc.bytesT_congr (copied_of_outsideLog memory (outside.entries i name hi))).trans target

/-- Exact memory effects retain the existing primitive-table frame API. -/
theorem bindings_frame_log {P c c' log} (h : PrimitiveBindings P c)
    (outside : BindingsOutside log P c) (memory : c'.σ.mem = writeLog c.σ.mem log) :
    PrimitiveBindings P c' :=
  bindings_frame_outsideLog h outside (outsideLog_of_observedLog (fun x => by rw [memory]))

end OCaml.Vm.Primitives
