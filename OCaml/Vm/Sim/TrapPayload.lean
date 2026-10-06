import OCaml.Vm.Sim.PayloadRestore
import OCaml.Vm.Sim.StackStore
import OCaml.Vm.Sim.WriteGeometry

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A trap-pointer update leaves the represented stack and live objects intact. -/
structure TrapWriteOutside (log : List WEntry) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (sp : Nat) : Prop extends PayloadCoreOutside log P s c pl cp where
  stack : ∀ i v, s.stack[i]? = some v → OutLRange log (sp + 8 * i) 8
  heap : ∀ l a o, Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some o →
    ObjectOutside log a o

/-- Exact log of a native trap-pointer store. -/
def trapLog (domain high trap : Nat) : List WEntry :=
  [(domain + Layout.off_trapsp, 8, BitVec.ofNat 64 (high - 8 * trap))]

/-- Read back the new trap pointer and frame the remaining payload. -/
theorem payload_trap_written {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high trap : Nat}
    (h : VmPayload P s before pl cp sp high) (highNat : high < 2^64)
    (outside : TrapWriteOutside (trapLog (word before Layout.sym_Caml_state).toNat high trap)
      P s before pl cp sp)
    (memory : after.σ.mem = writeLog before.σ.mem
      (trapLog (word before Layout.sym_Caml_state).toNat high trap))
    (out : after.σ.sailOutput = before.σ.sailOutput) :
    VmPayload P {s with trap := trap} after pl cp sp high := by
  apply payload_rebuild h outside.toPayloadCoreOutside memory out
  · have domain : word after Layout.sym_Caml_state = word before Layout.sym_Caml_state :=
      Reloc.bytesT_congr (copied_of_writeLog memory outside.domain)
    have saved := word_after_writeLog_at memory 0 _ _ rfl trivial
    rw [domain, saved]
    exact Nat.mod_eq_of_lt (by omega)
  · exact stack_frame_log h.stack outside.stack memory
  · exact heap_frame_log h.heap outside.heap memory

/-- Geometry and separation supplied by the loop invariant for trap writes. -/
structure TrapWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high trap : Nat) : Prop where
  highNat : high < 2^64
  address : (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp < 2^64
  window : WriteWindow (word c Layout.sym_Caml_state + BitVec.ofNat 64 Layout.off_trapsp) 8
  payload : TrapWriteOutside (trapLog (word c Layout.sym_Caml_state).toNat high trap) P s c pl cp sp
  image : ImageOutside (trapLog (word c Layout.sym_Caml_state).toNat high trap)
  young : YoungOutside (trapLog (word c Layout.sym_Caml_state).toNat high trap) c
  bindings : BindingsOutside (trapLog (word c Layout.sym_Caml_state).toNat high trap) P c

/-- Restore a trap-pointer write together with stack-frame removal. -/
theorem trap_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high trap pc count : Nat} {accu : BitVec 64}
    (stable : WindowStable L.runtimeOk [⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩])
    (data : VmReprAt P s c pl cp sp high) (platform : PlatformOk L.runtimeOk c)
    (loop : LoopRegisters c) (space : TrapWriteOk P s c pl cp sp high trap)
    (bound : count ≤ s.stack.length) (value : valWord pl s.accu = some accu)
    (post : StackPost c pl pc (sp + 8 * count) accu
      (writeLog c.σ.mem (trapLog (word c Layout.sym_Caml_state).toNat high trap)) after)
    (geometry : OCaml.LoopGeometry L P s c pl cp high)
    (native : NativePlaced c) :
    Running L P {s with pc := pc, stack := s.stack.drop count, trap := trap} after := by
  have payload := payload_trap_written (payload_of_repr data) space.highNat space.payload post.memory post.output
  have memoryFrame : FrameOn [⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩] c.σ.mem after.σ.mem := by
    rw [post.memory]
    apply frameOn_writeLog
    simp only [trapLog, LogInW, InsideW, or_false, and_true]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  exact running_of_payload (payload_pc (payload_stack_drop payload bound) pc)
    (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory,
      stable c after memoryFrame platform.runtime⟩
    (post.registers data rfl rfl value) (post.loopRegisters loop)
    (geometry.frame_log rfl rfl space.payload.domain space.bindings.contents space.young post.memory)
    (native.frame_vm (ws := [⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp, (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩]) (by simp only [trapLog, LogInW, InsideW, or_false, and_true]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩) (by simp only [List.mem_singleton, forall_eq]; have := geometry.domain_below (off := Layout.off_trapsp + 8) (by decide); omega) space.payload.domain post.memory post.nativeSp)

end OCaml.Vm.Sim
