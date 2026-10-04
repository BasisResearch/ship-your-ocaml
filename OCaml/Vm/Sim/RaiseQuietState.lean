import OCaml.Vm.Sim.RaiseCheck
import OCaml.Vm.Sim.RaiseHandler

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- No debugger trap barrier and no active backtrace in the quiet exception path.
Runtime/startup supplies these memory facts and domain read geometry. -/
structure RaiseQuietReady (high : Nat) (c : Config) : Prop where
  barrier : word c ((word c Layout.sym_Caml_state).toNat + Layout.off_trap_barrier) = BitVec.ofNat 64 high
  backtrace : word c ((word c Layout.sym_Caml_state).toNat + Layout.off_backtrace_active) = 0#64
  trapRead : RamReadAt ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) 8
  barrierRead : RamReadAt ((word c Layout.sym_Caml_state).toNat + Layout.off_trap_barrier) 8
  backtraceRead : RamReadAt ((word c Layout.sym_Caml_state).toNat + Layout.off_backtrace_active) 8
  highRead : RamReadAt ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) 8

/-- Field addressing is uniform across the domain's native loads. -/
theorem domain_field_address (w : BitVec 64) (offset : Nat) :
    w + BitVec.ofNat 64 offset = BitVec.ofNat 64 (w.toNat + offset) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat]; rfl

/-- The original loop representation supplies the memory context for a raise. -/
theorem raise_context {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val} {c : Config} {op : Opcode}
    (h : ArmInput L P s op c pl cp sp high) (frame : RaiseFrame s dest link env extra rest) :
    RaiseContext L P s pl cp sp high dest link env extra rest c :=
  ⟨payload_of_repr h.toVmReprAt, h.primitives, h.running.platform, frame, h.accu, h.dispatch.tick⟩

/-- Domain trap readback follows from the represented absolute trap pointer. -/
theorem RaiseContext.trap_word {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val} {c : Config}
    (h : RaiseContext L P s pl cp sp high dest link env extra rest c) :
    word c ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) = BitVec.ofNat 64 (high - 8 * s.trap) := by
  rw [← h.data.trapsp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Read-only native prefixes preserve the trap-write geometry and all frames. -/
theorem TrapWriteOk.frame {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high trap : Nat} {c after : Config}
    (h : TrapWriteOk P s c pl cp sp high trap) (memory : after.σ.mem = c.σ.mem) :
    TrapWriteOk P s after pl cp sp high trap := by
  have words (a : Nat) : word after a = word c a := by simp only [word, memory]
  refine ⟨h.highNat, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [words] using h.address
  · simpa only [words] using h.window
  · rw [words]
    exact {
      toPayloadCoreOutside := { h.payload.toPayloadCoreOutside with stackHigh := by simpa only [words] using h.payload.stackHigh }
      stack := h.payload.stack, heap := h.payload.heap }
  · simpa only [words] using h.image
  · rw [words]
    exact ⟨h.bindings.contents, by simpa only [words] using h.bindings.entries⟩

end OCaml.Vm.Sim
