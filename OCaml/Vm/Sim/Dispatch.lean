import OCaml.Vm.Sim.DispatchSegment
import OCaml.Vm.Sim.DispatchPins
import OCaml.Vm.Sim.DispatchTable

namespace OCaml.Vm.Sim
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- The dispatch loop's concrete inputs. The VM representation supplies the
opcode and registers; code placement supplies RAM geometry. No machine run
or selected-target premise is assumed. -/
structure DispatchInput (op : Opcode) (a : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  loop : LoopRegisters c
  atHead : pcOf c = some (BitVec.ofNat 64 Layout.loopHead)
  codeReg : gpr c Layout.reg_pc = some a
  opcode : word32 c a.toNat = BitVec.ofNat 32 op.toNat
  tick : c.tick < 2
  lower : 0x80000000 ≤ a.toNat
  upper : a.toNat + 4 ≤ 0x100000000
  htif : a.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat

/-- Dispatch changes only the decoded target, advanced bytecode pointer,
and the machine's standard step bookkeeping. -/
structure DispatchPost (before : Config) (op : Opcode) (a : BitVec 64)
    (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : pcOf after = some (BitVec.ofNat 64 (dispatchTarget op))
  nextCode : gpr after 23 = some (a + 4#64)
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut ([Register.x15, Register.x23] ++ noiseRegs) before.σ after.σ

/-- Connect the generated eight-step path to the pinned table. The remaining
arm proof starts exactly at its census target, with a complete read-only frame. -/
theorem dispatch_run {op : Opcode} {a : BitVec 64} {c : Config}
    (h : DispatchInput op a c) :
    ∃ n c', 8 ≤ n ∧ StepsN n c c' ∧ DispatchPost c op a c' := by
  have hread : bytesT4 c.σ.mem a.toNat = BitVec.ofNat 32 op.toNat := by
    simpa only [word32, bytesT_four_eq] using h.opcode
  have htable : bytesT4 c.σ.mem (Layout.jumpTable + 4 * op.toNat) = dispatchOffset op := by
    simpa only [word32, bytesT_four_eq] using dispatchOffset_loaded h.image op
  have hz : sign_extend (m := 64) (0x000#12) = 0#64 := by decide
  have hfour : sign_extend (m := 64) (0x004#12) = 4#64 := by decide
  have run := tr_dispatch a (BitVec.ofNat 64 Layout.opcodeBound)
    (BitVec.ofNat 64 Layout.jumpTable) c.σ.mem c.σ
  simp only [hz, BitVec.add_zero, hfour, hread, dispatchIndex, dispatchIndex_nat,
    htable, dispatchOffset_target, dispatchTarget_clear] at run
  have pre : SegSt (0x80001f5c#64)
      [⟨Register.x8, a⟩, ⟨Register.x24, BitVec.ofNat 64 Layout.opcodeBound⟩,
       ⟨Register.x22, BitVec.ofNat 64 Layout.jumpTable⟩]
      (fun σ => Vsa.Sim.Code.CamlDispatchLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.good, h.atHead, ⟨h.codeReg, h.loop.opcodeBound, h.loop.dispatchTable, trivial⟩,
      h.good.minstret, h.tick, dispatch_loaded h.image, rfl, rfl⟩
  obtain ⟨n, after, hn, steps, post⟩ := run h.lower h.upper h.htif (dispatchOpcode_guard op)
    (dispatchIndex_lower op) (dispatchIndex_upper op) (dispatchIndex_htif op)
    (dispatchTarget_aligned op) c pre
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨n, after, hn, steps, post.good, post.tick, post.pcAt, ?_, hm, ?_⟩
  · exact PinsHold.get post.pins ⟨1, by simp⟩
  · refine ⟨frame.out, ?_⟩
    intro r hr
    apply frame.frame r
    intro q hq
    apply hr q
    simpa only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, false_or, or_self, or_self_left,
      or_assoc, or_left_comm, or_comm] using hq

end OCaml.Vm.Sim
