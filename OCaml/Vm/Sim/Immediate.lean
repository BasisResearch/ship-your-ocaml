import OCaml.Vm.Sim.ArmInput

namespace OCaml.Vm.Sim
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable
open OCaml.Vm.Primitives

/-- Registers unchanged by arms that only advance PC and replace the
accumulator with an immediate. Use the generated register assignment. -/
def immediatePreserved : List Register :=
  [gprReg Layout.reg_sp, gprReg Layout.reg_env, gprReg Layout.reg_extra,
   gprReg Layout.reg_dispatchTable, gprReg Layout.reg_opcodeBound,
   gprReg Layout.reg_pending, gprReg Layout.reg_domain]

/-- Machine observations sufficient to restore an immediate-result VM state.
The generated segment supplies execution and its complete frame separately. -/
structure ImmediatePost (before : Config) (pl : Place) (pc : Nat) (n : BitVec 63)
    (after : Config) : Prop where
  good : GoodState after.σ
  head : pcOf after = some (BitVec.ofNat 64 Layout.loopHead)
  code : gpr after Layout.reg_pc = some (BitVec.ofNat 64 (pl.codeBase + 4 * pc))
  accu : gpr after Layout.reg_accu = some (tag64 n)
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  preserved : ∀ r ∈ immediatePreserved, after.σ.regs.get? r = before.σ.regs.get? r

theorem codePc_succ (pl : Place) (pc : Nat) :
    BitVec.ofNat 64 (pl.codeBase + 4 * pc) + 4#64 =
      BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 1)) := by
  simp only [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, BitVec.ofNat_add]

/-- One restoration proof for all read-only, immediate-result arms. -/
theorem immediate_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high pc : Nat} {n : BitVec 63}
    (stable : MemoryStable L.runtimeOk) (data : VmReprAt P s c pl cp sp high)
    (platform : PlatformOk L.runtimeOk c) (loop : LoopRegisters c)
    (post : ImmediatePost c pl pc n after) :
    Running L P {s with pc := pc, accu := .int n} after := by
  have payload := (payload_pc ((payload_of_repr data).accu_int n) pc).frame post.memory post.output
  refine ⟨⟨pl, cp, sp, high, ?_⟩, ?_, ?_⟩
  · refine ⟨post.head, post.code, ?_, ⟨tag64 n, post.accu, rfl⟩, ?_, ?_,
      payload.stackHigh, payload.trapsp, payload.codeBase, payload.code,
      payload.globals, payload.stack, payload.heap, payload.world, data.primitives.frame post.memory⟩
    · exact (post.preserved _ (by decide)).trans data.spReg
    · obtain ⟨w, hw, hv⟩ := data.env
      exact ⟨w, (post.preserved _ (by decide)).trans hw, hv⟩
    · exact (post.preserved _ (by decide)).trans data.extra
  · exact ⟨post.good,
      ⟨fun i hi => by rw [post.memory]; exact platform.image.text i hi,
       fun i hi => by rw [post.memory]; exact platform.image.rodata i hi⟩,
      stable c after post.memory platform.runtime⟩
  · exact ⟨(post.preserved _ (by decide)).trans loop.dispatchTable,
      (post.preserved _ (by decide)).trans loop.opcodeBound,
      (post.preserved _ (by decide)).trans loop.pending,
      (post.preserved _ (by decide)).trans loop.domain⟩

/-- Check a generated write-set once, then consume the whole frame. -/
theorem immediate_preserved {W : List Register} {σ σ' : MState}
    (frame : StepFrameOut W σ σ')
    (avoid : ∀ r ∈ immediatePreserved, ∀ q ∈ W, (q == r) = false) :
    ∀ r ∈ immediatePreserved, σ'.regs.get? r = σ.regs.get? r :=
  fun r hr => frame.frame r (avoid r hr)

end OCaml.Vm.Sim
