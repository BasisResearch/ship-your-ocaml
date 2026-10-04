import OCaml.Vm.Sim.SignedDivision
import OCaml.Vm.Sim.DivisionArithmetic
import OCaml.Vm.Sim.ArithmeticCallFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

def divisionOpcode : DivisionKind → Opcode
  | .quotient => .DIVINT
  | .remainder => .MODINT

def divisionCallerReturn : DivisionKind → BitVec 64
  | .quotient => 0x80002d24#64
  | .remainder => 0x80002cfc#64

/-- Both consuming callers share the represented libgcc call boundary. -/
structure DivisionCall (kind : DivisionKind) (before : Config) (pl : Place) (pc sp : Nat)
    (x y : BitVec 63) (c : Config) : Prop
    extends SignedDivisionInput ((tag64 x).sshiftRight 1) ((tag64 y).sshiftRight 1) (divisionCallerReturn kind) c,
      ArithmeticCallFrame before pl pc sp c where
  calleePC : pcOf c = some (divisionEntry kind)

/-- Signed libgcc returns a native word for the generated caller to retag. -/
structure DivisionReturn (kind : DivisionKind) (before : Config) (pl : Place) (pc sp : Nat)
    (x y : BitVec 63) (c : Config) : Prop
    extends ArithmeticCallFrame before pl pc sp c where
  good : GoodState c.σ
  image : ExecutableImage c
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  returnPC : pcOf c = some (divisionCallerReturn kind)
  result : gpr c 10 = some (divisionResult kind ((tag64 x).sshiftRight 1) ((tag64 y).sshiftRight 1))

/-- Preserve the interpreter's caller observations through the full signed call. -/
theorem division_callee {kind : DivisionKind} {before : Config} {pl : Place} {pc sp : Nat} {x y : BitVec 63} :
    Vsa.Logic.Triple (DivisionCall kind before pl pc sp x y) (DivisionReturn kind before pl pc sp x y) := by
  intro c h
  obtain ⟨after, run, post⟩ := (signed_division_summary kind h.toSignedDivisionInput).run c ⟨h.calleePC, rfl⟩
  refine ⟨after, run, ?_, post.good, post.image, post.minstret, post.tick, post.pc, post.result⟩
  exact ⟨(post.frame.frame Register.x23 (by decide)).trans h.nextCode,
    (post.frame.frame Register.x9 (by decide)).trans h.stack,
    post.memory.trans h.memory, post.frame.out.trans h.output,
    fun r hr => (post.frame.frame r (by revert r; decide)).trans (h.preserved r hr)⟩

end OCaml.Vm.Sim
