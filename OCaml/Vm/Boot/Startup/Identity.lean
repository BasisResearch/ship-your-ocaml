import OCaml.Vm.Boot.Startup.UserIdRows
import OCaml.Vm.Boot.Startup.EffectiveUserIdRows
import OCaml.Vm.Boot.Startup.GroupIdRows
import OCaml.Vm.Boot.Startup.EffectiveGroupIdRows
import OCaml.Vm.Boot.Startup.UserIdImage
import OCaml.Vm.Boot.Startup.EffectiveUserIdImage
import OCaml.Vm.Boot.Startup.GroupIdImage
import OCaml.Vm.Boot.Startup.EffectiveGroupIdImage
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.Control
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The bare-metal identity functions share the same zero-return protocol. -/
inductive IdentityKind where
  | user | effectiveUser | group | effectiveGroup

def IdentityKind.entry : IdentityKind → BitVec 64
  | .user => 0x80001d74#64
  | .effectiveUser => 0x80001d7c#64
  | .group => 0x80001d84#64
  | .effectiveGroup => 0x80001d8c#64

def IdentityKind.blocks : IdentityKind → List BBlock
  | .user => getuidX1d74Seg
  | .effectiveUser => geteuidX1d7cSeg
  | .group => getgidX1d84Seg
  | .effectiveGroup => getegidX1d8cSeg

theorem identity_input (kind : IdentityKind) {ra c} (h : LeafInput ra c) :
    BlockInput kind.blocks kind.entry [(1, ra)] [] c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.raReg, trivial⟩
  keys := by change KeysOK [1]; decide
  shape := by change ChainOK kind.entry [1] kind.blocks; cases kind <;> decide
  tick := h.tick
  facts := by
    have user := userId_code h.image
    have effectiveUser := effectiveUserId_code h.image
    have group := groupId_code h.image
    have effectiveGroup := effectiveGroupId_code h.image
    have ret : (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0 := by
      rw [ret_tgt ra h.aligned]
      exact h.aligned
    cases kind with
    | user => chain_facts user with "Vsa.Sim.Code.getuid_at_"; exact ret
    | effectiveUser => chain_facts effectiveUser with "Vsa.Sim.Code.geteuid_at_"; exact ret
    | group => chain_facts group with "Vsa.Sim.Code.getgid_at_"; exact ret
    | effectiveGroup => chain_facts effectiveGroup with "Vsa.Sim.Code.getegid_at_"; exact ret

/-- Both real/effective user and group identities are zero in this runtime. -/
theorem identity_zero (kind : IdentityKind) (c : Config) (ra : BitVec 64) (h : LeafInput ra c) :
    FnSummary kind.entry (fun d => d = c)
      (WriteRegistersPost [10] [] c ra 0#64 [(10, 0#64), (1, ra)]) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (identity_input kind h))
  · cases kind <;> rfl
  · cases kind <;> exact ret_tgt ra h.aligned
  · cases kind <;> rfl
  · rfl
  · cases kind <;> decide
end OCaml.Vm.Boot.Startup
