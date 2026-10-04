import OCaml.Vm.Gc.Generated.AllocColor
import OCaml.Vm.Gc.AllocAccount

namespace OCaml.Vm.Gc.AllocColor
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def colored (black : Bool) (R : Nat → BitVec 64) (n : Nat) :=
  if n = 11 then header black (R 8) (R 11) else R n

structure Input (R : Nat → BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem
  registers : GHolds c.σ (regs R)

/-- The chosen header builder reaches accounting with unchanged memory
and the size/tag/color word in its actual store register. -/
structure Post (black : Bool) (R : Nat → BitVec 64) (before after : Config) : Prop where
  machine : BlockPost (blocks black) (pc black) (regs R) [] before after
  pc : PCAt AllocAccount.pc after
  memory : after.σ.mem = before.σ.mem
  registers : GHolds after.σ (AllocAccount.regs (colored black R))
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem

theorem prepare (black : Bool) {R c} (input : Input R c) :
    FnSummary (pc black) (fun d => d = c) (Post black R c) := by
  have facts := chainPlan_facts (code_facts black input.code) (access black c.σ.mem R)
  have summary := block_summary (blocks black) (pc black) (regs R) [] c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [2,8,10,11]; decide,
      facts,chain_ok black,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory,no_stores]; rfl
  refine ⟨post,?_,memory,?_,memory ▸ input.code⟩
  · rw [PCAt,post.pc,endpoint]
    rfl
  · have holds := post.regs
    change GHolds after.σ (runGM (block black).body (regs R) []) at holds
    rw [registers] at holds
    exact ⟨gholds_lookup _ holds rfl,gholds_lookup _ holds rfl,
      gholds_lookup _ holds rfl,gholds_lookup _ holds rfl,True.intro⟩

/-- A legal OCaml byte tag is unchanged by the native uint32 conversion. -/
theorem tag32_eq (tag : BitVec 64) (bound : tag.toNat < 256) : tag32 tag = tag := by
  apply BitVec.eq_of_toNat_eq
  simp only [tag32,BitVec.toNat_shiftLeft,BitVec.toNat_ushiftRight,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

/-- Both collector colors preserve the represented size and byte tag. -/
theorem header_ok (black : Bool) (size tag : BitVec 64)
    (sizeBound : size.toNat < 2^54) (tagBound : tag.toNat < 256) :
    HeaderOk (header black size tag) size.toNat tag.toNat := by
  unfold header
  rw [tag32_eq tag tagBound]
  cases black
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,HeaderOk,Layout.gc_black,Layout.gc_white,
    BitVec.toNat_add,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,BitVec.toNat_ofNat]
  all_goals constructor <;> omega

end OCaml.Vm.Gc.AllocColor
