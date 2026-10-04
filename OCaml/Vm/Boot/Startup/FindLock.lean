import OCaml.Vm.Boot.Startup.FindFrame
import OCaml.Vm.Boot.Startup.EnvLock
import OCaml.Vm.Boot.Startup.LeafCall
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def findParked (sp reent name offset s1 : BitVec 64) : GRegs :=
  [(21, reent), (22, offset), (18, name), (19, BitVec.ofNat 64 Layout.sym_environ),
   (2, nativeStack sp 80), (9, s1)]

/-- The native saving prologue followed by the actual environment-lock call. -/
theorem find_locked (c : Config) (sp reent name offset ra s1 s2 s3 s5 s6 : BitVec 64)
    (leaf : LeafInput ra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findPrefixInput sp reent name offset ra s1 s2 s3 s5 s6)) :
    FnSummary 0x80037438#64 (fun d => d = c)
      (WriteRegistersPost [2, 19, 18, 22, 21, 1, 10] (findPrefixLog sp ra s1 s2 s3 s5 s6) c
        jal_80037468_call.link (envLockValue false)
        ((10, envLockValue false) :: (1, jal_80037468_call.link) :: findParked sp reent name offset s1)) := by
  apply summary_bind (find_prefix c sp reent name offset ra s1 s2 s3 s5 s6 leaf frame regs) (fun _ post => post.pc)
  intro mid prepared
  have holds : GHolds mid.σ ((10, reent) :: findParked sp reent name offset s1) :=
    holds_project prepared.regs (by simp [findPrefixRegs, findParked, lookupG])
  have call := scalar_leaf_call jal_80037468_call jal_80037468_call_shape jal_80037468_call_decode
    (envLockValue false) mid ra reent (prepared.leaf (by rfl) leaf.aligned)
    (jal_80037468_call_pins prepared.image) (findParked sp reent name offset s1) holds
    (by simp only [findParked, keysG]; decide) (by simp only [KeysAvoidRa, findParked, keysG]; decide)
    (by simp only [findParked, keysG]; decide) (by simp only [findParked, keysG]; decide) (by decide)
    (fun state h => env_lock false state _ h)
  apply call.weaken (fun _ eq => eq)
  intro after post
  exact prefix_readonly_post prepared post
end OCaml.Vm.Boot.Startup
