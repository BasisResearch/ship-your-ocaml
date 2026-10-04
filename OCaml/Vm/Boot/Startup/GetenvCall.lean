import OCaml.Vm.Boot.Startup.GetenvPrefix
import OCaml.Vm.Primitives.RegisterPins
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def getenvSavedRegs (s1 s2 s3 s4 s5 s6 : BitVec 64) : GRegs :=
  [(9, s1), (18, s2), (19, s3), (20, s4), (21, s5), (22, s6)]
def getenvCallRegs (sp name reent s1 s2 s3 s4 s5 s6 : BitVec 64) : GRegs :=
  [(10, reent), (11, name), (12, nativeStack sp 32 + 12#64), (2, nativeStack sp 32)] ++
    getenvSavedRegs s1 s2 s3 s4 s5 s6

/-- Getenv's prologue and generated call establish the complete native search
register interface, preserving its caller's saved-register values. -/
theorem getenv_to_find (c : Config) (sp name ra s1 s2 s3 s4 s5 s6 : BitVec 64)
    (leaf : LeafInput ra c) (frame : NativeFrame sp 32)
    (regs : GHolds c.σ (getenvPrefixInput sp name ra))
    (saved : GHolds c.σ (getenvSavedRegs s1 s2 s3 s4 s5 s6)) :
    FnSummary 0x80037410#64 (fun d => d = c)
      (WriteRegistersPost [11, 10, 2, 12, 1] (getenvLog sp ra) c jal_80037428_call.target (getenvReent c)
        ((1, jal_80037428_call.link) :: getenvCallRegs sp name (getenvReent c) s1 s2 s3 s4 s5 s6)) := by
  apply summary_bind (getenv_prefix c sp name ra leaf frame regs) (fun _ post => post.pc)
  intro mid prepared
  have kept := holds_frame_ne prepared.frame saved
    (by simp only [getenvSavedRegs, keysG]; decide)
    (by simp only [getenvSavedRegs, keysG]; decide)
    (by simp only [getenvSavedRegs, keysG]; decide)
  have holds : GHolds mid.σ (getenvCallRegs sp name (getenvReent c) s1 s2 s3 s4 s5 s6) := by
    apply (gholds_append _ _).mpr
    exact ⟨⟨prepared.result, gholds_lookup (n := 11) _ prepared.regs (by rfl),
      gholds_lookup (n := 12) _ prepared.regs (by rfl), gholds_lookup (n := 2) _ prepared.regs (by rfl), trivial⟩, kept⟩
  have call := call_registers_summary jal_80037428_call_shape jal_80037428_call_decode mid
    (jal_80037428_call_pins prepared.image) prepared.good prepared.image prepared.tick prepared.minstret _ holds
    (by simp only [getenvCallRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [KeysAvoidRa, getenvCallRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide) (by rfl)
  apply call.weaken (fun _ eq => eq)
  intro after post
  exact prefix_call_post prepared post
end OCaml.Vm.Boot.Startup
