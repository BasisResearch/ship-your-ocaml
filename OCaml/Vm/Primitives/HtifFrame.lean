import OCaml.Vm.Primitives.Register
import VsaIris.Vsa.Instance

/-! Every exact-effect post frames the HTIF payload counter: it is neither a
GPR nor a noise register, so an idle HTIF stays idle across the call. -/
namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

theorem EffectPost.htifIdle {writes mem before after ra value}
    (post : EffectPost writes mem before ra value after)
    (idle : before.σ.regs.get? Register.htif_payload_writes = some (0#4)) :
    after.σ.regs.get? Register.htif_payload_writes = some (0#4) := by
  rw [post.frame _ (fun n _ => by
    have h := VsaIris.Inst.gprReg_htif_payload n
    exact fun eq => by rw [eq, beq_self_eq_true] at h; contradiction) (by decide)]
  exact idle

end OCaml.Vm.Primitives
