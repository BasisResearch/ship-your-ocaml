import OCaml.Vm.Primitives.ExitPath.HtifExit
import Vsa.Sim.TermEntry

namespace OCaml.Vm.Primitives.ExitPath.HtifExit
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- `_exit`'s HTIF store halts the machine with the requested exit code and the
output produced so far. This is the single architectural step at the parked
`sd a5, 1812(a4)`, certified by `stepOnce_tohost_G`. -/
theorem store_halts {c : Config} {e : BitVec 64} (small : e.toNat < 2 ^ 47)
    (good : GoodState c.σ) (image : ExecutableImage c)
    (pc : pcOf c = some 0x800008b0#64)
    (base : gpr c 14 = some 0x800618ac#64)
    (data : gpr c 15 = some ((e <<< 1) ||| 1#64))
    (idle : c.σ.regs.get? Register.htif_payload_writes = some 0#4) :
    Halts c (output c.σ) e.toNat := by
  obtain ⟨vm, hvm⟩ := good.minstret
  obtain ⟨th, hth⟩ := good.htif_tohost
  obtain ⟨b0, b1, b2, b3⟩ := Vsa.Sim.Code._exit_at_800008b0 (loaded image)
  have prelude : ∀ R : Register, (Register.minstret_increment == R) = false →
      (afterPrelude c.σ).regs.get? R = c.σ.regs.get? R := get?_afterPrelude c.σ
  have dec := Vsa.Sim.ElfDecode.decode_70f73a23 (afterPrelude c.σ)
    (by rw [prelude _ (by decide)]; exact good.misa)
    (by rw [prelude _ (by decide)]; exact good.cur_privilege)
    (by rw [prelude _ (by decide)]; exact good.mseccfg)
  have step := stepOnce_tohost_G c.σ c.tick c.steps 0x800008b0#64 vm 1895250467#32 1812#12
    (regidx.Regidx 15#5) (regidx.Regidx 14#5) 0x800618ac#64 ((e <<< 1) ||| 1#64) ((e <<< 1) ||| 1#64) e th
    0x23#8 0x3a#8 0xf7#8 0x70#8 good pc hvm (by decide) (by decide) dec
    (rX_src c.σ _ 14 (by decide) _ base) (rX_src c.σ _ 15 (by decide) _ data) (by decide) rfl idle hth small rfl
    b0 b1 b2 b3 (by decide) (by decide) (by decide)
  exact ⟨c, _, .refl c, .mk step, rfl⟩

end OCaml.Vm.Primitives.ExitPath.HtifExit
