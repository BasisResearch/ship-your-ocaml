import OCaml.Vm.Primitives.ConsoleWrite
import Vsa.Sim.HtifStepObs

/-! The HTIF putchar store in `_write`'s console loop. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

theorem output_push {σ σ' : MState} {x : String} (h : σ'.sailOutput = σ.sailOutput.push x) :
    Vsa.Machine.output σ' = Vsa.Machine.output σ ++ x := by
  unfold Vsa.Machine.output
  rw [h, Array.toList_push, String.join_append]
  simp

/-- The putchar word of one console byte. -/
abbrev putcWord (b : BitVec 8) : BitVec 64 := 0x0101000000000000#64 ||| BitVec.zeroExtend 64 b

/-- After the store: one more character of output; memory, every GPR and the
image unchanged; the HTIF idle again. -/
structure PutcharPost (c : Config) (b : BitVec 8) (d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  pc : pcOf d = some 0x80000f80#64
  memory : d.σ.mem = c.σ.mem
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ ++ toString (Char.ofNat b.toNat)
  idle : d.σ.regs.get? Register.htif_payload_writes = some 0#4
  gpr : ∀ n, gpr d n = gpr c n

theorem putchar_step {c : Config} {b : BitVec 8}
    (good : GoodState c.σ) (image : ExecutableImage c) (tick : c.tick < 2)
    (pc : pcOf c = some 0x80000f7c#64)
    (base : gpr c 12 = some 0x80061f78#64)
    (data : gpr c 15 = some (putcWord b))
    (idle : c.σ.regs.get? Register.htif_payload_writes = some 0#4) :
    ∃ d, Step c d ∧ PutcharPost c b d := by
  obtain ⟨vm, hvm⟩ := good.minstret
  obtain ⟨th, hth⟩ := good.htif_tohost
  obtain ⟨b0, b1, b2, b3⟩ := Vsa.Sim.Code._write_at_80000f7c (loaded image)
  have prelude : ∀ R : Register, (Register.minstret_increment == R) = false →
      (afterPrelude c.σ).regs.get? R = c.σ.regs.get? R := get?_afterPrelude c.σ
  have dec := Vsa.Sim.ElfDecode.decode_04f63423 (afterPrelude c.σ)
    (by rw [prelude _ (by decide)]; exact good.misa)
    (by rw [prelude _ (by decide)]; exact good.cur_privilege)
    (by rw [prelude _ (by decide)]; exact good.mseccfg)
  obtain ⟨σ', i', step, tick', good', mem', out', pc', mins', idle', _, frame⟩ :=
    stepObs_tohost_putchar c.σ c.tick c.steps 0x80000f7c#64 vm 0x04f63423#32 72#12
      (regidx.Regidx 15#5) (regidx.Regidx 12#5) 0x80061f78#64 (putcWord b) (putcWord b) b th
      0x23#8 0x34#8 0xf6#8 0x04#8 good pc hvm (by decide) (by decide) dec
      (rX_src c.σ _ 12 (by decide) _ base) (rX_src c.σ _ 15 (by decide) _ data) (by decide) rfl idle hth rfl
      b0 b1 b2 b3 (by decide) (by decide) (by decide) tick
  refine ⟨⟨σ', i', c.steps + 1⟩, step, good', ?_, mins', tick', ?_, mem', output_push out', idle', ?_⟩
  · exact image_of_writeLog (log := []) image ⟨True.intro, True.intro⟩ mem'
  · change σ'.regs.get? Register.PC = _
    rw [pc']
    decide
  · intro n
    change gprGet σ' n = gprGet c.σ n
    unfold gprGet
    split <;> first
      | rfl
      | exact frame _ (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end OCaml.Vm.Primitives.ConsoleWrite
