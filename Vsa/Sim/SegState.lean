import Vsa.Sim.RegPins

/-!
The generic `SegSt` boundary record from ship-your-interpreter,
`95ee5f98^:Vsa/Sim/SegState.lean`, with the unused SnprintfSpec18 import
and its example/transport cone cut. Consumed by `gen_segment.py`.
-/
namespace Vsa.Sim
open Vsa.Machine LeanRV64DExecutable

/-- Standard site-proof harness plus a named segment-specific payload. -/
structure SegSt (pcv : BitVec 64) (L : List Pin) (P : MState → Prop) (c : Config) : Prop where
  good : GoodState c.σ
  pcAt : c.σ.regs.get? Register.PC = some pcv
  pins : PinsHold c.σ L
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  extra : P c.σ

end Vsa.Sim
