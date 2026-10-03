import OCaml.Vm.Gc.ScanState

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Observable one-field progress shared by copying and relocating routes.
Concrete machine summaries supply the normalized branch and field value;
separation supplies the memory frame and the already scanned prefix. -/
structure ScanProgress (writes : List Nat) (a b count start i : Nat)
    (footprint : List W) (expected : Nat → BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_mopupLoaded after.σ.mem
  pc : PCAt (if i + 1 < count then pc else exitPc) after
  registers : GHolds after.σ (regs (scanPtr a (i + 1)) (BitVec.ofNat 64 b - BitVec.ofNat 64 a)
    (BitVec.ofNat 64 b) (BitVec.ofNat 64 (i + 1)))
  memory : FrameOn footprint before.σ.mem after.σ.mem
  destination : word after (b + 8 * i) = expected i
  previous : ∀ j, start ≤ j → j < i → word after (b + 8 * j) = word before (b + 8 * j)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ writes, (gprReg n == r) = false) →
      after.σ.regs.get? r = before.σ.regs.get? r

/-- Shared invariant update, independent of how the machine computes the
field word or which auxiliary storage its route writes. -/
theorem ScanAtWith.advance_progress {writes a b count start initial i c d footprint expected}
    (h : ScanAtWith writes a b count start initial i c footprint expected)
    (bound : i < count)
    (post : ScanProgress writes a b count start i footprint expected c d) :
    ScanAtWith writes a b count start initial (i + 1) d footprint expected := by
  refine ⟨post.good, post.minstret, post.tick, post.code,
    by have := h.lower; omega, by omega, post.pc, post.registers,
    (fun a ha => (post.memory a ha).trans (h.memory a ha)), ?_,
    post.output.trans h.output, ?_⟩
  · intro j lower upper
    by_cases current : j = i
    · subst j; exact post.destination
    · have old : j < i := by omega
      exact (post.previous j lower old).trans (h.copied j lower old)
  · intro r noise outside
    exact (post.native r noise outside).trans (h.native r noise outside)

end OCaml.Vm.Gc.FieldCopy
