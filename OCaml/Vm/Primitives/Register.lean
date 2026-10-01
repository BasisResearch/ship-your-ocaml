import OCaml.Vm.Primitives.Blocks
import OCaml.Vm.Platform
import OCaml.Vm.Primitives.ImageFrame

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- A primitive has an exact memory effect and may clobber the listed ABI temporaries. -/
structure EffectPost (writes : List Nat) (expectedMem : Std.ExtHashMap Nat (BitVec 8))
    (before : Config) (ra value : BitVec 64)
    (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  pc : pcOf after = some ra
  result : gpr after 10 = some value
  memory : after.σ.mem = expectedMem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ n ∈ writes, gprReg n ≠ r) →
    (∀ q ∈ noiseRegs, (q == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Exact memory effect of a generated write log. -/
abbrev WritePost (writes : List Nat) (log : List WEntry) (before : Config) (ra value : BitVec 64) :=
  EffectPost writes (writeLog before.σ.mem log) before ra value

/-- Preserve the existing read-only summary API. -/
abbrev RegisterPost (writes : List Nat) (before : Config) (ra value : BitVec 64) :=
  EffectPost writes before.σ.mem before ra value

/-- A finite write-set check protects the interpreter's dedicated registers. -/
def PreservesLoopRegisters (writes : List Nat) : Prop :=
  ∀ r ∈ [Layout.reg_dispatchTable, Layout.reg_opcodeBound, Layout.reg_pending, Layout.reg_domain],
    ∀ n ∈ writes, gprReg n ≠ gprReg r

theorem EffectPost.loop {writes expectedMem before ra value after}
    (post : EffectPost writes expectedMem before ra value after)
    (frame : PreservesLoopRegisters writes) (loop : LoopRegisters before) : LoopRegisters after := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (post.frame (gprReg Layout.reg_dispatchTable) (frame Layout.reg_dispatchTable (by simp)) (by decide)).trans loop.dispatchTable
  · exact (post.frame (gprReg Layout.reg_opcodeBound) (frame Layout.reg_opcodeBound (by simp)) (by decide)).trans loop.opcodeBound
  · exact (post.frame (gprReg Layout.reg_pending) (frame Layout.reg_pending (by simp)) (by decide)).trans loop.pending
  · exact (post.frame (gprReg Layout.reg_domain) (frame Layout.reg_domain (by simp)) (by decide)).trans loop.domain

/-- Package the segment kernel's complete frame for a callee with a write log.
The generated certificate proves its accesses and image separation. -/
theorem write_of_blocks {bs : List BBlock} {entry : BitVec 64} {before : Config}
    {L : GRegs} {loads : List (List (BitVec 8))} {writes : List Nat}
    {ra value : BitVec 64} (image : ExecutableImage before)
    {log : List WEntry} (outside : ImageOutside log)
    (S : FnSummary entry (fun c => c = before) (BlockPost bs entry L loads before))
    (hlog : (evalBlocks bs (SegEvalState.init L loads)).log = log)
    (hpc : evalBlocksPC entry (SegEvalState.init L loads) bs = ra)
    (hresult : ∀ σ, GHolds σ (evalBlocks bs (SegEvalState.init L loads)).regs →
      gprGet σ 10 = some value)
    (hwrites : ∀ n ∈ wrChain bs, n ∈ writes) :
    FnSummary entry (fun c => c = before) (WritePost writes log before ra value) := by
  apply S.weaken (fun _ h => h)
  intro after h
  have hm : after.σ.mem = writeLog before.σ.mem log := by simpa only [hlog] using h.memory
  refine ⟨h.good, image_of_writeLog image outside hm, h.minstret, h.tick, ?_, hresult _ h.regs, hm, h.output, ?_⟩
  · exact h.pc.trans (congrArg some hpc)
  · intro r hr hn
    apply h.frame r hn
    intro n hmem
    exact beq_eq_false_iff_ne.mpr (hr n (hwrites n hmem))

/-- Read-only packaging is the empty-log specialization. -/
theorem register_of_blocks {bs : List BBlock} {entry : BitVec 64} {before : Config}
    {L : GRegs} {loads : List (List (BitVec 8))} {writes : List Nat}
    {ra value : BitVec 64} (image : ExecutableImage before)
    (S : FnSummary entry (fun c => c = before) (BlockPost bs entry L loads before))
    (hlog : (evalBlocks bs (SegEvalState.init L loads)).log = [])
    (hpc : evalBlocksPC entry (SegEvalState.init L loads) bs = ra)
    (hresult : ∀ σ, GHolds σ (evalBlocks bs (SegEvalState.init L loads)).regs →
      gprGet σ 10 = some value)
    (hwrites : ∀ n ∈ wrChain bs, n ∈ writes) :
    FnSummary entry (fun c => c = before) (RegisterPost writes before ra value) := by
  exact write_of_blocks image (log := []) ⟨True.intro, True.intro⟩ S hlog hpc hresult hwrites

end OCaml.Vm.Primitives
