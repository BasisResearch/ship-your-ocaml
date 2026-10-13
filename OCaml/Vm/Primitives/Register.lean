import OCaml.Vm.Primitives.Blocks
import OCaml.Vm.Primitives.BlockGprs
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
  /-- every register that held a value still does, and `gp` is unchanged -/
  kept : GprsKept before after

/-- Exact memory effect of a generated write log. -/
abbrev WritePost (writes : List Nat) (log : List WEntry) (before : Config) (ra value : BitVec 64) :=
  EffectPost writes (writeLog before.σ.mem log) before ra value

/-- Preserve the existing read-only summary API. -/
abbrev RegisterPost (writes : List Nat) (before : Config) (ra value : BitVec 64) :=
  EffectPost writes before.σ.mem before ra value

/-- A finite write-set check protects the interpreter's dedicated registers. -/
def PreservesLoopRegisters (writes : List Nat) : Prop :=
  ∀ r ∈ [Layout.reg_dispatchTable, Layout.reg_opcodeBound, Layout.reg_pending, Layout.reg_domain,
      3],
    ∀ n ∈ writes, gprReg n ≠ gprReg r

/-- No GPR is the HTIF payload counter. -/
theorem gprReg_ne_htif (n : Nat) : gprReg n ≠ Register.htif_payload_writes := by
  by_cases small : n < 32
  · have : ∀ n, n < 32 → gprReg n ≠ Register.htif_payload_writes := by decide
    exact this n small
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 32 := ⟨n - 32, by omega⟩
    show Register.x1 ≠ _
    decide

theorem EffectPost.loop {writes expectedMem before ra value after}
    (post : EffectPost writes expectedMem before ra value after)
    (frame : PreservesLoopRegisters writes) (loop : LoopRegisters before) : LoopRegisters after := by
  refine ⟨?_, ?_, ?_, ?_, ?_,
    ⟨fun n lo hi => post.kept.present n lo (by omega) (loop.gprs.get n lo hi)⟩, ?_⟩
  · exact (post.frame (gprReg Layout.reg_dispatchTable) (frame Layout.reg_dispatchTable (by simp)) (by decide)).trans loop.dispatchTable
  · exact (post.frame (gprReg Layout.reg_opcodeBound) (frame Layout.reg_opcodeBound (by simp)) (by decide)).trans loop.opcodeBound
  · exact (post.frame (gprReg Layout.reg_pending) (frame Layout.reg_pending (by simp)) (by decide)).trans loop.pending
  · exact (post.frame (gprReg Layout.reg_domain) (frame Layout.reg_domain (by simp)) (by decide)).trans loop.domain
  · exact (post.frame Register.htif_payload_writes (fun n _ => gprReg_ne_htif n) (by decide)).trans loop.htifIdle
  · exact (post.frame (gprReg 3) (frame 3 (by simp)) (by decide)).trans loop.gp

/-- Package the segment kernel's complete frame for a callee with a write log.
The generated certificate proves its accesses and image separation. -/
theorem BlockPost.effect {bs : List BBlock} {entry : BitVec 64} {before after : Config}
    {L : GRegs} {loads : List (List (BitVec 8))} {writes : List Nat}
    {ra value : BitVec 64} (image : ExecutableImage before)
    {log : List WEntry} (outside : ImageOutside log)
    (h : BlockPost bs entry L loads before after)
    (hlog : (evalBlocks bs (SegEvalState.init L loads)).log = log)
    (hpc : evalBlocksPC entry (SegEvalState.init L loads) bs = ra)
    (hresult : ∀ σ, GHolds σ (evalBlocks bs (SegEvalState.init L loads)).regs →
      gprGet σ 10 = some value)
    (hwrites : ∀ n ∈ wrChain bs, n ∈ writes)
    (keys : KeysOK (wrChain bs) := by first | decide | exact of_decide_eq_true rfl)
    (no3 : 3 ∉ wrChain bs := by first | decide | exact of_decide_eq_true rfl) :
    WritePost writes log before ra value after := by
  have hm : after.σ.mem = writeLog before.σ.mem log := by simpa only [hlog] using h.memory
  refine ⟨h.good, image_of_writeLog image outside hm, h.minstret, h.tick, ?_, hresult _ h.regs, hm, h.output, ?_,
    h.kept keys no3⟩
  · exact h.pc.trans (congrArg some hpc)
  · intro r hr hn
    apply h.frame r hn
    intro n hmem
    exact beq_eq_false_iff_ne.mpr (hr n (hwrites n hmem))


theorem write_of_blocks {bs : List BBlock} {entry : BitVec 64} {before : Config}
    {L : GRegs} {loads : List (List (BitVec 8))} {writes : List Nat}
    {ra value : BitVec 64} (image : ExecutableImage before)
    {log : List WEntry} (outside : ImageOutside log)
    (S : FnSummary entry (fun c => c = before) (BlockPost bs entry L loads before))
    (hlog : (evalBlocks bs (SegEvalState.init L loads)).log = log)
    (hpc : evalBlocksPC entry (SegEvalState.init L loads) bs = ra)
    (hresult : ∀ σ, GHolds σ (evalBlocks bs (SegEvalState.init L loads)).regs →
      gprGet σ 10 = some value)
    (hwrites : ∀ n ∈ wrChain bs, n ∈ writes)
    (keys : KeysOK (wrChain bs) := by first | decide | exact of_decide_eq_true rfl)
    (no3 : 3 ∉ wrChain bs := by first | decide | exact of_decide_eq_true rfl) :
    FnSummary entry (fun c => c = before) (WritePost writes log before ra value) := by
  exact S.weaken (fun _ h => h) (fun _ h => h.effect image outside hlog hpc hresult hwrites keys no3)

/-- Read-only packaging is the empty-log specialization. -/
theorem register_of_blocks {bs : List BBlock} {entry : BitVec 64} {before : Config}
    {L : GRegs} {loads : List (List (BitVec 8))} {writes : List Nat}
    {ra value : BitVec 64} (image : ExecutableImage before)
    (S : FnSummary entry (fun c => c = before) (BlockPost bs entry L loads before))
    (hlog : (evalBlocks bs (SegEvalState.init L loads)).log = [])
    (hpc : evalBlocksPC entry (SegEvalState.init L loads) bs = ra)
    (hresult : ∀ σ, GHolds σ (evalBlocks bs (SegEvalState.init L loads)).regs →
      gprGet σ 10 = some value)
    (hwrites : ∀ n ∈ wrChain bs, n ∈ writes)
    (keys : KeysOK (wrChain bs) := by first | decide | exact of_decide_eq_true rfl)
    (no3 : 3 ∉ wrChain bs := by first | decide | exact of_decide_eq_true rfl) :
    FnSummary entry (fun c => c = before) (RegisterPost writes before ra value) := by
  exact write_of_blocks image (log := []) ⟨True.intro, True.intro⟩ S hlog hpc hresult hwrites keys no3

end OCaml.Vm.Primitives
