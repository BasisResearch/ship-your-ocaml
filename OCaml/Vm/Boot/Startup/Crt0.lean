import OCaml.Vm.Boot.Startup.Crt0Rows
import OCaml.Vm.Primitives.Blocks
import OCaml.Vm.Primitives.Control
import OCaml.Vm.Primitives.Write
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.DeriveLoop

/-! Reusable crt0 summaries. The machine runs come from generated segments;
loop composition uses `loopFromBody`, independently of the BSS length. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

/-- Control and code hypotheses shared by startup blocks. -/
structure CrtReady (c : Config) : Prop where
  good : GoodState c.σ
  code : Code._startLoaded c.σ.mem
  tick : c.tick < 2

theorem setup_input {c : Config} (h : CrtReady c) :
    BlockInput startX0000Seg 0x80000000#64 startX0000L [] c where
  good := h.good
  minstret := h.good.minstret
  regs := True.intro
  keys := by decide
  shape := by decide
  tick := h.tick
  facts := by
    chain_facts h.code with "Vsa.Sim.Code._start_at_"

theorem setup_summary (c : Config) (h : CrtReady c) :
    FnSummary 0x80000000#64 (fun d => d = c)
      (BlockPost startX0000Seg 0x80000000#64 startX0000L [] c) :=
  block_summary _ _ _ _ _ (setup_input h)

/-- One word-store body, parameterized by the cursor and its RAM window. -/
theorem clear_input {c : Config} {p : BitVec 64} (h : CrtReady c)
    (hp : gprGet c.σ 5 = some p) (window : WriteWindow p 8) :
    BlockInput startX0024Seg 0x80000024#64 (startX0024L p) [] c where
  good := h.good
  minstret := h.good.minstret
  regs := ⟨hp, True.intro⟩
  keys := by show KeysOK [5]; decide
  shape := by show ChainOK 0x80000024#64 [5] startX0024Seg; decide
  tick := h.tick
  facts := by
    chain_facts h.code with "Vsa.Sim.Code._start_at_"
    exact window.sd rfl (by change p + 0#64 = p; exact BitVec.add_zero p)

/-- The body records precisely one zero-word store and advances the cursor. -/
theorem clear_summary (c : Config) (p : BitVec 64) (h : CrtReady c)
    (hp : gprGet c.σ 5 = some p) (window : WriteWindow p 8) :
    FnSummary 0x80000024#64 (fun d => d = c)
      (BlockPost startX0024Seg 0x80000024#64 (startX0024L p) [] c) :=
  block_summary _ _ _ _ _ (clear_input h hp window)

/-- The cursor update is a small symbolic reflection fact, not a machine replay. -/
theorem clear_log (p : BitVec 64) :
    (evalBlocks startX0024Seg (SegEvalState.init (startX0024L p) [])).log =
      [(p.toNat, 8, 0#64)] := by
  change [((p + 0#64).toNat, 8, 0#64)] = _
  rw [BitVec.add_zero]

theorem clear_regs (p : BitVec 64) :
    (evalBlocks startX0024Seg (SegEvalState.init (startX0024L p) [])).regs =
      [(5, p + 8#64)] := by
  rfl

structure ClearBodyPost (p : BitVec 64) (before after : Config) : Prop where
  ready : CrtReady after
  memory : after.σ.mem = writeLog before.σ.mem [(p.toNat, 8, 0#64)]
  pc : PCAt 0x80000020#64 after
  cursor : gprGet after.σ 5 = some (p + 8#64)
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    r ≠ .x5 → after.σ.regs.get? r = before.σ.regs.get? r

theorem clear_body (c : Config) (p : BitVec 64) (h : CrtReady c)
    (hp : gprGet c.σ 5 = some p) (window : WriteWindow p 8)
    (above : 0x80000040 ≤ p.toNat) :
    FnSummary 0x80000024#64 (fun d => d = c) (ClearBodyPost p c) := by
  apply (clear_summary c p h hp window).weaken (fun _ hc => hc)
  intro d post
  have hm := post.memory
  rw [clear_log] at hm
  have code : Code._startLoaded d.σ.mem := Code._start_transport h.code (by
    intro a ha hb
    rw [hm, writeLog_out _ _ _ (show OutL [(p.toNat, 8, 0#64)] a from
      ⟨Or.inl (by omega), True.intro⟩)])
  have regs := post.regs
  rw [clear_regs] at regs
  refine ⟨⟨post.good, code, post.tick⟩, hm, post.pc, regs.1, post.output, ?_⟩
  intro r noise other
  apply post.frame r noise
  change ∀ n ∈ [5], (gprReg n == r) = false
  intro n hn
  have : n = 5 := List.mem_singleton.mp hn
  subst n
  simpa only [gprReg, beq_eq_false_iff_ne] using Ne.symm other

def guardSeg (taken : Bool) : List BBlock :=
  if taken then startX0020TSeg else startX0020FSeg

structure GuardPost (taken : Bool) (before after : Config) : Prop where
  ready : CrtReady after
  memory : after.σ.mem = before.σ.mem
  pc : PCAt (if taken then 0x80000030#64 else 0x80000024#64) after
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

theorem guard_input {c : Config} {p e : BitVec 64} {taken : Bool}
    (h : CrtReady c) (hp : gprGet c.σ 5 = some p) (he : gprGet c.σ 6 = some e)
    (branch : guardB .BGEU p e = taken) :
    BlockInput (guardSeg taken) 0x80000020#64 (startX0020TL p e) [] c where
  good := h.good
  minstret := h.good.minstret
  regs := ⟨hp, he, True.intro⟩
  keys := by show KeysOK [5, 6]; decide
  shape := by
    change ChainOK 0x80000020#64 [5, 6] (guardSeg taken)
    cases taken <;> decide
  tick := h.tick
  facts := by
    cases taken <;> chain_facts h.code with "Vsa.Sim.Code._start_at_"
    all_goals exact branch

theorem guard_summary (c : Config) (p e : BitVec 64) (taken : Bool)
    (h : CrtReady c) (hp : gprGet c.σ 5 = some p) (he : gprGet c.σ 6 = some e)
    (branch : guardB .BGEU p e = taken) :
    FnSummary 0x80000020#64 (fun d => d = c) (GuardPost taken c) := by
  apply (block_summary _ _ _ _ _ (guard_input h hp he branch)).weaken (fun _ hc => hc)
  intro d post
  have empty : (evalBlocks (guardSeg taken)
      (SegEvalState.init (startX0020TL p e) [])).log = [] := by cases taken <;> rfl
  have hm := post.memory
  rw [empty] at hm
  change d.σ.mem = c.σ.mem at hm
  refine ⟨⟨post.good, ?_, post.tick⟩, hm, ?_, post.output, ?_⟩
  · rw [hm]; exact h.code
  · have pc := post.pc
    cases taken <;> exact pc
  · intro r noise
    apply post.frame r noise
    cases taken <;> simp [guardSeg, startX0020TSeg, startX0020FSeg, wrChain, wrRegsM]

end OCaml.Vm.Boot.Startup


