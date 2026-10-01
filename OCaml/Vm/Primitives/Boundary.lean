import OCaml.Vm.Primitives.Leaf

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- Select an interface register list from a generated symbolic register state. -/
theorem holds_select {σ : MState} {source target : GRegs} (h : GHolds σ source)
    (select : ∀ n v, (n, v) ∈ target → lookupG n source = some v) : GHolds σ target := by
  induction target with
  | nil => trivial
  | cons pair rest ih =>
    obtain ⟨n, v⟩ := pair
    exact ⟨gholds_lookup source h (select n v (by simp)),
      ih (fun n v hm => select n v (by simp [hm]))⟩

/-- Read-only CFG boundaries preserve the caller's return address and a common
frame. Generated blocks supply their exact outgoing register interface. -/
structure BoundaryPost (writes : List Nat) (before : Config) (ra pc : BitVec 64)
    (regs : GRegs) (after : Config) : Prop extends LeafInput ra after where
  pc : pcOf after = some pc
  regs : GHolds after.σ regs
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ n ∈ writes, gprReg n ≠ r) →
    (∀ q ∈ noiseRegs, (q == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

/-- One packaging rule for every generated read-only CFG block. -/
theorem boundary_of_blocks {bs entry before L loads writes ra pc regs}
    (h : LeafInput ra before)
    (S : FnSummary entry (fun c => c = before) (BlockPost bs entry L loads before))
    (hlog : (evalBlocks bs (SegEvalState.init L loads)).log = [])
    (hpc : evalBlocksPC entry (SegEvalState.init L loads) bs = pc)
    (hregs : ∀ σ, GHolds σ (evalBlocks bs (SegEvalState.init L loads)).regs → GHolds σ regs)
    (hwrites : ∀ n ∈ wrChain bs, n ∈ writes)
    (hra : ∀ n ∈ writes, gprReg n ≠ gprReg 1) :
    FnSummary entry (fun c => c = before) (BoundaryPost writes before ra pc regs) := by
  apply S.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = before.σ.mem := by simpa only [hlog, writeLog, List.foldl_nil] using post.memory
  have frame : ∀ r : Register, (∀ n ∈ writes, gprReg n ≠ r) →
      (∀ q ∈ noiseRegs, (q == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r := by
    intro r hr hn
    exact post.frame r hn (fun n hm => beq_eq_false_iff_ne.mpr (hr n (hwrites n hm)))
  refine {
    toLeafInput := ⟨post.good, ?_, post.minstret, ?_, h.aligned, post.tick⟩
    pc := post.pc.trans (congrArg some hpc)
    regs := hregs _ post.regs
    memory := memory
    output := post.output
    frame := frame }
  · exact ⟨fun i hi => by rw [memory]; exact h.image.text i hi,
      fun i hi => by rw [memory]; exact h.image.rodata i hi⟩
  · exact (frame _ hra (by decide)).trans h.raReg

/-- Compose frames at CFG joins without tracking individual unchanged registers. -/
theorem BoundaryPost.then {writes before mid after ra pc pc' regs regs'}
    (h : BoundaryPost writes before ra pc regs mid)
    (h' : BoundaryPost writes mid ra pc' regs' after) :
    BoundaryPost writes before ra pc' regs' after :=
  { h' with
    memory := h'.memory.trans h.memory
    output := h'.output.trans h.output
    frame := fun r hr hn => (h'.frame r hr hn).trans (h.frame r hr hn) }

theorem BoundaryPost.finish {writes before after ra regs value}
    (h : BoundaryPost writes before ra ra regs after)
    (result : lookupG 10 regs = some value) : RegisterPost writes before ra value after :=
  ⟨h.good, h.image, h.minstret, h.tick, h.pc, gholds_lookup _ h.regs result,
    h.memory, h.output, h.frame⟩

/-- Forget surplus symbolic registers at a join. -/
theorem BoundaryPost.select {writes before after ra pc source target}
    (h : BoundaryPost writes before ra pc source after)
    (select : ∀ n v, (n, v) ∈ target → lookupG n source = some v) :
    BoundaryPost writes before ra pc target after :=
  { h with regs := holds_select h.regs select }

/-- Instantiate the next summary at the state reached by a preceding summary. -/
theorem summary_bind {entry pc pre post Q}
    (S : FnSummary entry pre post) (parked : ∀ c, post c → PCAt pc c)
    (next : ∀ c, post c → FnSummary pc (fun d => d = c) Q) : FnSummary entry pre Q := by
  constructor
  apply Vsa.Logic.Triple.seq S.run
  intro c h
  exact (next c h).run c ⟨parked c h, rfl⟩

/-- A dependent sequence of generated summaries uses the standard triple rule. -/
theorem boundary_bind {entry pre writes before ra pc regs Q}
    (S : FnSummary entry pre (BoundaryPost writes before ra pc regs))
    (next : ∀ c, BoundaryPost writes before ra pc regs c →
      FnSummary pc (fun d => d = c) Q) : FnSummary entry pre Q :=
  summary_bind S (fun _ h => h.pc) next

/-- A finite lookup certificate selects register interfaces without positional
conjunct projections or a separate proof for each register. -/
theorem holds_project {σ : MState} {source target : GRegs} (h : GHolds σ source)
    (select : target.all (fun p => lookupG p.1 source == some p.2) = true) : GHolds σ target := by
  apply holds_select h
  intro n v hm
  exact beq_iff_eq.mp ((List.all_eq_true.mp select) (n, v) hm)

theorem BoundaryPost.project {writes before after ra pc source target}
    (h : BoundaryPost writes before ra pc source after)
    (select : target.all (fun p => lookupG p.1 source == some p.2) = true) :
    BoundaryPost writes before ra pc target after :=
  { h with regs := holds_project h.regs select }

end OCaml.Vm.Primitives
