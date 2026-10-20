import OCaml.Vm.Primitives.Uncaught.Sinit
import OCaml.Vm.Primitives.Uncaught.GlobalStdioInit
import OCaml.Vm.Primitives.Uncaught.RetargetLockInit
import OCaml.Vm.Primitives.Uncaught.StdioState
import OCaml.Vm.Boot.Startup.MemsetBytes
import OCaml.Vm.Boot.Startup.MemsetTail

/-!
# newlib's stdio initialization (`__sinit`)

On the first stdio call (`fprintf(stderr, …)` on the fatal path) `__sinit`
installs `cleanup_stdio` as `reent->__cleanup` and, with no
`__stdio_exit_handler` yet, runs `global_stdio_init`: `stdio_exit_handler`
installed, and stdin, stdout and stderr set up (flags, descriptor, cookie,
the four I/O functions, `_mbstate` cleared by `memset(…, 0, 8)`).
-/

namespace OCaml.Vm.Primitives.Uncaught.StdioInit
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives VsaIris.Inst
open OCaml.Vm.Boot.Startup (memsetBytesLog MemsetBytesInput memset_bytes memsetPrefix_code)

private theorem zero_imm : Functions.sign_extend (m := 64) 0#12 = 0#64 := by decide

local macro "memset8_nf" : tactic =>
  `(tactic| simp only [OCaml.Vm.Boot.Startup.memsetprefix_line_8004276c, OCaml.Vm.Boot.Startup.memsetprefix_line_80042770, OCaml.Vm.Boot.Startup.memsettail_line_800427a8,
    OCaml.Vm.Boot.Startup.memsettail_line_800427ac, OCaml.Vm.Boot.Startup.memsettail_line_800427b0, OCaml.Vm.Boot.Startup.memsettail_line_800427b4, memsetX276cTSeg, memsetX27a8Seg,
    evalBlocksPC, chainEndPC, endPCB, nextPC0, ldsRunM, evalBlocks, evalBlock, SegEvalState.init, List.cons_append, List.nil_append,
    runGM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, imm20Of, Option.getD_some, BitVec.add_zero,
    Nat.reduceEqDiff, ite_true, ite_false, tgtPCT, zero_imm])

/-- `memset(p, 0, 8)`'s entry and dispatch: `n < 16`, so a computed jump into
the byte-store ladder at its eighth entry. -/
theorem memset8_dispatch (c : Config) (p ra : BitVec 64) (h : LeafInput ra c)
    (a0 : gprGet c.σ 10 = some p) (a2 : gprGet c.σ 12 = some 8#64) :
    FnSummary 0x8004276c#64 (fun d => d = c)
      (BoundaryPost [5, 6, 13, 14] c ra 0x800427d8#64 [(14, p)]) := by
  have input : BlockInput (memsetX276cTSeg ++ memsetX27a8Seg) 0x8004276c#64 [(10, p), (12, 8#64)] [] c := {
    good := h.good
    minstret := h.minstret
    regs := ⟨a0, a2, trivial⟩
    keys := by change KeysOK [10, 12]; decide
    shape := by change ChainOK _ [10, 12] _; decide
    tick := h.tick
    facts := by
      have code := memsetPrefix_code h.image
      chain_facts code with "Vsa.Sim.Code.memset_at_"
      all_goals memset8_nf
      all_goals decide }
  apply boundary_of_blocks h (block_summary _ _ _ _ _ input)
  · rfl
  · memset8_nf; decide
  · intro σ pins
    exact ⟨gholds_lookup _ pins (by memset8_nf), trivial⟩
  · decide
  · decide

/-- **`memset(p, 0, 8)`**: the eight bytes at `p` cleared, `p` returned. -/
theorem memset8 (c : Config) (p ra : BitVec 64) (h : LeafInput ra c)
    (a0 : gprGet c.σ 10 = some p) (a1 : gprGet c.σ 11 = some 0#64) (a2 : gprGet c.σ 12 = some 8#64)
    (windows : ∀ i : Nat, i < 8 → WriteWindow (p + BitVec.ofNat 64 i) 1)
    (outside : ImageOutside (memsetBytesLog p)) :
    FnSummary 0x8004276c#64 (fun d => d = c)
      (EffectPost [5, 6, 13, 14] (writeLog c.σ.mem (memsetBytesLog p)) c ra p) := by
  apply summary_bind (memset8_dispatch c p ra h a0 a2) (fun _ q => q.pc)
  intro d q
  have input : MemsetBytesInput p p ra d :=
    { toLeafInput := q.toLeafInput
      destination := (q.frame .x10 (by decide) (by decide)).trans a0
      cursor := gholds_lookup _ q.regs rfl
      zero := (q.frame .x11 (by decide) (by decide)).trans a1
      windows := windows
      outside := outside }
  apply (memset_bytes d p p ra input).weaken (fun _ e => e)
  intro e post
  refine { post.toEffectPost with memory := ?_, output := ?_, frame := ?_, kept := q.kept.trans post.kept }
  · rw [post.memory, q.memory]
  · exact post.output.trans q.output
  · intro r out noise
    exact (post.frame r (by simp) noise).trans (q.frame r out noise)

end OCaml.Vm.Primitives.Uncaught.StdioInit
