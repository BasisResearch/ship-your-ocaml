import OCaml.Vm.Primitives.Memprof.UpdateYoungLimit
import OCaml.Vm.Primitives.Named.NamedChain

/-!
# `caml_update_young_limit` with no pending action

`Caml_state->young_limit = max(young_trigger, caml_memprof_young_trigger)`
(unsigned), and nothing more when `caml_something_to_do` is clear. The two
comparison outcomes (`triggerHigh`, `triggerLow` then `memprof`) meet at the
store (`idle`), then return.
-/

namespace OCaml.Vm.Primitives.Memprof.UpdateYoungLimit
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of wl_nil gprReg_ne_htif gpr_some)

/-- The new young limit: the larger of the two triggers. -/
def limitValue (trig memp : BitVec 64) : BitVec 64 := if memp.toNat ≤ trig.toNat then trig else memp

/-- **A call of `caml_update_young_limit`** with no pending action. -/
structure LimitInput (ra dom trig memp : BitVec 64) (c : Config) : Prop where
  leaf : LeafInput ra c
  pc : PCAt 0x8000d590#64 c
  a0 : (gprGet c.σ 10).isSome
  domain : bytesVal .ld (read8 c.σ.mem (2147896584#64).toNat) = dom
  trigger : bytesVal .ld (read8 c.σ.mem (dom + 72#64).toNat) = trig
  memprof : bytesVal .ld (read8 c.σ.mem (2147896520#64).toNat) = memp
  triggerWindow : ReadWindow (dom + 72#64) 8
  limitWindow : WriteWindow dom 8
  image : ImageOutside [(dom.toNat, 8, limitValue trig memp)]
  idle : bytesVal .lw (read8 c.σ.mem (2147896112#64).toNat) = 0#64

/-- **`caml_update_young_limit` returned**: `young_limit` written. -/
structure LimitPost (before : Config) (ra dom trig memp : BitVec 64) (after : Config) : Prop where
  leaf : LeafInput ra after
  pc : pcOf after = some ra
  memory : after.σ.mem = writeLog before.σ.mem [(dom.toNat, 8, limitValue trig memp)]
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [12, 13, 14, 15] → gprGet after.σ n = gprGet before.σ n
  htif : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes
  /-- every register that held a value still does, and `gp` is unchanged -/
  kept : GprsKept before after

/-- At the store: the chosen limit in `a5`, `Caml_state` in `a4`. -/
structure Chosen (before : Config) (ra dom trig memp : BitVec 64) (c : Config) : Prop where
  leaf : LeafInput ra c
  pc : PCAt 0x8000d5b0#64 c
  value : gprGet c.σ 15 = some (limitValue trig memp)
  domain : gprGet c.σ 14 = some dom
  state : gprGet c.σ 13 = some 2147896584#64
  a0 : (gprGet c.σ 10).isSome
  memory : c.σ.mem = before.σ.mem
  output : c.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [12, 13, 14, 15] → gprGet c.σ n = gprGet before.σ n
  htif : c.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes
  kept : GprsKept before c

theorem choose {c : Config} {ra dom trig memp : BitVec 64} (h : LimitInput ra dom trig memp c) :
    ∃ d, Steps c d ∧ Chosen c ra dom trig memp d := by
  have l0 : LeafInput (regsAt c 1) c := by rw [regsAt_of h.leaf.raReg]; exact h.leaf
  have regs0 : GHolds c.σ [(10, regsAt c 10)] := ⟨gpr_some h.a0, trivial⟩
  have w2 : ReadWindow ((bytesVal .ld (read8 c.σ.mem (2147896584#64).toNat)) + 72#64) 8 := by
    rw [h.domain]; exact h.triggerWindow
  by_cases high : memp.toNat ≤ trig.toNat
  · obtain ⟨d, run, p⟩ := (triggerHigh_fast c (regsAt c) l0 regs0 w2 (by
        simp only [triggerHigh_loads, List.getD_cons_zero, List.getD_cons_succ, h.domain, h.trigger, h.memprof]
        simp [guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt, high])).run c ⟨h.pc, rfl⟩
    have o := p.regs
    simp only [triggerHigh_regs, triggerHigh_loads, List.getD_cons_zero, List.getD_cons_succ, h.domain, h.trigger,
      h.memprof, GHolds] at o
    obtain ⟨o15, -, o14, o13, o10, -⟩ := o
    refine ⟨d, run, ⟨p.good, p.image, p.minstret, (p.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans
      h.leaf.raReg, h.leaf.aligned, p.tick⟩, p.pc, by rw [o15]; simp [limitValue, high], o14, o13,
      Named.NamedValue.gpr_some_of o10, by rw [p.memory, wl_nil], p.output,
      fun n lo hi out => p.gpr_frame (by decide) n lo hi out,
      p.frame _ (fun n _ => gprReg_ne_htif n) (by decide), p.kept⟩
  · obtain ⟨d1, run1, p1⟩ := (triggerLow_fast c (regsAt c) l0 regs0 w2 (by
        simp only [triggerLow_loads, List.getD_cons_zero, List.getD_cons_succ, h.domain, h.trigger, h.memprof]
        simp [guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt, high])).run c ⟨h.pc, rfl⟩
    have o1 := p1.regs
    simp only [triggerLow_regs, triggerLow_loads, List.getD_cons_zero, List.getD_cons_succ, h.domain, h.trigger,
      h.memprof, GHolds] at o1
    obtain ⟨-, q12, q14, q13, q10, -⟩ := o1
    have leaf1 : LeafInput ra d1 := ⟨p1.good, p1.image, p1.minstret,
      (p1.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans h.leaf.raReg, h.leaf.aligned, p1.tick⟩
    have l1 : LeafInput (regsAt d1 1) d1 := by rw [regsAt_of leaf1.raReg]; exact leaf1
    obtain ⟨d2, run2, p2⟩ := (memprof_fast d1 (regsAt d1) l1 (by
        simp only [memprof_input, GHolds, regsAt_of q10, regsAt_of q12]
        exact ⟨q10, q12, trivial⟩)).run d1 ⟨p1.pc, rfl⟩
    have o2 := p2.regs
    simp only [memprof_regs, regsAt_of q12, GHolds] at o2
    obtain ⟨m15, m10, -, -⟩ := o2
    have k2 : ∀ n, n ≠ 15 → 1 ≤ n → n ≤ 31 → gprGet d2.σ n = gprGet d1.σ n :=
      fun n ne lo hi => p2.gpr_frame (by decide) n lo hi (by simpa using ne)
    refine ⟨d2, run1.trans run2, ⟨p2.good, p2.image, p2.minstret,
      (k2 1 (by decide) (by decide) (by decide)).trans leaf1.raReg, h.leaf.aligned, p2.tick⟩, p2.pc,
      by rw [m15]; simp [limitValue, high], (k2 14 (by decide) (by decide) (by decide)).trans q14,
      (k2 13 (by decide) (by decide) (by decide)).trans q13, Named.NamedValue.gpr_some_of m10,
      by rw [p2.memory, wl_nil, p1.memory, wl_nil], by rw [p2.output, p1.output],
      fun n lo hi out => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
        exact (k2 n out.2.2.2 lo hi).trans (p1.gpr_frame (by decide) n lo hi (by simp; omega)),
      by rw [p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide), p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide)],
      p1.kept.trans p2.kept⟩

/-- **`caml_update_young_limit` with no pending action.** -/
theorem update_young_limit {c : Config} {ra dom trig memp : BitVec 64} (h : LimitInput ra dom trig memp c) :
    ∃ d, Steps c d ∧ LimitPost c ra dom trig memp d := by
  obtain ⟨c1, run1, p1⟩ := choose h
  have l1 : LeafInput (regsAt c1 1) c1 := by rw [regsAt_of p1.leaf.raReg]; exact p1.leaf
  have r14 := regsAt_of p1.domain
  have r15 := regsAt_of p1.value
  have logEq : idleLog (regsAt c1) (idle_loads c1.σ.mem (regsAt c1)) = [(dom.toNat, 8, limitValue trig memp)] := by
    simp only [idleLog, r14, r15]
  obtain ⟨c2, run2, p2⟩ := (idle_fast c1 (regsAt c1) l1 (by
      simp only [idle_input, GHolds, regsAt_of p1.state, r14, r15]
      exact ⟨gpr_some p1.a0, p1.state, p1.domain, p1.value, trivial⟩)
    (by rw [r14]; exact h.limitWindow) (by rw [logEq]; exact h.image)
    (by simp only [idle_loads, List.getD_cons_zero, p1.memory, h.idle]; decide)).run c1 ⟨p1.pc, rfl⟩
  have k2 : ∀ n, n ≠ 12 → 1 ≤ n → n ≤ 31 → gprGet c2.σ n = gprGet c1.σ n :=
    fun n ne lo hi => p2.gpr_frame (by decide) n lo hi (by simpa using ne)
  have leaf2 : LeafInput ra c2 := ⟨p2.good, p2.image, p2.minstret,
    (k2 1 (by decide) (by decide) (by decide)).trans p1.leaf.raReg, h.leaf.aligned, p2.tick⟩
  have l2 : LeafInput (regsAt c2 1) c2 := by rw [regsAt_of leaf2.raReg]; exact leaf2
  have a10 := (k2 10 (by decide) (by decide) (by decide)).trans (gpr_some p1.a0)
  obtain ⟨c3, run3, p3⟩ := (done_fast c2 (regsAt c2) l2 (by
      simp only [done_input, GHolds, regsAt_of leaf2.raReg, regsAt_of a10]
      exact ⟨leaf2.raReg, a10, trivial⟩)).run c2 ⟨p2.pc, rfl⟩
  have k3 : ∀ n, 1 ≤ n → n ≤ 31 → gprGet c3.σ n = gprGet c2.σ n :=
    fun n lo hi => p3.gpr_frame (by decide) n lo hi (by simp)
  refine ⟨c3, run1.trans (run2.trans run3), ⟨p3.good, p3.image, p3.minstret,
    (k3 1 (by decide) (by decide)).trans leaf2.raReg, h.leaf.aligned, p3.tick⟩, by rw [p3.pc, regsAt_of leaf2.raReg],
    by rw [p3.memory, wl_nil, p2.memory, logEq, p1.memory], by rw [p3.output, p2.output, p1.output],
    fun n lo hi out => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
      rw [k3 n lo hi, k2 n out.1 lo hi]
      exact p1.frame n lo hi (by simp; omega),
    by rw [p3.frame _ (fun n _ => gprReg_ne_htif n) (by decide), p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide),
      p1.htif], p1.kept.trans (p2.kept.trans p3.kept)⟩

end OCaml.Vm.Primitives.Memprof.UpdateYoungLimit
