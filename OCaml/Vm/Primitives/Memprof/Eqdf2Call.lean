import OCaml.Vm.Primitives.Memprof.Eqdf2
import OCaml.Vm.Primitives.Named.NamedChain

/-!
# `__eqdf2` on two zeros

libgcc's `__eqdf2(a, b)` returns 0 for equal doubles. On `+0.0 == +0.0`
(both words zero) the path is: neither is a NaN (`unpack`, `rhs`), the
exponents, mantissas and signs agree (`exps`, `mants`, `signs`), return 0.
-/

namespace OCaml.Vm.Primitives.Memprof.Eqdf2
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of wl_nil)

/-- **`__eqdf2` returned 0**: at the caller's return address, memory and
output kept, the integer registers outside `a0`–`a7` kept. -/
structure EqZeroPost (before : Config) (ra : BitVec 64) (after : Config) : Prop where
  leaf : LeafInput ra after
  pc : pcOf after = some ra
  result : gprGet after.σ 10 = some 0#64
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [10, 11, 12, 13, 14, 15, 16, 17] → gprGet after.σ n = gprGet before.σ n
  htif : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes

/-- **`__eqdf2(+0.0, +0.0) = 0`.** -/
theorem eqdf2_zero {c : Config} {ra : BitVec 64} (leaf : LeafInput ra c) (pc : PCAt 0x80034740#64 c)
    (a : gprGet c.σ 10 = some 0#64) (b : gprGet c.σ 11 = some 0#64) :
    ∃ d, Steps c d ∧ EqZeroPost c ra d := by
  have r1 := regsAt_of leaf.raReg
  have r10 := regsAt_of a
  have r11 := regsAt_of b
  have l0 : LeafInput (regsAt c 1) c := by rw [r1]; exact leaf
  obtain ⟨c1, run1, p1⟩ := (unpack_fast c (regsAt c) l0 (by simp only [unpack_input, GHolds, r10, r11]; exact ⟨a, b, trivial⟩)
    (by rw [r10]; decide)).run c ⟨pc, rfl⟩
  have o1 := p1.regs
  simp only [unpack_regs, r10, r11, GHolds] at o1
  obtain ⟨g11, g15, g14, g16, g12, -, g13, g10, -⟩ := o1
  have k1 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [10, 11, 12, 13, 14, 15, 16, 17] → gprGet c1.σ n = gprGet c.σ n :=
    fun n lo hi out => p1.gpr_frame (by decide) n lo hi (by simp at out ⊢; omega)
  have leaf1 : LeafInput ra c1 :=
    ⟨p1.good, p1.image, p1.minstret, (k1 1 (by decide) (by decide) (by decide)).trans leaf.raReg, leaf.aligned, p1.tick⟩
  have l1 : LeafInput (regsAt c1 1) c1 := by rw [regsAt_of leaf1.raReg]; exact leaf1
  have z12 : (0#64 >>> 52 &&& 2047#64 : BitVec 64) = 0#64 := by decide
  rw [z12] at g12 g13
  obtain ⟨c2, run2, p2⟩ := (rhs_fast c1 (regsAt c1) l1 (by
      simp only [rhs_input, GHolds, regsAt_of g10, regsAt_of g12]; exact ⟨g10, g12, trivial⟩)
    (by rw [regsAt_of g12]; decide)).run c1 ⟨p1.pc, rfl⟩
  have k2 : ∀ n, n ≠ 10 → 1 ≤ n → n ≤ 31 → gprGet c2.σ n = gprGet c1.σ n :=
    fun n ne lo hi => p2.gpr_frame (by decide) n lo hi (by simpa using ne)
  have o2 := p2.regs
  simp only [rhs_regs, regsAt_of g12, GHolds] at o2
  have leaf2 : LeafInput ra c2 :=
    ⟨p2.good, p2.image, p2.minstret, (k2 1 (by decide) (by decide) (by decide)).trans leaf1.raReg, leaf.aligned, p2.tick⟩
  have l2 : LeafInput (regsAt c2 1) c2 := by rw [regsAt_of leaf2.raReg]; exact leaf2
  have h12 := (k2 12 (by decide) (by decide) (by decide)).trans g12
  have h13 := (k2 13 (by decide) (by decide) (by decide)).trans g13
  obtain ⟨c3, run3, p3⟩ := (exps_fast c2 (regsAt c2) l2 (by
      simp only [exps_input, GHolds, regsAt_of o2.1, regsAt_of h12, regsAt_of h13]; exact ⟨o2.1, h12, h13, trivial⟩)
    (by rw [regsAt_of h12, regsAt_of h13]; decide)).run c2 ⟨p2.pc, rfl⟩
  have k3 : ∀ n, 1 ≤ n → n ≤ 31 → gprGet c3.σ n = gprGet c2.σ n :=
    fun n lo hi => p3.gpr_frame (by decide) n lo hi (by simp)
  have leaf3 : LeafInput ra c3 :=
    ⟨p3.good, p3.image, p3.minstret, (k3 1 (by decide) (by decide)).trans leaf2.raReg, leaf.aligned, p3.tick⟩
  have l3 : LeafInput (regsAt c3 1) c3 := by rw [regsAt_of leaf3.raReg]; exact leaf3
  have i10 := (k3 10 (by decide) (by decide)).trans o2.1
  have i15 := (k3 15 (by decide) (by decide)).trans ((k2 15 (by decide) (by decide) (by decide)).trans g15)
  have i16 := (k3 16 (by decide) (by decide)).trans ((k2 16 (by decide) (by decide) (by decide)).trans g16)
  obtain ⟨c4, run4, p4⟩ := (mants_fast c3 (regsAt c3) l3 (by
      simp only [mants_input, GHolds, regsAt_of i10, regsAt_of i15, regsAt_of i16]; exact ⟨i10, i15, i16, trivial⟩)
    (by rw [regsAt_of i15, regsAt_of i16]; decide)).run c3 ⟨p3.pc, rfl⟩
  have k4 : ∀ n, 1 ≤ n → n ≤ 31 → gprGet c4.σ n = gprGet c3.σ n :=
    fun n lo hi => p4.gpr_frame (by decide) n lo hi (by simp)
  have leaf4 : LeafInput ra c4 :=
    ⟨p4.good, p4.image, p4.minstret, (k4 1 (by decide) (by decide)).trans leaf3.raReg, leaf.aligned, p4.tick⟩
  have l4 : LeafInput (regsAt c4 1) c4 := by rw [regsAt_of leaf4.raReg]; exact leaf4
  have j11 := (k4 11 (by decide) (by decide)).trans ((k3 11 (by decide) (by decide)).trans
    ((k2 11 (by decide) (by decide) (by decide)).trans g11))
  have j14 := (k4 14 (by decide) (by decide)).trans ((k3 14 (by decide) (by decide)).trans
    ((k2 14 (by decide) (by decide) (by decide)).trans g14))
  obtain ⟨c5, run5, p5⟩ := (signs_fast c4 (regsAt c4) l4 (by
      simp only [signs_input, GHolds, regsAt_of j11, regsAt_of j14]; exact ⟨j11, j14, trivial⟩)
    (by rw [regsAt_of j11, regsAt_of j14]; decide)).run c4 ⟨p4.pc, rfl⟩
  have k5 : ∀ n, n ≠ 10 → 1 ≤ n → n ≤ 31 → gprGet c5.σ n = gprGet c4.σ n :=
    fun n ne lo hi => p5.gpr_frame (by decide) n lo hi (by simpa using ne)
  have o5 := p5.regs
  simp only [signs_regs, GHolds] at o5
  have leaf5 : LeafInput ra c5 :=
    ⟨p5.good, p5.image, p5.minstret, (k5 1 (by decide) (by decide) (by decide)).trans leaf4.raReg, leaf.aligned, p5.tick⟩
  have l5 : LeafInput (regsAt c5 1) c5 := by rw [regsAt_of leaf5.raReg]; exact leaf5
  obtain ⟨c6, run6, p6⟩ := (ret_fast c5 (regsAt c5) l5 (by
      simp only [ret_input, GHolds, regsAt_of leaf5.raReg, regsAt_of o5.1]; exact ⟨leaf5.raReg, o5.1, trivial⟩)).run c5
    ⟨p5.pc, rfl⟩
  have k6 : ∀ n, 1 ≤ n → n ≤ 31 → gprGet c6.σ n = gprGet c5.σ n :=
    fun n lo hi => p6.gpr_frame (by decide) n lo hi (by simp)
  refine ⟨c6, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))), ?_⟩
  exact
    { leaf := ⟨p6.good, p6.image, p6.minstret, (k6 1 (by decide) (by decide)).trans leaf5.raReg, leaf.aligned, p6.tick⟩
      pc := by rw [p6.pc, regsAt_of leaf5.raReg]
      result := (k6 10 (by decide) (by decide)).trans o5.1
      memory := by rw [p6.memory, wl_nil, p5.memory, wl_nil, p4.memory, wl_nil, p3.memory, wl_nil, p2.memory, wl_nil,
        p1.memory, wl_nil]
      output := by rw [p6.output, p5.output, p4.output, p3.output, p2.output, p1.output]
      frame := fun n lo hi out => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
        rw [k6 n lo hi, k5 n out.1 lo hi, k4 n lo hi, k3 n lo hi, k2 n out.1 lo hi]
        exact k1 n lo hi (by simp; omega)
      htif := by
        rw [p6.frame _ (fun n _ => Named.NamedValue.gprReg_ne_htif n) (by decide),
          p5.frame _ (fun n _ => Named.NamedValue.gprReg_ne_htif n) (by decide),
          p4.frame _ (fun n _ => Named.NamedValue.gprReg_ne_htif n) (by decide),
          p3.frame _ (fun n _ => Named.NamedValue.gprReg_ne_htif n) (by decide),
          p2.frame _ (fun n _ => Named.NamedValue.gprReg_ne_htif n) (by decide),
          p1.frame _ (fun n _ => Named.NamedValue.gprReg_ne_htif n) (by decide)] }

end OCaml.Vm.Primitives.Memprof.Eqdf2
