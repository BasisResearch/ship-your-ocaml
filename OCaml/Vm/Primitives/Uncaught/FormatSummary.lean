import OCaml.Vm.Primitives.Uncaught.FormatReturn

/-!
# `caml_format_exception` on a constant exception, entry to return

`format_exception_constant` composes the prologue (`format_pro`), `strlen`
and the tests (`format_measure`), the copy into the buffer (`format_copy`),
the terminator and the call (`format_terminate`), `caml_stat_alloc_noexc`
(`format_alloc`), the copy out (`format_out`) and the return
(`format_leave`). The result `res` is a fresh block holding the name and its
terminator.
-/

namespace OCaml.Vm.Primitives.Uncaught.FormatException
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Boot.Startup
  VsaIris VsaIris.VsaHeap

/-- **`caml_format_exception` returned** on a constant exception: `res` is a
fresh block of `len + 1` bytes holding the name and its terminator. -/
structure FormatDone (H : List (Nat × Nat)) (capacity : Nat) (ra sp s0 s1 s2 s4 s5 : BitVec 64)
    (name : List (BitVec 8)) (res : BitVec 64) (before after : Config) : Prop where
  ready : RuntimeReadyL imageLive ((res.toNat, name.length + 1) :: H) capacity sp ra after
  pc : PCAt ra after
  result : gprGet after.σ 10 = some res
  low : heapStart ≤ res.toNat
  high : res.toNat + (name.length + 1) ≤ heapEnd
  disjoint : ∀ e ∈ H, ∀ a, InExt (res.toNat, name.length + 1) a → ¬ InExt e a
  bytes : ∀ i (hi : i < name.length), (after.σ.mem[res.toNat + i]?).getD 0 = name[i]
  term : (after.σ.mem[res.toNat + name.length]?).getD 0 = 0#8
  saved0 : gprGet after.σ 8 = some s0
  saved1 : gprGet after.σ 9 = some s1
  saved2 : gprGet after.σ 18 = some s2
  saved4 : gprGet after.σ 20 = some s4
  saved5 : gprGet after.σ 21 = some s5
  callee : ∀ k ∈ formatCallee, gprGet after.σ k = gprGet before.σ k
  /-- the caller's frame -/
  caller : ∀ a, sp.toNat ≤ a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0
  /-- every other live block -/
  blocks : ∀ q m a, (q, m) ∈ H → heapStart ≤ q → q + m ≤ heapEnd → q ≤ a → a < q + m →
    (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0
  /-- low memory outside the allocator's globals -/
  globals : ∀ a, a < heapStart → ¬ allocGlobal a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ

/-- **`caml_format_exception` on a constant exception**, entry to return. -/
theorem format_exception_constant {H : List (Nat × Nat)} {capacity charge : Nat}
    {ra sp exn np s0 s1 s2 s4 s5 : BitVec 64} {name : List (BitVec 8)} {c0 : Config}
    (h : FormatInput ra sp exn np s0 s1 s2 s4 s5 name c0) (heap : FormatHeap H capacity charge sp ra name.length c0) :
    ∃ res r, Steps c0 r ∧ FormatDone H capacity ra sp s0 s1 s2 s4 s5 name res c0 r := by
  obtain ⟨p, run1, pd⟩ := format_pro h
  obtain ⟨d, run2, m⟩ := format_measure h pd
  obtain ⟨e, run3, cp⟩ := format_copy h pd m
  obtain ⟨f, run4, fl⟩ := format_terminate h cp
  have fits := h.fits
  have hbase : heapEnd ≤ nativeFrameBase sp 432 := by
    unfold nativeFrameBase; exact Nat.le_sub_of_add_le h.frame.lower
  have low (a : Nat) (ha : a < heapEnd) : (f.σ.mem[a]?).getD 0 = (c0.σ.mem[a]?).getD 0 :=
    filled_out h pd fl (Or.inl (Nat.lt_of_lt_of_le ha hbase))
  have readyF := ready_transport heap.ready fl.leaf fl.ready
    (fun a ha => low a (Nat.lt_of_lt_of_le ha (by decide))) (fun a ha => low a (allocator_foot_below ha)) fl.stack
  obtain ⟨g, res, run5, A⟩ := format_alloc heap fits fl readyF
  obtain ⟨e4, run6, co⟩ := format_out h.frame A ((A.saved 8 (by decide)).trans fl.sizeSaved)
    ((A.saved 20 (by decide)).trans fl.data)
  have resEnd : res.toNat + (name.length + 1) ≤ nativeFrameBase sp 432 := Nat.le_trans A.high hbase
  have frameTop : nativeFrameBase sp 432 ≤ sp.toNat := Nat.sub_le _ _
  have savedE : SavedWords e4.σ.mem sp ra s0 s1 s2 s4 s5 :=
    (filled_saved h pd fl).transport fun a lo _ =>
      (co.kept a (Or.inr (Nat.le_trans resEnd (Nat.le_trans (Nat.le_add_right _ 376) lo)))).trans
        (A.caller a (Nat.le_trans (Nat.le_add_right _ _) lo))
  obtain ⟨r, run7, R⟩ := format_leave h.frame h.leaf.aligned co savedE
  have dataIn (i : Nat) : sp.toNat - 432 ≤ dataNat sp + i :=
    Nat.le_trans (Nat.sub_le_sub_left (by decide) _) (Nat.le_add_right _ _)
  refine ⟨res, r, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))), ?_⟩
  exact
    { ready := R.ready
      pc := R.pc
      result := R.result
      low := A.low
      high := A.high
      disjoint := A.disjoint
      bytes := fun i hi => by
        rw [R.memory, co.copied i (by omega), A.caller _ (dataIn i)]
        exact fl.memory.buffer i hi
      term := by
        rw [R.memory, co.copied name.length (by omega), A.caller _ (dataIn _)]
        exact fl.memory.term
      saved0 := R.saved0
      saved1 := R.saved1
      saved2 := R.saved2
      saved4 := R.saved4
      saved5 := R.saved5
      callee := fun k hk => by
        have mem := hk
        simp only [formatCallee, List.mem_cons, List.not_mem_nil, or_false] at mem
        have abi : k ∈ abiSaved := by
          rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact (R.callee k hk).trans ((co.callee k hk).trans ((A.saved k abi).trans ((fl.callee k hk).trans
          (pd.frame k (by omega) (by omega) (fun hm => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega)))))
      caller := fun a ha => by
        rw [R.memory, co.kept a (Or.inr (Nat.le_trans resEnd (Nat.le_trans frameTop ha))),
          A.caller a (Nat.le_trans (Nat.sub_le _ _) ha)]
        exact filled_out h pd fl (Or.inr ha)
      blocks := fun q m a member lo hi qa aq => by
        have apart : a < res.toNat ∨ res.toNat + (name.length + 1) ≤ a := by
          by_cases inside : res.toNat ≤ a ∧ a < res.toNat + (name.length + 1)
          · exact absurd ⟨qa, aq⟩ (A.disjoint (q, m) member a inside)
          · omega
        rw [R.memory, co.kept a apart, A.blocks q m a member lo hi qa aq]
        exact filled_out h pd fl (Or.inl (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le aq hi) hbase))
      globals := fun a lo ng => by
        have order : heapStart ≤ res.toNat := A.low
        rw [R.memory, co.kept a (Or.inl (by omega)), A.globals a lo ng]
        exact filled_out h pd fl (Or.inl (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le lo (by decide)) hbase))
      output := by
        rw [R.output, co.output, A.output, fl.output]
        simp only [Vsa.Machine.output]
        rw [pd.output] }

end OCaml.Vm.Primitives.Uncaught.FormatException
