import OCaml.Vm.Sim.CcallAllocation

/-!
# Scalars at a string-allocating primitive's entry

`caml_sys_get_config`, `caml_sys_get_argv` and `caml_sys_executable_name`
build a native frame below the interpreter's, store into the domain record
and reserve their objects below `young_ptr`. `StringAllocEntry c N D Y Lm k`
names the numbers their logs are stated over at the callee entry: the native
stack pointer `N`, the domain record `D`, the young pointer `Y` and limit
`Lm`, with room for `k` bytes of fresh objects. `StringAllocEntry.of_setup`
derives them from the C_CALL setup.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The numbers a string-allocating primitive's log is stated over. -/
structure StringAllocEntry (c : Config) (N D Y Lm k : Nat) : Prop where
  stack : gpr c 2 = some (BitVec.ofNat 64 N)
  nativeLow : Vsa.Sim.DlHeap.heapEnd + nativeHeadroom ≤ N
  nativeHigh : N ≤ Layout.sym_stack_top
  nativeAligned : N % 16 = 0
  domain : (word c Layout.sym_Caml_state).toNat = D
  domainLow : Layout.sym_bss_end ≤ D
  domainHigh : D + Layout.domainStateBytes ≤ Vsa.Sim.DlHeap.heapEnd
  domainAligned : D % 8 = 0
  young : (runtimeFields c).youngPtr = Y
  limit : (runtimeFields c).youngLimit = Lm
  youngHigh : Y ≤ Vsa.Sim.DlHeap.heapEnd
  youngAligned : Y % 8 = 0
  limitLow : Layout.sym_bss_end ≤ Lm
  /-- the free nursery misses the domain record -/
  domainApart : D + Layout.domainStateBytes ≤ Lm ∨ Y ≤ D
  /-- room for the fresh objects -/
  room : Lm + k ≤ Y

theorem StringAllocEntry.of_setup {ra : BitVec 64} {args : List Val} {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high domain entry : Nat} {env : BitVec 64} {c : Config} {w : Nat}
    (setup : CcallSetupPost ra args L P s pl cp sp high domain entry env c)
    (fits : s.heap.words + w ≤ L.budget.heapWords) :
    ∃ N, StringAllocEntry c N (word c Layout.sym_Caml_state).toNat (runtimeFields c).youngPtr
      (runtimeFields c).youngLimit (8 * w) := by
  obtain ⟨I, inv, valid⟩ := setup.native
  have g := setup.geometry
  have ng := g.nursery
  have room := g.room.nursery
  have stat := ng.statics
  have dom := ng.domain.1
  simp only [Gc.nurseryFree] at stat dom
  have hh : Layout.sym_stack_top ≤ 0x100000000 := by decide
  exact ⟨I.nativeSp,
    { stack := inv.stack, nativeLow := valid.headroom
      nativeHigh := by have := valid.high; omega
      nativeAligned := valid.aligned, domain := rfl
      domainLow := g.domainLow, domainHigh := g.domainArena, domainAligned := g.domainAligned
      young := rfl, limit := rfl, youngHigh := ng.arena, youngAligned := ng.aligned
      limitLow := stat
      domainApart := by omega
      room := by omega }⟩

/-- A natural address as a 64-bit word and back. -/
theorem toNat_ofNat_small {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_add_small {n k : Nat} : BitVec.ofNat 64 n + BitVec.ofNat 64 k = BitVec.ofNat 64 (n + k) :=
  (BitVec.ofNat_add n k).symm

theorem ofNat_sub_small {n k : Nat} (hk : k ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp; omega

/-- A word-aligned natural address in writable RAM. -/
theorem window_of_nat {n : Nat} (lo : Layout.sym_tohost + 16 ≤ n) (hi : n + 8 ≤ 0x100000000)
    (al : n % 8 = 0) : WriteWindow (BitVec.ofNat 64 n) 8 := by
  have e : (BitVec.ofNat 64 n).toNat = n := toNat_ofNat_small (by omega)
  have t : 0x80000000 + 16 ≤ Layout.sym_tohost + 16 := by decide
  exact ⟨by rw [e]; omega, by rw [e]; exact hi, by rw [e]; exact lo, by rw [e]; exact al⟩

/-- The three nursery metadata words at the entry. -/
theorem StringAllocEntry.words {c : Config} {N D Y Lm k : Nat} (e : StringAllocEntry c N D Y Lm k) :
    word c Layout.sym_Caml_state = BitVec.ofNat 64 D ∧
      word c (D + Layout.off_young_ptr) = BitVec.ofNat 64 Y ∧
      word c (D + Layout.off_young_limit) = BitVec.ofNat 64 Lm := by
  have y := e.young; have l := e.limit; have d := e.domain
  simp only [runtimeFields, domainWord, d] at y l
  refine ⟨?_, ?_, ?_⟩
  · rw [← d, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← y, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← l, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end OCaml.Vm.Sim
