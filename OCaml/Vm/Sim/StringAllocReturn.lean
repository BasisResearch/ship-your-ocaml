import OCaml.Vm.Sim.StringAllocEntry
import OCaml.Vm.Sim.PrimAllocFrame
import OCaml.Vm.Sim.AllocChain
import OCaml.Vm.Sim.PayloadWindows
import OCaml.Vm.Sim.ConfigLogWindows

/-!
# The C_CALL return of a string-allocating primitive

A log inside the four windows of a string-allocating primitive (its native
frame, its nursery block, the domain's `young_ptr` and `local_roots`) lies
below the native stack pointer, misses the caller's saved C-call words and
consists of `PrimAllocEntry` stores.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

variable {c : Config} {N D Y Lm k : Nat} {log : List WEntry}

theorem StringAllocEntry.bound (e : StringAllocEntry c N D Y Lm k) : N < 2 ^ 32 := by
  have := e.nativeHigh; simp only [Layout.sym_stack_top] at this; omega

/-- The log lies below the native stack pointer. -/
theorem StringAllocEntry.below (e : StringAllocEntry c N D Y Lm k) (hk : 48 ≤ k)
    (inside : LogInW (configWindows N D Y) log) :
    ∀ n, gpr c 2 = some (BitVec.ofNat 64 n) → LogInW [⟨0, n⟩] log := by
  intro n hn
  have same : BitVec.ofNat 64 n = BitVec.ofNat 64 N := Option.some.inj (hn.symm.trans e.stack)
  have hN : n % 2 ^ 64 = N := by
    have := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat] at this
    rw [this]; exact Nat.mod_eq_of_lt (by have := e.bound; omega)
  have ge : N ≤ n := by rw [← hN]; exact Nat.mod_le _ _
  have := e.nativeLow; have := e.domainHigh; have := e.youngHigh; have := e.room
  apply logInW_widen inside
  intro w hw
  simp only [configWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [nativeHeadroom, Layout.domainStateBytes] at *
  rcases hw with rfl | rfl | rfl | rfl <;> simp only [Layout.off_young_ptr, Layout.off_local_roots] <;> omega

/-- Every store is a `PrimAllocEntry`. -/
theorem StringAllocEntry.entries (e : StringAllocEntry c N D Y Lm k) (hk : 48 ≤ k)
    (inside : LogInW (configWindows N D Y) log) : ∀ x ∈ log, PrimAllocEntry c x := by
  intro x hx
  have mem := logInW_mem inside hx
  simp only [configWindows, InsideW, Layout.off_young_ptr, Layout.off_local_roots] at mem
  have nl := e.nativeLow; have rm := e.room
  have he : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  rw [he] at nl
  simp only [nativeHeadroom] at nl
  unfold PrimAllocEntry
  simp only [Layout.off_young_ptr, Layout.off_local_roots]
  rw [e.young, e.limit, e.domain]
  rcases mem with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | f
  · exact Or.inr (Or.inl (by rw [he]; omega))
  · exact Or.inl ⟨by omega, hi⟩
  · exact Or.inr (Or.inr (Or.inl ⟨lo, hi⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨lo, hi⟩))
  · exact f.elim

end OCaml.Vm.Sim
