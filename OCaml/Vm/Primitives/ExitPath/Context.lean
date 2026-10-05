import OCaml.Vm.Primitives.ExitPath.Effects
import OCaml.Vm.Primitives.LibraryEffects

/-! The state retained along the exit path: library health, the image, the
console output so far, and all memory outside the native stack window. -/
namespace OCaml.Vm.Primitives.ExitPath
open Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable

/-- Every entry of a write log lies in the address window `[lo, hi)`. -/
def LogWithin (log : List WEntry) (lo hi : Nat) : Prop :=
  ∀ e ∈ log, lo ≤ e.1 ∧ e.1 + e.2.1 ≤ hi

theorem LogWithin.outL {log : List WEntry} {lo hi x : Nat} (h : LogWithin log lo hi)
    (outside : x < lo ∨ hi ≤ x) : OutL log x := by
  induction log with
  | nil => trivial
  | cons e rest ih =>
    have he := h e (by simp)
    exact ⟨by omega, ih (fun e' he' => h e' (by simp [he']))⟩

theorem LogWithin.nil {lo hi : Nat} : LogWithin [] lo hi := fun _ h => nomatch h

/-- The exit-path invariant relative to the configuration at the call. -/
structure ExitCtx (live : Nat → Prop) (lo hi : Nat) (c d : Config) : Prop where
  ok : VsaOk live d
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ
  frame : ∀ x, (x < lo ∨ hi ≤ x) → (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0

theorem ExitCtx.leaf {live lo hi c d} (h : ExitCtx live lo hi c d) {ra : BitVec 64}
    (raReg : gpr d 1 = some ra) (aligned : ra.toNat % 4 = 0) : LeafInput ra d :=
  ⟨h.ok.good, h.image, h.minstret, raReg, aligned, h.ok.tick⟩

theorem ExitCtx.present {live lo hi c d} (h : ExitCtx live lo hi c d) (n : Nat)
    (lo1 : 1 ≤ n) (hi31 : n ≤ 31) : gpr d n = some ((gpr d n).getD 0) := by
  have := h.ok.gpr n lo1 hi31
  change gprGet d.σ n = some ((gprGet d.σ n).getD 0)
  cases e : gprGet d.σ n with
  | none => rw [e] at this; cases this
  | some v => rfl

/-- One generated block preserves the invariant when its log stays in the window. -/
theorem ExitCtx.step {live lo hi c d e writes log pc value regs}
    (h : ExitCtx live lo hi c d) (post : WriteRegistersPost writes log d pc value regs e)
    (within : LogWithin log lo hi) (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) :
    ExitCtx live lo hi c e where
  ok := post.vsaOk h.ok keys cover
  image := post.image
  minstret := post.minstret
  output := by
    unfold Vsa.Machine.output
    rw [post.output]
    exact h.output
  frame := by
    intro x out
    rw [post.memory, writeLog_out _ _ _ (within.outL out)]
    exact h.frame x out

/-- A direct call changes only `ra` and the pc. -/
theorem ExitCtx.call {live lo hi c d e target value regs}
    (h : ExitCtx live lo hi c d) (post : RegistersPost [1] d.σ.mem d target value regs e)
    (cover : 1 ∈ keysG regs) : ExitCtx live lo hi c e where
  ok := post.vsaOk_of_present h.ok (by decide) (by simpa using cover)
    (fun a ha => by rw [post.memory]; exact h.ok.live a ha)
  image := post.image
  minstret := post.minstret
  output := by
    unfold Vsa.Machine.output
    rw [post.output]
    exact h.output
  frame := by
    intro x out
    rw [post.memory]
    exact h.frame x out

/-- Loads of a word outside the window see the value at the call. -/
theorem ExitCtx.read {live lo hi c d} (h : ExitCtx live lo hi c d) {a : Nat}
    (outside : a + 8 ≤ lo ∨ hi ≤ a) : read8 d.σ.mem a = read8 c.σ.mem a := by
  simp only [read8]
  rw [h.frame a (by omega), h.frame (a + 1) (by omega), h.frame (a + 2) (by omega),
    h.frame (a + 3) (by omega), h.frame (a + 4) (by omega), h.frame (a + 5) (by omega),
    h.frame (a + 6) (by omega), h.frame (a + 7) (by omega)]

end OCaml.Vm.Primitives.ExitPath
