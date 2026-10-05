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

/-- The registers the default exit path reads before writing them: ra, sp,
a0, s0, s1 and s2–s10 (from `caml_do_exit`'s and `__call_exitprocs`'s saves). -/
def exitReads : List Nat := [1, 2, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26]

/-- Machine health needed along the exit path: no other register need be present. -/
structure ExitOk (d : Config) : Prop where
  good : GoodState d.σ
  tick : d.tick < 2
  htifIdle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  present : ∀ n ∈ exitReads, (gprGet d.σ n).isSome

/-- The exit-path invariant relative to the configuration at the call. -/
structure ExitCtx (lo hi : Nat) (c d : Config) : Prop where
  ok : ExitOk d
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ
  frame : ∀ x, (x < lo ∨ hi ≤ x) → (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0

theorem ExitCtx.leaf {lo hi c d} (h : ExitCtx lo hi c d) {ra : BitVec 64}
    (raReg : gpr d 1 = some ra) (aligned : ra.toNat % 4 = 0) : LeafInput ra d :=
  ⟨h.ok.good, h.image, h.minstret, raReg, aligned, h.ok.tick⟩

theorem ExitCtx.present {lo hi c d} (h : ExitCtx lo hi c d) (n : Nat)
    (read : n ∈ exitReads) : gpr d n = some ((gpr d n).getD 0) := by
  have := h.ok.present n read
  change gprGet d.σ n = some ((gprGet d.σ n).getD 0)
  cases e : gprGet d.σ n with
  | none => rw [e] at this; cases this
  | some v => rfl

/-- One generated block preserves the invariant when its log stays in the window. -/
theorem ExitCtx.step {lo hi c d e writes log pc value regs}
    (h : ExitCtx lo hi c d) (post : WriteRegistersPost writes log d pc value regs e)
    (within : LogWithin log lo hi) (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) :
    ExitCtx lo hi c e where
  ok := by
    refine ⟨post.good, post.tick, ?_, ?_⟩
    · rw [post.frame _ (fun n _ => by
        have h := gprReg_htif_payload n
        exact fun eq => by rw [eq, beq_self_eq_true] at h; contradiction) (by decide)]
      exact h.ok.htifIdle
    · intro n read
      have bounds : 1 ≤ n ∧ n ≤ 31 := by simp [exitReads] at read; omega
      by_cases written : n ∈ writes
      · obtain ⟨v, hv⟩ := lookupG_of_mem (cover n written)
        rw [gholds_lookup _ post.regs hv]
        rfl
      · have frame := post.toEffectPost.gpr_frame keys n bounds.1 bounds.2 written
        change gprGet e.σ n = gprGet d.σ n at frame
        rw [frame]
        exact h.ok.present n read
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
theorem ExitCtx.call {lo hi c d e target value regs}
    (h : ExitCtx lo hi c d) (post : RegistersPost [1] d.σ.mem d target value regs e)
    (cover : 1 ∈ keysG regs) : ExitCtx lo hi c e where
  ok := by
    refine ⟨post.good, post.tick, ?_, ?_⟩
    · rw [post.frame _ (fun n _ => by
        have h := gprReg_htif_payload n
        exact fun eq => by rw [eq, beq_self_eq_true] at h; contradiction) (by decide)]
      exact h.ok.htifIdle
    · intro n read
      have bounds : 1 ≤ n ∧ n ≤ 31 := by simp [exitReads] at read; omega
      by_cases written : n = 1
      · subst written
        obtain ⟨v, hv⟩ := lookupG_of_mem cover
        rw [gholds_lookup _ post.regs hv]
        rfl
      · have frame := post.toEffectPost.gpr_frame (by decide) n bounds.1 bounds.2 (by simpa using written)
        change gprGet e.σ n = gprGet d.σ n at frame
        rw [frame]
        exact h.ok.present n read
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
theorem ExitCtx.read {lo hi c d} (h : ExitCtx lo hi c d) {a : Nat}
    (outside : a + 8 ≤ lo ∨ hi ≤ a) : read8 d.σ.mem a = read8 c.σ.mem a := by
  simp only [read8]
  rw [h.frame a (by omega), h.frame (a + 1) (by omega), h.frame (a + 2) (by omega),
    h.frame (a + 3) (by omega), h.frame (a + 4) (by omega), h.frame (a + 5) (by omega),
    h.frame (a + 6) (by omega), h.frame (a + 7) (by omega)]

end OCaml.Vm.Primitives.ExitPath
