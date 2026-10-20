import OCaml.Vm.Primitives.LibraryEffects
import OCaml.Vm.Primitives.Effects
import OCaml.Vm.Primitives.GprsKeptCore
import OCaml.Vm.Boot.Startup.AllocatorRun

/-! Register values across a composed native run: every general-purpose
register outside the accumulated written set keeps its value. One `GprsSame`
per block (`of_post`), composed with `trans`, replaces per-step frame
hypotheses and their hand-chained `.trans` towers; a register is read through
the whole run with one `get` and one `decide` on membership. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Registers `x1`–`x31` outside `writes` agree between `before` and `after`. -/
structure GprsSame (before after : Config) (writes : List Nat) : Prop where
  same : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ writes → gprGet after.σ n = gprGet before.σ n

theorem GprsSame.of_effect {writes : List Nat} {mem : Std.ExtHashMap Nat (BitVec 8)} {c d : Config}
    {pc value : BitVec 64} (p : EffectPost writes mem c pc value d) (keys : KeysOK writes) : GprsSame c d writes :=
  ⟨fun n lo hi out => p.gpr_frame keys n lo hi out⟩

/-- A generated block's (or call's) register post. -/
theorem GprsSame.of_post {writes : List Nat} {mem : Std.ExtHashMap Nat (BitVec 8)} {c d : Config}
    {pc value : BitVec 64} {regs : GRegs} (p : RegistersPost writes mem c pc value regs d) (keys : KeysOK writes) :
    GprsSame c d writes :=
  GprsSame.of_effect p.toEffectPost keys

theorem GprsSame.refl (c : Config) : GprsSame c c [] := ⟨fun _ _ _ _ => rfl⟩

theorem GprsSame.trans {c d e : Config} {ws vs : List Nat} (first : GprsSame c d ws) (second : GprsSame d e vs) :
    GprsSame c e (vs ++ ws) :=
  ⟨fun n lo hi out => by
    rw [List.mem_append, not_or] at out
    exact (second.same n lo hi out.1).trans (first.same n lo hi out.2)⟩

/-- Widen the written set (one `decide` on inclusion). -/
theorem GprsSame.mono {c d : Config} {ws vs : List Nat} (k : GprsSame c d ws) (sub : ∀ n ∈ ws, n ∈ vs) :
    GprsSame c d vs :=
  ⟨fun n lo hi out => k.same n lo hi fun w => out (sub n w)⟩

/-- A register's value carried from `before` to `after`. -/
theorem GprsSame.get {c d : Config} {ws : List Nat} (k : GprsSame c d ws) {n : Nat} (lo : 1 ≤ n) (hi : n ≤ 31)
    (out : n ∉ ws) {v : BitVec 64} (h : gprGet c.σ n = some v) : gprGet d.σ n = some v :=
  (k.same n lo hi out).trans h

/-- The registers a called C function may clobber: all but `abiSaved`. -/
def abiClobbered : List Nat := [1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- A callee post that keeps the ABI callee-saved registers. -/
theorem GprsSame.of_saved {c d : Config} (saved : ∀ k ∈ abiSaved, gprGet d.σ k = gprGet c.σ k) :
    GprsSame c d abiClobbered :=
  ⟨fun n lo hi out => saved n (by simp only [abiClobbered, abiSaved, List.mem_cons, List.not_mem_nil, or_false] at out ⊢; omega)⟩

/-- A library post's step frame over the ABI registers `W` and the noise registers. -/
theorem GprsSame.of_stepFrame {c d : Config} {W : List Nat} (keys : KeysOK W)
    (frame : StepFrameOut (W.map gprReg ++ noiseRegs) c.σ d.σ) : GprsSame c d W :=
  ⟨fun n lo hi w => gprGet_of_frame n lo hi (by gpr_cases n => decide)
      (fun m hm => by
        obtain ⟨b1, b2⟩ := keys m hm
        exact gprReg_beq_false m (by omega) n (by omega) b1 lo (fun e => w (e ▸ hm)))
      (fun R hn hw => frame.frame R fun q hq => by
        rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
          exact hw k hk
        · exact hn q hq)⟩

/-- A register frame over all registers outside `W` and the noise registers
(the `frame` field of `BoundaryPost` and `EffectPost`). -/
theorem GprsSame.of_regFrame {c d : Config} {W : List Nat} (keys : KeysOK W)
    (frame : ∀ r : LeanRV64DExecutable.Register, (∀ n ∈ W, gprReg n ≠ r) →
      (∀ q ∈ noiseRegs, (q == r) = false) → d.σ.regs.get? r = c.σ.regs.get? r) : GprsSame c d W :=
  ⟨fun n lo hi w => gprGet_of_frame n lo hi (by gpr_cases n => decide)
      (fun m hm => by
        obtain ⟨b1, b2⟩ := keys m hm
        exact gprReg_beq_false m (by omega) n (by omega) b1 lo (fun e => w (e ▸ hm)))
      (fun R hn hw => frame R (fun m hm e => by have := hw m hm; rw [e] at this; simp at this) hn)⟩

/-- Register presence follows when each written register holds a value and `gp` is unwritten. -/
theorem GprsSame.kept {c d : Config} {ws : List Nat} (k : GprsSame c d ws) (no3 : 3 ∉ ws)
    (written : ∀ n ∈ ws, (gprGet d.σ n).isSome) : GprsKept c d :=
  GprsKept.of_written no3 written k.same

end OCaml.Vm.Boot.Startup
