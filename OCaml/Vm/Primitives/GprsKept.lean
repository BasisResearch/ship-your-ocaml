import OCaml.Vm.Primitives.LibraryEffects

/-! Register presence across a native run: every general-purpose register that
held a value still holds one, and `gp` (`x3`, which no C code writes) is
unchanged. Library models that take `VsaOk` (memmove) need complete GPR
presence at their entry; posts carry this monotone fact instead of a full
register frame for temporaries. -/
namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

/-- Register presence and `gp` kept from `c` to `d`. -/
structure GprsKept (c d : Config) : Prop where
  present : ∀ n, 1 ≤ n → n ≤ 31 → (gprGet c.σ n).isSome → (gprGet d.σ n).isSome
  gp : gpr d 3 = gpr c 3

theorem GprsKept.refl (c : Config) : GprsKept c c := ⟨fun _ _ _ h => h, rfl⟩

theorem GprsKept.trans {c d e : Config} (h : GprsKept c d) (h' : GprsKept d e) : GprsKept c e :=
  ⟨fun n lo hi p => h'.present n lo hi (h.present n lo hi p), h'.gp.trans h.gp⟩

/-- A generated block's effect: its written registers hold values, the rest
are unchanged, and `gp` is not written. -/
theorem GprsKept.of_effect {writes : List Nat} {mem : Std.ExtHashMap Nat (BitVec 8)} {c d : Config}
    {pc value : BitVec 64} (p : EffectPost writes mem c pc value d) (keys : KeysOK writes) (no3 : 3 ∉ writes)
    (written : ∀ n ∈ writes, (gprGet d.σ n).isSome) : GprsKept c d where
  present n lo hi h := by
    by_cases w : n ∈ writes
    · exact written n w
    · change (gpr d n).isSome
      rw [p.gpr_frame keys n lo hi w]; exact h
  gp := p.gpr_frame keys 3 (by decide) (by decide) no3

end OCaml.Vm.Primitives
