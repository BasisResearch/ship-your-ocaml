import OCaml.Vm.Primitives.GprsKeptCore
import OCaml.Vm.Primitives.LibraryEffects
import OCaml.Vm.Primitives.Effects
import OCaml.Vm.Boot.Startup.GprPresence

/-! Register presence across a native run: every general-purpose register that
held a value still holds one, and `gp` (`x3`, which no C code writes) is
unchanged. Library models that take `VsaOk` (memmove) need complete GPR
presence at their entry; posts carry this monotone fact instead of a full
register frame for temporaries. -/
namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

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

/-- A generated block with its register pins: every written register is
among the pinned ones. -/
theorem GprsKept.of_pins {writes : List Nat} {mem : Std.ExtHashMap Nat (BitVec 8)} {c d : Config}
    {pc value : BitVec 64} {regs : GRegs} (p : RegistersPost writes mem c pc value regs d)
    (keys : KeysOK writes) (no3 : 3 ∉ writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) : GprsKept c d :=
  GprsKept.of_effect p.toEffectPost keys no3 fun n hn => by
    obtain ⟨w, hw⟩ := lookup_of_mem regs (cover n hn)
    rw [gholds_lookup regs p.regs hw]; rfl


end OCaml.Vm.Primitives
