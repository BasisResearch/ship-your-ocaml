import OCaml.Vm.Repr
import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.StepFrameOut
import OCaml.Vm.Boot.Startup.GprPresence

/-! Register presence across a native run: every general-purpose register that
held a value still holds one, and `gp` (`x3`, which no C code writes) is
unchanged. -/
namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

/-- Register presence and `gp` kept from `c` to `d`. -/
structure GprsKept (c d : Config) : Prop where
  present : ∀ n, 1 ≤ n → n ≤ 31 → (gprGet c.σ n).isSome → (gprGet d.σ n).isSome
  gp : gpr d 3 = gpr c 3

theorem GprsKept.refl (c : Config) : GprsKept c c := ⟨fun _ _ _ h => h, rfl⟩

theorem GprsKept.trans {c d e : Config} (h : GprsKept c d) (h' : GprsKept d e) : GprsKept c e :=
  ⟨fun n lo hi p => h'.present n lo hi (h.present n lo hi p), h'.gp.trans h.gp⟩

/-- Complete GPR presence survives a run that keeps register presence. -/
theorem GprsKept.gprPresent {c d : Config} (h : GprsKept c d) (p : OCaml.Vm.Boot.Startup.GprPresent c.σ) :
    OCaml.Vm.Boot.Startup.GprPresent d.σ :=
  ⟨fun n lo hi => h.present n lo (by omega) (p.get n lo hi)⟩

/-- A run that writes only `W` (not `gp`), each written register present. -/
theorem GprsKept.of_written {c d : Config} {W : List Nat} (no3 : 3 ∉ W)
    (written : ∀ n ∈ W, (gprGet d.σ n).isSome)
    (frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ W → gprGet d.σ n = gprGet c.σ n) : GprsKept c d where
  present n lo hi p := by
    by_cases w : n ∈ W
    · exact written n w
    · rw [frame n lo hi w]; exact p
  gp := frame 3 (by decide) (by decide) no3

/-- A run with a register frame outside the ABI write set `W` (checked
`KeysOK`, not `gp`) and each written register present. -/
theorem GprsKept.of_regFrame {c d : Config} {W : List Nat} (keys : KeysOK W) (no3 : 3 ∉ W)
    (written : ∀ n ∈ W, (gprGet d.σ n).isSome)
    (frame : ∀ r : LeanRV64DExecutable.Register, (∀ n ∈ W, gprReg n ≠ r) →
      (∀ q ∈ noiseRegs, (q == r) = false) → d.σ.regs.get? r = c.σ.regs.get? r) :
    GprsKept c d :=
  GprsKept.of_written no3 written fun n lo hi w =>
    gprGet_of_frame n lo hi (by gpr_cases n => decide)
      (fun m hm => by
        obtain ⟨b1, b2⟩ := keys m hm
        exact gprReg_beq_false m (by omega) n (by omega) b1 lo (fun e => w (e ▸ hm)))
      (fun R hn hw => frame R (fun m hm e => by have := hw m hm; rw [e] at this; simp at this) hn)

/-- A step frame over ABI registers `W` (checked `KeysOK`, not `gp`), each
written register present. -/
theorem GprsKept.of_stepFrame {c d : Config} {W : List Nat} (keys : KeysOK W) (no3 : 3 ∉ W)
    (written : ∀ n ∈ W, (gprGet d.σ n).isSome)
    (frame : StepFrameOut (W.map gprReg ++ noiseRegs) c.σ d.σ) : GprsKept c d :=
  GprsKept.of_regFrame keys no3 written fun r hr hn => frame.frame r fun q hq => by
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨n, hn', rfl⟩ := List.mem_map.mp hq
      exact beq_eq_false_iff_ne.mpr (hr n hn')
    · exact hn q hq

/-- A call seam writes only `ra`, which it links. -/
theorem GprsKept.of_x1 {c d : Config} (link : (gprGet d.σ 1).isSome)
    (frame : ∀ R : LeanRV64DExecutable.Register, (∀ q ∈ noiseRegs, (q == R) = false) →
      (gprReg 1 == R) = false → d.σ.regs.get? R = c.σ.regs.get? R) : GprsKept c d :=
  GprsKept.of_regFrame (W := [1]) (by decide) (by decide)
    (fun n hn => by rw [List.mem_singleton.mp hn]; exact link)
    (fun R hr hn => frame R hn (beq_eq_false_iff_ne.mpr (hr 1 (by simp))))

/-- A run that keeps every GPR. -/
theorem GprsKept.of_gprs {c d : Config} (h : ∀ n, gpr d n = gpr c n) : GprsKept c d :=
  ⟨fun n _ _ p => by change (gpr d n).isSome; rw [h n]; exact p, h 3⟩

/-- A run whose written ABI registers are among its symbolic register pins. -/
theorem GprsKept.of_holds {c d : Config} {W : List Nat} {L : GRegs} (keys : KeysOK W) (no3 : 3 ∉ W)
    (holds : GHolds d.σ L) (cover : ∀ n ∈ W, n ∈ keysG L)
    (frame : ∀ r : LeanRV64DExecutable.Register, (∀ n ∈ W, gprReg n ≠ r) →
      (∀ q ∈ noiseRegs, (q == r) = false) → d.σ.regs.get? r = c.σ.regs.get? r) : GprsKept c d :=
  GprsKept.of_regFrame keys no3 (fun n hn => by
    obtain ⟨v, hv⟩ := lookup_of_mem L (cover n hn)
    rw [gholds_lookup L holds hv]; rfl) frame

end OCaml.Vm.Primitives
