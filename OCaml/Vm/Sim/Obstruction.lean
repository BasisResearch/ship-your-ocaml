import OCaml.Refinement

/-!
# A1 precondition obstruction

`VmRepr` forgets the HTIF control registers. Setting `htif_done` preserves
it but prevents a positive machine run, or forces the wrong exit code.
Consequently the present `ArmSim` cannot hold for a loaded, good program
within budget. The simulation invariant needs a running-machine predicate
(preserved by the arms), including the code image and platform invariants.
This file records the obstruction without weakening the requested theorem.
-/

namespace OCaml.Vm.Sim
open OCaml.Bytecode Vsa.Machine LeanRV64DExecutable
open Sail Sail.ConcurrencyInterfaceV1

/-- Change only the two HTIF control registers, leaving VM observations intact. -/
def forceExit (c : Config) (e : BitVec 64) : Config :=
  { c with σ := { c.σ with regs :=
      (c.σ.regs.insert Register.htif_done true).insert Register.htif_exit_code e } }

/-- The current VM predicate admits already halted configurations. -/
theorem repr_forceExit {P : Prog} {s : St} {c : Config}
    (h : VmRepr P s c) (e : BitVec 64) : VmRepr P s (forceExit c e) := by
  obtain ⟨pl, cp, sp, high, h⟩ := h
  refine ⟨pl, cp, sp, high, ?_⟩
  have hpc : pcOf (forceExit c e) = pcOf c := by
    simp [pcOf, forceExit, Std.ExtDHashMap.get?_insert]
  have hregs : ∀ n, gpr (forceExit c e) n = gpr c n := by
    intro n
    unfold gpr Vsa.Sim.gprGet
    split <;> simp [forceExit, Std.ExtDHashMap.get?_insert]
  exact { h with
    atHead := hpc.trans h.atHead
    pc := (hregs _).trans h.pc
    spReg := (hregs _).trans h.spReg
    accu := by simpa only [hregs] using h.accu
    env := by simpa only [hregs] using h.env
    extra := (hregs _).trans h.extra }

/-- `stepOnce` checks HTIF before fetching any instruction. -/
theorem forceExit_halted (c : Config) (e : BitVec 64) :
    Halted (forceExit c e) e.toNat (forceExit c e).σ := by
  apply Halted.mk (n := c.steps)
  simp [Vsa.stepOnce, forceExit, EStateM.run, bind, Bind.bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get,
    EStateM.get, Std.ExtDHashMap.get?_insert]

/-- A positive segment cannot start at the forced exit state. -/
theorem forceExit_not_plus (c c' : Config) (e : BitVec 64) :
    ¬ Plus (forceExit c e) c' := by
  rintro ⟨n, hn⟩
  cases hn with
  | succ hstep _ => exact hstep.not_halted (forceExit_halted c e)

/-- Even the halt arm is impossible: `VmRepr` permits any HTIF exit code.
This refutes the current invariant for any represented reachable good state. -/
theorem armSim_not_repr {L : OCaml.Layout} {B : Budget} {P : Prog}
    (A : ArmSim L B P) (hg : Good P) (hf : Fits B P)
    {s : St} (hr : Reach P s) {c : Config} (hv : VmRepr P s c) : False := by
  have hg' := hg s hr
  cases hs : step P s with
  | unsupported => exact hg'.1 hs
  | wrong => exact hg'.2 hs
  | next s' =>
      obtain ⟨c', hp, _⟩ := A.next s s' (forceExit c 0) hr hg hf
        (repr_forceExit hv 0) hs
      exact forceExit_not_plus c c' 0 hp
  | halt e w =>
      let bad : BitVec 64 := if e = 0 then 1 else 0
      have hbad : bad.toNat ≠ e := by
        dsimp [bad]
        split <;> simp_all [eq_comm]
      have hm := A.halt s e w (forceExit c bad) hr hg hf (repr_forceExit hv bad) hs
      have hx : Halts (forceExit c bad) (output c.σ) bad.toNat :=
        ⟨_, _, .refl _, forceExit_halted c bad, rfl⟩
      exact hbad (hx.deterministic hm).2

/-- A nonvacuous instance of the lane exit criterion is impossible with
`ArmSim`'s current precondition, independently of any generator coverage. -/
theorem loaded_not_armSim {L : OCaml.Layout} {B : Budget} {P : Prog} {c : Config}
    (hl : Loaded L P c) (hg : Good P) (hf : Fits B P) : ¬ ArmSim L B P := by
  intro A
  obtain ⟨c', _, hv⟩ := A.entry c hl hg hf
  exact armSim_not_repr A hg hf ⟨0, .zero _⟩ hv

end OCaml.Vm.Sim
