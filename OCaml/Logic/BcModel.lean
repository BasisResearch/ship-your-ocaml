import OCaml.Bytecode.Semantics
import VsaIris.Adequacy
import OCaml.Run.Model

/-!
# Layer B′: a machine-level program logic over `BcSem`

MachCSL's pattern (ship-your-interpreter `VsaIris/`, after xv6iris) builds
an Iris language whose one expression is the CPU loop and whose primitive
step is one step of the ISA model; programs are verified by proving the
total WP of that loop from points-to ownership of registers and memory.
`VsaIris.MachineModel` is generic in the model. Here the "ISA" is `BcSem`:
`bcModel P` presents the ZINC machine of program `P` as a `MachineModel`,
so ship-your-interpreter's ghost state, WP rules and adequacy apply to
bytecode unchanged, and the exponentiating layer (per-segment WP rules
generated from disassembly) is re-targeted at bytecode disassembly
(`dumpobj`) instead of RISC-V disassembly (PLAN.md §Layer B′).

The machine-style view of a VM state:

* registers (`reg`): `0` pc, `1` accu, `2` env, `3` stack depth,
  `4` extra_args, `5` trap depth — values encoded by `enc`;
* memory (`mem`): byte `8 w + b` of the word-addressed store where word
  `w = Nat.pair r i` is stack slot `i` from the BOTTOM (`r = 0`) or field
  `i` of block `r - 1` (`r ≥ 1`), so a block and the stack are disjoint
  footprints and a frame rule applies per block.

`bytecode_adequacy` is proved by instantiating `VsaIris.mach_adequacy`:
a total-WP proof about `bcModel P` from the initial ownership implies that
`P` halts under `BcSem` with an exit satisfying the postcondition.
-/

namespace OCaml.Logic

open OCaml.Bytecode

/-- An injective pairing `ℕ × ℕ → ℕ`: `pair r i = 2^r (2 i + 1) - 1`. -/
def pair (r i : Nat) : Nat := 2 ^ r * (2 * i + 1) - 1

/-- Its inverse (the 2-adic valuation of `w + 1`, and the odd part). -/
def unpair (w : Nat) : Nat × Nat :=
  let rec go : Nat → Nat → Nat → Nat × Nat
    | 0, r, n => (r, n / 2)
    | f + 1, r, n => if n % 2 = 0 ∧ n ≠ 0 then go f (r + 1) (n / 2) else (r, n / 2)
  go (w + 1) 0 (w + 1)

example : unpair (pair 3 5) = (3, 5) := by decide

/-- Machine-word view of a value (odd: integers, as in the binary;
pointers/code/atoms: distinct even classes). -/
def enc : Val → BitVec 64
  | .int n => tag64 n
  | .ptr l k => BitVec.ofNat 64 (16 * pair l k)
  | .code pc => BitVec.ofNat 64 (16 * pc + 2)
  | .atom t => BitVec.ofNat 64 (16 * t + 4)
  | .raw w => w

/-- The word at word-address `w`. -/
def wordAt (s : St) (w : Nat) : BitVec 64 :=
  let (r, i) := unpair w
  if r = 0 then
    (s.stack.reverse[i]?.map enc).getD 0
  else match s.heap.get? (r - 1) with
    | some (.block _ fs) => (fs[i]?.map enc).getD 0
    | some (.double d) => if i = 0 then d else 0
    | some (.doubleArray ds) => ds[i]?.getD 0
    | some (.int64 n) | some (.nativeint n) => if i = 0 then n else 0
    | some (.int32 n) => if i = 0 then n.zeroExtend 64 else 0
    | some (.bytes b) =>
        BitVec.ofNat 64 ((List.range 8).foldr (fun k a => a * 256 + (b[8 * i + k]?.map UInt8.toNat).getD 0) 0)
    | _ => 0

/-- `BcSem` of program `P` as an abstract ISA model. -/
def bcModel (P : Prog) : VsaIris.MachineModel where
  State := St
  step s := match step P s with
    | .next s' => .next s'
    | .halt e w => .halt e (bytesToString w.console)
    | .unsupported | .wrong => .stuck
  reg s
    | 0 => BitVec.ofNat 64 s.pc
    | 1 => enc s.accu
    | 2 => enc s.env
    | 3 => BitVec.ofNat 64 s.stack.length
    | 4 => BitVec.ofNat 64 s.extra
    | 5 => BitVec.ofNat 64 s.trap
    | _ => 0
  mem s a := (wordAt s (a / 8)).extractLsb' (8 * (a % 8)) 8
  out s := bytesToString s.world.console

/-- `bcModel`'s lossy outcome map (`unsupported`/`wrong` collapse to `stuck`). -/
def gBc : Res → Option (Nat × String)
  | .halt e w => some (e, bytesToString w.console)
  | _ => none

/-- The lockstep square from `BcSem`'s kernel to `bcModel`'s. -/
theorem bcModel_square (P : Prog) (s : St) :
    Run.mmK (bcModel P) s = Run.mapOut id gBc (bcK P s) := by
  unfold Run.mmK bcK bcModel; dsimp only; cases step P s <;> rfl

/-- `Reaches` of the model is `BcSem`'s `StepsN`. -/
theorem reaches_stepsN {P : Prog} {a b : (bcModel P).State}
    (h : VsaIris.Reaches (bcModel P) a b) : ∃ n, Bytecode.StepsN P n a b := by
  obtain ⟨n, hn⟩ := ((Run.reaches_pres _).iff (Run.mmK_graph _)).1 h
  obtain ⟨c, hc, rfl⟩ := Run.mapOut_ok ((Run.iter_transport id gBc (bcModel_square P) n a).symm.trans hn)
  exact ⟨n, stepsN_iff.2 hc⟩

/-- The model halts exactly as `BcSem` does. -/
theorem halts_bcHalts {P : Prog} {e : Nat} {out : String}
    (h : VsaIris.Halts (bcModel P) P.init e out) : BcHalts P out e := by
  obtain ⟨n, hn⟩ := Run.haltsK_iff.1 (Run.mm_halts_iff.1 h)
  obtain ⟨o, ho, hg⟩ := Run.mapOut_error ((Run.iter_transport id gBc (bcModel_square P) n P.init).symm.trans hn)
  cases o <;> cases hg
  exact bcHalts_iff.2 ⟨_, Run.haltsK_iff.2 ⟨n, ho⟩, rfl⟩

open Iris in
/-- **Adequacy of the bytecode program logic.** If the client proves the
total WP of the ZINC loop of `P` from ownership of the initial registers
`mr` and memory `mm` (agreeing with `P.init`) and of the console, then `P`
halts under `BcSem` with an exit and output satisfying `φ`. Proved by
instantiating ship-your-interpreter's `VsaIris.mach_adequacy` with
`bcModel P`. -/
theorem bytecode_adequacy {GF : BundledGFunctors} [VsaIris.MachGpreS GF] (P : Prog)
    (mr : VsaIris.NatMap (BitVec 64)) (mm : VsaIris.NatMap (BitVec 8))
    (hr : VsaIris.RegAgree (bcModel P) mr P.init) (hm : VsaIris.MemAgree (bcModel P) mm P.init)
    (φ : Nat × String → Prop)
    (H : VsaIris.AdequacyHyp GF (bcModel P) mr mm ((bcModel P).out P.init) φ) :
    ∃ e out, BcHalts P out e ∧ φ (e, out) := by
  obtain ⟨e, out, hh, hφ⟩ := VsaIris.mach_adequacy (M := bcModel P) P.init mr mm hr hm trivial φ H
  exact ⟨e, out, halts_bcHalts hh, hφ⟩

/-- The statement of Layer B′'s adequacy as a `Prop` (for PHASES.md's
ledger of statements): proved by `bytecode_adequacy`. -/
def BytecodeLogicAdequacy : Prop :=
  ∀ (P : Prog) (mr : VsaIris.NatMap (BitVec 64)) (mm : VsaIris.NatMap (BitVec 8)),
    VsaIris.RegAgree (bcModel P) mr P.init → VsaIris.MemAgree (bcModel P) mm P.init →
    ∀ φ : Nat × String → Prop,
      VsaIris.AdequacyHyp VsaIris.MachGF (bcModel P) mr mm ((bcModel P).out P.init) φ →
      ∃ e out, BcHalts P out e ∧ φ (e, out)

theorem bytecodeLogicAdequacy : BytecodeLogicAdequacy :=
  fun P mr mm hr hm φ H => bytecode_adequacy (GF := VsaIris.MachGF) P mr mm hr hm φ H

end OCaml.Logic
