import OCaml
import VsaIris.Adequacy

/-!
# Held-out pilot suite, abstraction-discovery round 1

Cases nobody has proved, from the three target clusters (census:
`abstractions/ROUND-1.md`). Each is a `Prop`; a bake-off entrant proves all
of them (plus the three refactors listed in ROUND-1.md) with its
abstraction, and is measured on lines, wall time and failed attempts.
Nothing here is proved; this file only fixes the targets.
-/

namespace OCaml.Pilot

open OCaml.Bytecode OCaml.Vm

/-! ## C1 run-algebra (new relations) -/

/-- H1: halting is unique for ANY `VsaIris.MachineModel` (the Iris layer has
no such lemma; `Vsa.Machine.Halts.deterministic` is its twin for `Config`). -/
def H1 : Prop :=
  ∀ (M : VsaIris.MachineModel) (σ : M.State) (e e' : Nat) (out out' : String),
    VsaIris.Halts M σ e out → VsaIris.Halts M σ e' out' → e = e' ∧ out = out'

/-- H2: the Iris layer's `Reaches` is "some number of steps". -/
def H2 : Prop :=
  ∀ (M : VsaIris.MachineModel) (a b : M.State),
    VsaIris.Reaches M a b ↔ ∃ n, VsaIris.ReachesN M n a b

/-- H3: a `Good` bytecode program diverges iff it does not halt. -/
def H3 : Prop := ∀ P, Good P → (BcDiverges P ↔ ¬ ∃ out e, BcHalts P out e)

/-- H4: the machine, when it is never stuck, diverges iff it does not halt. -/
def H4 : Prop :=
  ∀ c : Vsa.Machine.Config,
    (∀ c', Vsa.Machine.Steps c c' →
      (∃ c'', Vsa.Machine.Step c' c'') ∨ ∃ e σ, Vsa.Machine.Halted c' e σ) →
    (Vsa.Machine.Diverges c ↔ ¬ ∃ out e, Vsa.Machine.Halts c out e)

/-! ## C3 moving-GC representation (relocation of live blocks) -/

/-- A relocation `μ` of block addresses: every placed block moves to `μ a`. -/
def reloc (μ : Nat → Nat) (pl : Place) : Place := { pl with φ := fun l => (pl.φ l).map μ }

/-- H5: relocation moves exactly the heap pointers. -/
def H5 : Prop :=
  ∀ (pl : Place) (μ : Nat → Nat),
    (∀ l k a, pl.φ l = some a →
      valWord (reloc μ pl) (.ptr l k) = some (BitVec.ofNat 64 (μ a + 8 * k))) ∧
    (∀ v, v.loc? = none → valWord (reloc μ pl) v = valWord pl v)

/-- H6: an object is laid out at its new address once its header is copied,
its fields hold the relocated values, and a non-structured payload is
copied byte for byte. -/
def H6 : Prop :=
  ∀ (c c' : Vsa.Machine.Config) (pl : Place) (cp : ChanPlace) (μ : Nat → Nat) (a : Nat) (o : Obj),
    ObjAt c pl cp a o →
    8 ≤ μ a →
    word c' (μ a - 8) = word c (a - 8) →
    (∀ t fs, o = .block t fs → ∀ i v, fs[i]? = some v →
      valWord (reloc μ pl) v = some (word c' (μ a + 8 * i))) →
    ((∀ t fs, o ≠ .block t fs) → ∀ j, j < 8 * o.wosize + 8 → byte c' (μ a + j) = byte c (a + j)) →
    ObjAt c' (reloc μ pl) cp (μ a) o

/-- H7: the VM stack after relocation. -/
def H7 : Prop :=
  ∀ (c c' : Vsa.Machine.Config) (pl : Place) (μ : Nat → Nat) (sp high : Nat) (stk : List Val),
    StackRepr c pl sp high stk →
    (∀ i v, stk[i]? = some v → valWord (reloc μ pl) v = some (word c' (sp + 8 * i))) →
    StackRepr c' (reloc μ pl) sp high stk

/-! ## C4 Layer B′: bytecode segment specifications -/

/-- Encode instructions as code words (opcode, then operands). -/
def enc (is : List (Opcode × List Int)) : Code :=
  (is.flatMap fun (o, args) => BitVec.ofNat 32 o.toNat :: args.map (BitVec.ofInt 32)).toArray

/-- `CONSTINT 40; PUSH; CONST2; ADDINT; STOP` (words 0,2,3,4,5). -/
def segP : Prog :=
  ⟨enc [(.CONSTINT, [40]), (.PUSH, []), (.CONST2, []), (.ADDINT, []), (.STOP, [])],
   #[], ⟨[]⟩, .atom 0, [], .atom 0, []⟩

/-- H8: from ANY state at word 0, four steps give `accu = 42` and leave the
stack as it was (symbolic in everything but the code). -/
def H8 : Prop :=
  ∀ s : St, s.pc = 0 → ∃ s', StepsN segP 4 s s' ∧ s'.pc = 5 ∧ s'.accu = .int 42 ∧ s'.stack = s.stack

/-- A counting loop on the stack top: `while i < 10 do i := i + 1 done; accu := i`.
  0 ACC0 · 1 BLEINT 10 → 11 · 4 ACC0 · 5 OFFSETINT 1 · 7 ASSIGN 0 · 9 BRANCH → 0 · 11 ACC0 · 12 STOP -/
def loopP : Prog :=
  ⟨enc [(.ACC0, []), (.BLEINT, [10, 8]), (.ACC0, []), (.OFFSETINT, [1]), (.ASSIGN, [0]),
        (.BRANCH, [-10]), (.ACC0, []), (.STOP, [])],
   #[], ⟨[]⟩, .atom 0, [], .atom 0, []⟩

/-- H9: from `i = n ≤ 10` on the stack top, the loop reaches `STOP` with
`accu = 10`. -/
def H9 : Prop :=
  ∀ (n : Nat) (rest : List Val) (s : St), n ≤ 10 → s.pc = 0 → s.stack = .int (BitVec.ofNat 63 n) :: rest →
    ∃ k s', StepsN loopP k s s' ∧ s'.pc = 12 ∧ s'.accu = .int 10

/-! Sanity: the programs run as intended (evaluation, not proof of H8/H9). -/
example : (runTo segP 10 segP.init).isSome = true := by decide +kernel
example : ((runTo loopP 200 { loopP.init with stack := [.int 3] }).map (·.1)) = some 0 := by
  decide +kernel

end OCaml.Pilot
