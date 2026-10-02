import OCaml.Bytecode.Semantics
import OCaml.Bytecode.MarshalIn

/-!
# Loading a bytecode executable into a `Prog` (executable model of the
cut-point state)

What `caml_main` does before calling `caml_interprete`: read CODE and PRIM,
unmarshal DATA (`caml_input_val`, `runtime/intern.c`) into the heap, and set
`caml_global_data` to the result. This file transcribes the unmarshaller
for the codes that occur in executables' global data, allocating objects in
`intern.c`'s `obj_counter` order, so `SHARED` back-references are location
arithmetic.

This is an EXECUTABLE model, used to run `BcSem` on real bytecode
(`experiments/RunBc.lean`, VALIDATION.md). It is not part of the trusted
statement: `Loaded` (`OCaml/Refinement.lean`) relates `P.heap0` to the
machine's memory through the representation predicate, whatever produced it.
-/

namespace OCaml.Bytecode

def strBytes (s : String) : List UInt8 := s.toList.map (·.toNat.toUInt8)

/-- Load a bytecode executable (the file's bytes) as the cut-point `Prog`,
with the command line `src/main.c` bakes in: `caml_exe_name = "/prog"`,
`main_argv = [| "/prog"; args… |]`. -/
def loadExe (f : ByteArray) (args : List String := [])
    (files : List (String × List UInt8) := []) : Option Prog := do
  let code ← sectionBytes f "CODE"
  let prim ← sectionBytes f "PRIM"
  let data ← sectionBytes f "DATA"
  let (g, h) ← unmarshal data ⟨#[]⟩
  let (h, ls) := ("/prog" :: args).foldl (fun (h, ls) a =>
    let (h, l) := h.alloc (.bytes (strBytes a)); (h, ls ++ [Val.ptr l 0])) (h, [])
  let (h, av) := if ls.isEmpty then (h, Val.atom 0) else
    let (h, l) := h.alloc (.block 0 ls); (h, Val.ptr l 0)
  pure ⟨codeOfBytes code, primsOfBytes prim, h, g, strBytes "/prog", av,
    ("/prog", f.toList) :: files, []⟩

/-- A halting run, as a checkable function: `runTo P k s = some (e, w)` if
`s` halts with `(e, w)` within `k` steps. -/
def runTo (P : Prog) : Nat → St → Option (Nat × World)
  | 0, _ => none
  | k + 1, s => match step P s with
    | .next s' => runTo P k s'
    | .halt e w => some (e, w)
    | _ => none

theorem runTo_sound (P : Prog) :
    ∀ k s, Reach P s → ∀ e w, runTo P k s = some (e, w) →
      ∃ s', Reach P s' ∧ step P s' = .halt e w := by
  intro k
  induction k with
  | zero => intro s _ e w h; simp [runTo] at h
  | succ k ih =>
    intro s hr e w h
    simp only [runTo] at h
    split at h
    · rename_i s' hs
      obtain ⟨n, hn⟩ := hr
      exact ih s' ⟨n + 1, hn.snoc (.mk hs)⟩ e w h
    · rename_i e' w' hs
      cases h; exact ⟨s, hr, hs⟩
    · cases h

/-- **Checked runs are behaviours**: if `runTo` halts from the initial
state, `BcSem` halts with that output and exit code. -/
theorem bcHalts_of_runTo {P : Prog} {k : Nat} {e : Nat} {w : World}
    (h : runTo P k P.init = some (e, w)) : BcHalts P (bytesToString w.console) e := by
  obtain ⟨s, hr, hs⟩ := runTo_sound P k P.init ⟨0, .zero _⟩ e w h
  exact ⟨s, w, hr, hs, rfl⟩

/-- The primitive a `C_CALLn` at `s.pc` calls, for diagnostics. -/
def primNameAt (P : Prog) (pc : Nat) : String :=
  match decodeAt P.code pc with
  | some ⟨.C_CALL1, [p]⟩ | some ⟨.C_CALL2, [p]⟩ | some ⟨.C_CALL3, [p]⟩
  | some ⟨.C_CALL4, [p]⟩ | some ⟨.C_CALL5, [p]⟩ | some ⟨.C_CALLN, [_, p]⟩ =>
      P.prims[p.toNat]?.getD "?"
  | _ => ""

/-- Run `BcSem` for at most `fuel` steps (executable; for validation). -/
def run (P : Prog) : Nat → St → Nat → (String × Option Nat × Nat × String)
  | 0, s, n => (bytesToString s.world.console, none, n, s!"fuel out at pc {s.pc}")
  | fuel + 1, s, n =>
    -- Retain only diagnostic scalars/output across step. Keeping s alive
    -- here forces every otherwise-exclusive heap array update to copy.
    let pc := s.pc
    let output := s.world.console
    match step P s with
    | .next s' => run P fuel s' (n + 1)
    | .halt e w => (bytesToString w.console, some e, n, "halt")
    | .unsupported =>
      (bytesToString output, none, n,
        s!"unsupported at pc {pc}: {repr ((decodeAt P.code pc).map (·.op))} {primNameAt P pc}")
    | .wrong => (bytesToString output, none, n,
        s!"wrong at pc {pc}: {repr ((decodeAt P.code pc).map (·.op))}")

/-- Validation runner retaining final filesystem state for compiler difftests.
Only the world and diagnostic PC survive each step, allowing exclusive heap
updates in the compiled evaluator. -/
def runWorld (P : Prog) : Nat → St → Nat → List String → (World × Option Nat × Nat × String)
  | 0, s, n, _ => (s.world, none, n, s!"fuel out at pc {s.pc}")
  | fuel + 1, s, n, seen =>
    let pc := s.pc
    let world := s.world
    let primitive := primNameAt P pc
    let seen := if primitive = "" ∨ primitive ∈ seen then seen else primitive :: seen
    match step P s with
    | .next s' => runWorld P fuel s' (n + 1) seen
    | .halt e w => (w, some e, n, "halt primitives " ++ reprStr seen.reverse)
    | .unsupported => (world, none, n, s!"unsupported at pc {pc}: {primNameAt P pc}")
    | .wrong => (world, none, n, s!"wrong at pc {pc}: {repr ((decodeAt P.code pc).map (·.op))}")

end OCaml.Bytecode
