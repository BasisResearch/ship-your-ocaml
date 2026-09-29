import OCaml.Refinement
import OCaml.Source.Lambda

/-!
# Layer C and the composed theorem (statements; composition proved)

The plan (README.md): give `ocamlc` a formal meaning at the SOURCE level,
prove its back half correct there, and connect the source-level compiler to
the bytes of `boot/ocamlc` by ONE translation validation — the bootstrap
fixpoint (`boot/ocamlc` is the compiler's sources compiled by itself; for
4.14.4 VALIDATION.md §Fixpoint checks this on the host: CODE, PRIM, SYMB and
CRCS are byte-identical, DATA differs only in `configure`'s install paths).

Everything here is parametric in the source semantics `S` (the LLM-written
`OCamlSem`, on Lambda first) and in the trusted front end `parse`. The three
obligations are `Prop`s, not axioms:

* `BackendCorrect S ocamlc parse` — **Layer C proper**: whenever the
  compiler (the program `ocamlc` of `S`: its own sources, meaning given by
  `S`) compiles a source text `src` to an executable, the executable's
  `BcSem` behaviours are exactly `S`'s behaviours of `parse src`.
  (`ocamlc_backend_correct`: proved with a program logic over `S`.)
* `SelfCompiles S ocamlc boot` — **the bootstrap fixpoint**: under `S`, the
  compiler compiling its own sources outputs exactly the bytes `boot`
  (`boot_ocamlc_fixpoint`: one run, validated once).
* `OcamlrunRefinement L B` — Layer A (`OCaml/Refinement.lean`).

`boot_meaning` (proved): from the first two, `BcSem` of the bytes `boot`
IS the source compiler: on every input the bytecode `boot/ocamlc` behaves
as `ocamlc`'s sources say.

`endToEnd_ocaml` (proved from the three): run `boot/ocamlc` under `BcSem`
on `src`; if it writes an executable, the bare-metal `ocamlrun` running
that executable halts with `(out, e)` iff `parse src` has behaviour
`(out, e)` under `S`, and diverges iff `S` says so (within the fragment and
budget). The remaining machine-level strengthening — running `boot/ocamlc`
itself on the machine rather than under `BcSem` — is Layer A applied to
`boot/ocamlc`, once `WorldRepr` covers the file system (F5); it is stated
as `EndToEndMachine`.
-/

namespace OCaml

open OCaml.Bytecode Vsa.Machine

abbrev Files := List (String × List UInt8)

def lookupFile (fs : Files) (p : String) : Option (List UInt8) := (fs.find? (·.1 == p)).map (·.2)

/-- A source-level semantics of whole programs with argv and files:
`Run p argv fs out e fs'` — `p` run with command line `argv` on files `fs`
prints `out`, exits `e`, leaving files `fs'`; `Div p argv fs` — it runs
forever. -/
structure SourceSem where
  Program : Type
  Run : Program → List String → Files → String → Nat → Files → Prop
  Div : Program → List String → Files → Prop

/-- How an executable's bytes become a `Prog` at the cut point, for a
command line and initial files (`loadExe` in `Load.lean` is one executable
model of it; the statements take it as a parameter). -/
abbrev Loader := List UInt8 → List String → Files → Option Prog

/-- The `ocamlc` command line compiling `/src/main.ml` to `/out/a.out`. -/
def compileArgv : List String := ["-o", "/out/a.out", "/src/main.ml"]

def srcFiles (src : List UInt8) : Files := [("/src/main.ml", src)]

/-- **Layer C: the back half of `ocamlc` is correct (statement).** For every
source text `src` the trusted front end accepts, if the compiler run on it
(under `S`) produces `/out/a.out = b`, then the loaded `b` behaves exactly as
`parse src` under `S`, for every command line and file system. -/
def BackendCorrect (S : SourceSem) (ocamlc : S.Program) (parse : List UInt8 → Option S.Program)
    (load : Loader) : Prop :=
  ∀ src sp out fs' b, parse src = some sp →
    S.Run ocamlc compileArgv (srcFiles src) out 0 fs' → lookupFile fs' "/out/a.out" = some b →
    ∀ argv fs P, load b argv fs = some P →
      (∀ o e fs'', BcRun P o e fs'' ↔ S.Run sp argv fs o e fs'') ∧
      (BcDiverges P ↔ S.Div sp argv fs)

/-- The command line that rebuilds the compiler from its sources, and the
sources (as files); instantiated from the 4.14.4 build (`boot/ocamlc`'s own
link command). -/
structure Bootstrap where
  argv : List String
  sources : Files
  output : String
  /-- the compiler's sources parse to the program `ocamlc` of `S` -/
  compilerSource : List UInt8

/-- **The bootstrap fixpoint (statement).** Under `S`, the compiler run on
its own sources writes exactly `boot`. -/
def SelfCompiles (S : SourceSem) (ocamlc : S.Program) (bs : Bootstrap) (boot : List UInt8) : Prop :=
  ∃ out fs', S.Run ocamlc bs.argv bs.sources out 0 fs' ∧ lookupFile fs' bs.output = some boot

/-- What the bytes of `boot/ocamlc` mean, as a statement: on every input,
`BcSem` of the loaded bytes behaves as the source compiler. -/
def BootMeaning (S : SourceSem) (ocamlc : S.Program) (load : Loader) (boot : List UInt8) : Prop :=
  ∀ argv fs P, load boot argv fs = some P →
    (∀ o e fs', BcRun P o e fs' ↔ S.Run ocamlc argv fs o e fs') ∧
    (BcDiverges P ↔ S.Div ocamlc argv fs)

/-- Backend correctness at a general command line: the compiler's own build
is a compilation like any other. Stated separately because `BackendCorrect`
fixes `compileArgv` (one source file) and the bootstrap compiles many. -/
def BackendCorrectFor (S : SourceSem) (ocamlc : S.Program) (load : Loader)
    (argv : List String) (srcs : Files) (output : String) (sp : S.Program) : Prop :=
  ∀ out fs' b, S.Run ocamlc argv srcs out 0 fs' → lookupFile fs' output = some b →
    ∀ argv' fs P, load b argv' fs = some P →
      (∀ o e fs'', BcRun P o e fs'' ↔ S.Run sp argv' fs o e fs'') ∧
      (BcDiverges P ↔ S.Div sp argv' fs)

/-- **`boot/ocamlc` means the compiler (proved):** backend correctness for
the compiler's own build, plus the fixpoint, give the meaning of the bytes. -/
theorem boot_meaning {S : SourceSem} {ocamlc : S.Program} {load : Loader} {bs : Bootstrap}
    {boot : List UInt8}
    (hC : BackendCorrectFor S ocamlc load bs.argv bs.sources bs.output ocamlc)
    (hF : SelfCompiles S ocamlc bs boot) : BootMeaning S ocamlc load boot := by
  obtain ⟨out, fs', hrun, hout⟩ := hF
  exact fun argv fs P hl => hC out fs' boot hrun hout argv fs P hl

/-- **The composed end-to-end statement.** Running the bytes of
`boot/ocamlc` (under `BcSem`) on `src` produces an executable `b`; the
bare-metal `ocamlrun` running `b` halts with `(out, e)` iff the source
program does, and diverges iff it does. -/
def EndToEnd (S : SourceSem) (parse : List UInt8 → Option S.Program) (load : Loader)
    (boot : List UInt8) (L : Layout) (B : Budget) : Prop :=
  ∀ src sp Pc out fs' b P c,
    parse src = some sp →
    load boot compileArgv (srcFiles src) = some Pc →
    BcRun Pc out 0 fs' → lookupFile fs' "/out/a.out" = some b →
    load b [] [] = some P → Loaded L P c → Good P → Fits B P →
      (∀ o e, (∃ fs'', S.Run sp [] [] o e fs'') ↔ Halts c o e) ∧
      (S.Div sp [] [] ↔ Diverges c)

/-- **End-to-end (proved from the three obligations).** -/
theorem endToEnd_ocaml {S : SourceSem} {ocamlc : S.Program}
    {parse : List UInt8 → Option S.Program} {load : Loader} {bs : Bootstrap}
    {boot : List UInt8} {L : Layout} {B : Budget}
    (hA : OcamlrunRefinement L B)
    (hC : BackendCorrect S ocamlc parse load)
    (hCself : BackendCorrectFor S ocamlc load bs.argv bs.sources bs.output ocamlc)
    (hF : SelfCompiles S ocamlc bs boot) :
    EndToEnd S parse load boot L B := by
  intro src sp Pc out fs' b P c hp hlc hrun hb hl hL hg hf
  have hM := boot_meaning hCself hF
  -- the compile run, read at the source level
  have hsrc : S.Run ocamlc compileArgv (srcFiles src) out 0 fs' :=
    ((hM compileArgv (srcFiles src) Pc hlc).1 out 0 fs').1 hrun
  obtain ⟨hbeh, hdiv⟩ := hC src sp out fs' b hp hsrc hb [] [] P hl
  obtain ⟨hA1, hA2⟩ := hA P c hL hg hf
  refine ⟨fun o e => ⟨fun ⟨fs'', h⟩ => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact (hA1 o e).1 (BcRun.halts ((hbeh o e fs'').2 h))
  · obtain ⟨fs'', hr⟩ := ((hA1 o e).2 h).run
    exact ⟨fs'', (hbeh o e fs'').1 hr⟩
  · exact hA2.1 (hdiv.2 h)
  · exact hdiv.1 (hA2.2 h)

/-- The machine-level strengthening (statement): `boot/ocamlc` itself runs
on the bare-metal `ocamlrun` (not under `BcSem`) and writes `b` into the
in-memory file system. Needs Layer A with files (`WorldRepr` over F5). -/
def EndToEndMachine (S : SourceSem) (parse : List UInt8 → Option S.Program) (load : Loader)
    (boot : List UInt8) (L : Layout) (B : Budget)
    (Written : Config → String → List UInt8 → Prop) : Prop :=
  ∀ src sp Pc cc out b P c,
    parse src = some sp → load boot compileArgv (srcFiles src) = some Pc →
    Loaded L Pc cc → Halts cc out 0 → Written cc "/out/a.out" b →
    load b [] [] = some P → Loaded L P c → Good P → Fits B P →
      (∀ o e, (∃ fs'', S.Run sp [] [] o e fs'') ↔ Halts c o e) ∧
      (S.Div sp [] [] ↔ Diverges c)

end OCaml
