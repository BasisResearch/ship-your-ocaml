import OCaml.Programs.WhileMin

/-!
# `BcSem` on a real executable, kernel-checked

`whileMin` is `c/tests/nostdlib/while_min.ml` — `c/tests/while.ml` (the OCaml
port of ship-your-interpreter's `while.wl`) without the Stdlib, printing
through the channel primitives directly — compiled by the host 4.14.2
`ocamlc -nopervasives -nostdlib` and loaded as `caml_main` loads it
(`OCaml/Bytecode/Load.lean`, generated literal in `WhileMin.lean`). The
bare-metal ELF running the same bytecode prints `55\n2500\n36\n` and exits
0 on the Sail model (VALIDATION.md); so does `BcSem`, by evaluation in the
kernel (`decide +kernel`, no `native_decide`): 2,161 ZINC steps.

(The Stdlib-linked `while.ml` also runs to the same output under `BcSem`,
2,602 steps, but only in compiled code (`runbc`): the kernel keeps no
sharing between steps, and its Stdlib-initialised heap exhausts 30 GB
within ~100 steps. A chunked proof over explicit intermediate states is
PHASES.md A1's exit criterion.)
-/

namespace OCaml.Programs
open OCaml.Bytecode

set_option maxRecDepth 100000 in
theorem whileMin_runTo :
    (runTo whileMin 2200 whileMin.init).map (fun r => (r.1, bytesToString r.2.console)) =
      some (0, "55\n2500\n36\n") := by
  decide +kernel

/-- **`BcSem` halts on `while_min.byte` with the binary's output.** -/
theorem whileMin_bcSem : BcHalts whileMin "55\n2500\n36\n" 0 := by
  have h := whileMin_runTo
  match hr : runTo whileMin 2200 whileMin.init, h with
  | some (e, w), h =>
    simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, hw⟩ := h
    exact hw ▸ bcHalts_of_runTo hr

end OCaml.Programs
