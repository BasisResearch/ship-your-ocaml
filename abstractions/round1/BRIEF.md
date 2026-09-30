# Brief for the round-1 ontologists (blind: semantics, census, laws only)

You are designing proof abstractions for a Lean 4 verification project. You
must NOT read any file of the project; everything you need is here.

## The semantics

* **A machine** (RISC-V, as a Lean model): a configuration steps
  deterministically by a total function `stepOnce : Config → Next Config |
  Halt (code, output) | Error`. Programs are ELF binaries in its byte memory.
* **A bytecode VM semantics** `BcSem`: a deterministic step function
  `step : Prog → St → Next St | Halt code world | Unsupported | Wrong` over
  states `St = {pc, accu, stack : List Val, env, extra, trap, heap, world}`.
  `Val = int (63-bit) | ptr loc offset | code pc | atom tag | raw word`.
  The heap is a list of objects (blocks with tag and fields, byte strings,
  doubles, channels); allocation appends, nothing is freed or moved. Each
  instruction is a small function of the state: read some stack slots /
  fields, write the accumulator, push/pop, allocate one block, jump.
* **A representation relation** linking a VM state to machine memory at the
  interpreter's loop head: registers hold pc/sp/accu/env; each VM value is a
  machine word (ints tagged `2n+1`, pointers `address + 8k`); each live block
  sits at `placement(loc)` with a header word and its fields; the VM stack is
  a region of machine memory; placement is existentially quantified.
* **The machine's garbage collector** is a copying minor collector: it moves
  every live young block to a new address, rewrites every pointer to it, and
  leaves everything else. The abstract VM heap never changes during a
  collection.
* **A generic "machine as Iris language" layer**: any deterministic step
  function presented as a machine model gets a weakest-precondition calculus
  and a proved adequacy theorem.

## The obligation census (hand proofs, shape-clustered)

| cluster | members so far | per-case cost | trend |
|---|---|---|---|
| C1 run-algebra: determinism, prefix/append/snoc of n-step runs, halting is unique, halting excludes divergence, halts-or-diverges-or-sticks, converting between closure relations — re-proved for every step relation (machine, bytecode VM, the generic machine model, the OS spec) | 31 | 8.6 lines, flat (first quarter 8.6, last 8.6) | FLAT: gate fired |
| C2 checker soundness: an executable runner/checker is sound or complete for the relation it computes | 7 | 4–20 lines | growing |
| C3 moving-GC representation: every component of the representation (value words, object layout for 8 object kinds, stack region, heap disjointness, channels, the 15 fields of the loop-head relation) must survive a collection that relocates blocks | 0 proved, ~40 upcoming | — | target |
| C4 bytecode specifications (Layer B′): specifications of bytecode segments and loops, first for small programs, eventually for a 412,087-instruction compiler | 0 proved, huge | — | target |

## The laws (each checked for counterexamples)

* **L1** (C1): *the n-step relation of a deterministic step function is the
  graph of its fuel-bounded iterate*; every C1 fact is a corollary.
  Checked on 20,000 random finite systems: 0 counterexamples.
* **L3** (C3): *every representation predicate is invariant under a
  relocation that moves each live block, as a whole, to a new address range,
  with the target ranges pairwise disjoint, rewriting pointer words through
  the relocation and copying all other words*. Checked on 20,000 random
  heaps: 0 counterexamples; with overlapping targets 12,358 counterexamples
  (disjointness is necessary).
* **L4** (C4): *a bytecode step is local*: it reads a bounded footprint (pc,
  code, the top few stack slots, the fields it touches) and leaves the rest
  of the state unchanged. Checked on 78,855 perturbed steps of real runs: 0
  violations.

## Forbidden vocabulary (the current encoding's primitives — do not propose these)

`StepsN`, `Steps`, `ReachesN`, `Triple`/`TripleN` (pre/post over configurations
with a step count), `segToTriple`, per-site step lemmas, `VmReprAt`, `Place`,
`valWord`, `ObjAt`, `HeapRepr`, `StackRepr`, generated per-instruction decode
lemmas, per-arm simulation obligations. Tools (SMT, model checking, fuzzing,
Houdini) are not abstractions: they may only check laws.

## Output contract

Return 5 candidate abstractions. For each: a name; the idea (what the proofs
would be written in instead); its core RULES (the laws above must become
proved rules of it, used everywhere); what it makes free and what it costs;
at least two theories from distant fields it draws on (databases,
concurrency, compilers, category theory, economics, physics, …); which
cluster(s) it targets; and a concrete pilot on this held-out suite (Lean 4
statements, stated in the vocabulary above only for the pilot's sake):

* H1: halting is unique for any deterministic step function presented as a
  machine model; H2: "reaches" equals "reaches in some n steps"; H3: a
  never-wrong VM program diverges iff it does not halt; H4: a never-stuck
  machine diverges iff it does not halt.
* H5–H7: relocation of live blocks preserves the value encoding, an
  object's layout, and the stack region.
* H8: from ANY VM state at pc 0 of `CONSTINT 40; PUSH; CONST2; ADDINT;
  STOP`, four steps give accumulator 42 with the stack unchanged; H9: a
  counting loop on the stack top reaches STOP with accumulator 10 from any
  start i ≤ 10.
* plus refactoring three existing proof blocks: the VM's run-determinism
  block, the machine's run-composition lemmas, and a conversion between the
  generic machine model's reachability and the VM's n-step relation.

Prefer depth and specificity over safe coverage.
