# Routes not to repeat

- 2026-10-21: `ulimit -v 12582912` prevents Lean thread/import initialization
  in large closures, even at low RSS and with two threads. Use the actual
  aggregate `MemoryMax=12G` cgroup cap without a virtual-address limit.
- `OpenOutRuntime.budget` quantified over every `runtimeOk` configuration
  cannot follow from that invariant: it does not bound prior custom calls.
  Supply the budget at a successful C_CALL from `Fits` and represented counts.
- `BarrierGrowthFull` cannot preserve G1 quietness on a full table: overflow
  requests a minor GC. Standing decision: discharge via G2, retain its premise.
- C4 hand-proof expansion triggered the abstraction gate. Preserve the draft;
  the approved discovery round 2 waits until F1 is closed.
- Named-value WIP's ASCII-only node predicate is stronger than current
  `GoodF1`, whose primitive accepts arbitrary bytes. Generalize the byte/string
  bridge; do not silently impose an ASCII guard or claim general refinement.
- `CustomMemCall` returning `Ready k` alone does not establish exact counter
  increment. A named counter-transition post is needed for n-to-n+1 accounting.
