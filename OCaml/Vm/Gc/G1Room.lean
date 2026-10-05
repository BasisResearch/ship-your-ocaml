import OCaml.Vm.Runtime

/-!
# G1: the allocation fast path never reaches the limit

Under G1 (PLAN.md §GC strategy) no minor collection happens after the cut:
`Fits B P` bounds `s.heap.words`, and the machine's remaining nursery covers
what the budget still allows. `G1Room` is that relation between a `BcSem`
state and a machine configuration. An allocating arm consumes it through
`G1Room.nursery_capacity` (the `capacity` field of `Sim.NurseryInput`) and
re-establishes it through `G1Room.step`; `G1Room.stack_capacity` gives the
`stack_threshold` check of `Sim.EnterReady`, so `caml_realloc_stack` never runs.
-/

namespace OCaml.Vm.Gc
open OCaml.Bytecode Vsa.Machine

/-- `Caml_state->stack_threshold`, as read by the interpreter's stack check. -/
def stackThreshold (c : Config) : Nat := domainWord c Layout.off_stack_threshold

/-- `Caml_state->stack_high`, the top of the VM stack. -/
def stackHigh (c : Config) : Nat := domainWord c Layout.off_stack_high

/-- The F1 budget. `stackWords`: `Stack_size - Stack_threshold` = 4096 − 256
words (`config.h`, `stacks.c:caml_init_stack`), so a stack within budget stays
above `stack_threshold`. `heapWords`: the pinned image's nursery is 2 MB
(`young_alloc_start` 0x80082000, `young_alloc_end` 0x80282000) with 800 bytes
taken at the cut (`young_ptr` 0x80281ce0), leaving 262,044 words. The budget
counts all `BcSem` heap words, the initial heap included, so it is conservative. -/
def g1Budget : Budget := ⟨3840, 262044⟩

/-- **G1 room**: the nursery between `young_limit` and `young_ptr` holds every
word the budget still allows, and the budgeted stack fits above the threshold.
Allocation sites that `BcSem` counts must move `young_ptr` down by at most
the words they add (`G1Room.step`). -/
structure G1Room (B : Budget) (s : St) (c : Config) : Prop where
  nursery : (runtimeFields c).youngLimit + 8 * (B.heapWords - s.heap.words) ≤ (runtimeFields c).youngPtr
  stack : stackThreshold c + 8 * B.stackWords ≤ stackHigh c

/-- Room for `w` more words whenever the budget allows them. -/
theorem G1Room.alloc_capacity {B : Budget} {s : St} {c : Config} (room : G1Room B s c) {w : Nat}
    (fits : s.heap.words + w ≤ B.heapWords) :
    (runtimeFields c).youngLimit + 8 * w ≤ (runtimeFields c).youngPtr := by
  have := room.nursery
  omega

/-- The `capacity` field of `Sim.NurseryInput`: an arm allocating `count + 1`
words (header included) below `young_ptr = a + 8 * count` stays above
`young_limit`, given that the successor state is within the budget. -/
theorem G1Room.nursery_capacity {B : Budget} {s : St} {c : Config} (room : G1Room B s c)
    {count a domain limit : Nat}
    (domainValue : word c Layout.sym_Caml_state = BitVec.ofNat 64 domain)
    (youngValue : word c (domain + Layout.off_young_ptr) = BitVec.ofNat 64 (a + 8 * count))
    (limitValue : word c (domain + Layout.off_young_limit) = BitVec.ofNat 64 limit)
    (domainRange : domain < 2 ^ 64) (youngRange : a + 8 * count < 2 ^ 64) (limitRange : limit < 2 ^ 64)
    (fits : s.heap.words + (count + 1) ≤ B.heapWords) : limit ≤ a - 8 := by
  have capacity := room.alloc_capacity fits
  have dom : (word c Layout.sym_Caml_state).toNat = domain := by
    rw [domainValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt domainRange]
  have ptr : (runtimeFields c).youngPtr = a + 8 * count := by
    simp only [runtimeFields, domainWord, dom, youngValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt youngRange]
  have lim : (runtimeFields c).youngLimit = limit := by
    simp only [runtimeFields, domainWord, dom, limitValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt limitRange]
  rw [ptr, lim] at capacity
  omega

/-- A step that adds `s'.heap.words - s.heap.words` words moves `young_ptr`
down by at most that many words (none, when it does not allocate in the
nursery) and leaves the limit and stack geometry alone. -/
theorem G1Room.step {B : Budget} {s s' : St} {c c' : Config} (room : G1Room B s c)
    (grow : s.heap.words ≤ s'.heap.words) (fits : s'.heap.words ≤ B.heapWords)
    (ptr : (runtimeFields c).youngPtr ≤ (runtimeFields c').youngPtr + 8 * (s'.heap.words - s.heap.words))
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (threshold : stackThreshold c' = stackThreshold c) (high : stackHigh c' = stackHigh c) :
    G1Room B s' c' := by
  have nursery := room.nursery
  have stack := room.stack
  constructor
  · rw [limit]
    omega
  · rw [threshold, high]
    exact stack

/-- The nursery reservation of `Sim.NurseryInput` (`young_ptr` from
`a + 8 * count` down to `a - 8`, i.e. `count + 1` words) preserves the room
when `BcSem` adds those `count + 1` words. -/
theorem G1Room.reserve {B : Budget} {s s' : St} {c c' : Config} (room : G1Room B s c)
    {count a : Nat}
    (before : (runtimeFields c).youngPtr = a + 8 * count)
    (after : (runtimeFields c').youngPtr = a - 8) (low : 8 ≤ a)
    (words : s'.heap.words = s.heap.words + (count + 1)) (fits : s'.heap.words ≤ B.heapWords)
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (threshold : stackThreshold c' = stackThreshold c) (high : stackHigh c' = stackHigh c) :
    G1Room B s' c' :=
  room.step (by omega) fits (by rw [before, after, words]; omega) limit threshold high

/-- The `stack_threshold` check (`Sim.EnterReady.capacity`) for a represented
stack (`StackRepr`: `sp + 8 * length = stack_high`) within the budget. -/
theorem G1Room.stack_capacity {B : Budget} {s : St} {c : Config} (room : G1Room B s c) {sp len : Nat}
    (repr : sp + 8 * len = stackHigh c) (fits : len ≤ B.stackWords) : stackThreshold c ≤ sp := by
  have := room.stack
  omega

end OCaml.Vm.Gc
