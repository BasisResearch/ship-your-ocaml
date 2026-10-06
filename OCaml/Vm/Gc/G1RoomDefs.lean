import OCaml.Budget
import OCaml.Vm.RuntimeFields

/-! G1 room: definitions, low enough for the loop-head witness (`Running`).
Lemmas: `G1Room.lean` (capacity) and `G1RoomTransport.lean` (preservation). -/

namespace OCaml.Vm.Gc
open OCaml.Bytecode Vsa.Machine

/-- The F1 budget. `stackWords`: `Stack_size - Stack_threshold` = 4096 − 256
words (`config.h`, `stacks.c:caml_init_stack`), so a stack within budget stays
above `stack_threshold`. `heapWords`: the pinned image's nursery is 2 MB
(`young_alloc_start` 0x80082000, `young_alloc_end` 0x80282000) with 800 bytes
taken at the cut (`young_ptr` 0x80281ce0), leaving 262,044 words. The budget
counts all `BcSem` heap words, the initial heap included, so it is conservative. -/
def g1Budget : Budget := ⟨3840, 262044⟩

/-- **G1 room**: the nursery between `young_limit` and `young_ptr` holds every
word the budget still allows.
Allocation sites that `BcSem` counts must move `young_ptr` down by at most
the words they add (`G1Room.step`). -/
structure G1Room (B : Budget) (s : St) (c : Config) : Prop where
  nursery : (runtimeFields c).youngLimit + 8 * (B.heapWords - s.heap.words) ≤ (runtimeFields c).youngPtr

end OCaml.Vm.Gc
