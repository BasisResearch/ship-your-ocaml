import OCaml.Vm.Gc.G1RoomDefs
import OCaml.Vm.Sim.ArmGeometry

/-! Preserving the G1 room across arms: allocation (`step`, `reserve`) and
non-allocating write logs (`frame`, `same`), below the arms' restore sites. -/

namespace OCaml.Vm.Gc
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- A step that adds `s'.heap.words - s.heap.words` words moves `young_ptr`
down by at most that many words (none, when it does not allocate in the
nursery) and leaves the limit and stack geometry alone. -/
theorem G1Room.step {B : Budget} {s s' : St} {c c' : Config} (room : G1Room B s c)
    (grow : s.heap.words ≤ s'.heap.words) (fits : s'.heap.words ≤ B.heapWords)
    (ptr : (runtimeFields c).youngPtr ≤ (runtimeFields c').youngPtr + 8 * (s'.heap.words - s.heap.words))
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit) :
    G1Room B s' c' := by
  have nursery := room.nursery
  constructor
  rw [limit]
  omega

/-- The nursery reservation of `Sim.NurseryInput` (`young_ptr` from
`a + 8 * count` down to `a - 8`, i.e. `count + 1` words) preserves the room
when `BcSem` adds those `count + 1` words. -/
theorem G1Room.reserve {B : Budget} {s s' : St} {c c' : Config} (room : G1Room B s c)
    {count a : Nat}
    (before : (runtimeFields c).youngPtr = a + 8 * count)
    (after : (runtimeFields c').youngPtr = a - 8) (low : 8 ≤ a)
    (words : s'.heap.words = s.heap.words + (count + 1)) (fits : s'.heap.words ≤ B.heapWords)
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit) :
    G1Room B s' c' :=
  room.step (by omega) fits (by rw [before, after, words]; omega) limit

/-- **Non-allocating arms**: a log missing the `Caml_state` pointer and the
`young_limit`/`young_ptr` words (`Sim.YoungOutside`) keeps the room, as long
as the heap does not shrink (allocation-free `BcSem` steps keep or grow it). -/
theorem G1Room.frame {B : Budget} {s s' : St} {c c' : Config} {log : List WEntry}
    (room : G1Room B s c) (young : Sim.YoungOutside log c)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (memory : c'.σ.mem = writeLog c.σ.mem log) (words : s.heap.words ≤ s'.heap.words) :
    G1Room B s' c' := by
  have keep : ∀ x, OutLRange log x 8 → word c' x = word c x := fun x h => by
    change bytesT c'.σ.mem x 8 = bytesT c.σ.mem x 8
    rw [memory, OCaml.Vm.Primitives.bytesT_writeLog_out _ h]
  have dom := keep _ domain
  have ptr : (runtimeFields c').youngPtr = (runtimeFields c).youngPtr := by
    simp only [runtimeFields, domainWord, dom]; rw [keep _ young.ptr]
  have limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit := by
    simp only [runtimeFields, domainWord, dom]; rw [keep _ young.limit]
  have nursery := room.nursery
  constructor
  rw [ptr, limit]
  omega

/-- Same memory, heap not shrunk. -/
theorem G1Room.same {B : Budget} {s s' : St} {c c' : Config} (room : G1Room B s c)
    (memory : c'.σ.mem = c.σ.mem) (words : s.heap.words ≤ s'.heap.words) : G1Room B s' c' := by
  have fields : runtimeFields c' = runtimeFields c := by simp only [runtimeFields, domainWord, word, word32, memory]
  have nursery := room.nursery
  constructor
  rw [fields]
  omega

end OCaml.Vm.Gc
