import OCaml.Vm.Primitives.MemoryFrame

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives Reloc

/-- A finite family of fixed-address scalar predicates. Collector roots and
copied headers instantiate this shared observation/footprint interface. -/
def wordFamily {α : Type} (cells : List α) (address : α → Nat) (accept : α → BitVec 64 → Prop) : Eqv :=
  Eqv.all fun cell => Eqv.guard (cell ∈ cells) (Eqv.rawW (fun _ => address cell) (accept cell))

/-- Exact disjoint store logs preserve the whole scalar family via Eqv
transport. Predicate-specific clients need only supply their word windows. -/
theorem wordFamily_frame {α : Type} {cells : List α} {address accept pl before after log}
    (view : (wordFamily cells address accept).P pl 0 before)
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (outside : ∀ cell ∈ cells, OutLRange log (address cell) 8) :
    (wordFamily cells address accept).P pl 0 after := by
  have image : (wordFamily cells address accept).Img id pl 0 0 before after := by
    intro cell member
    change word after (address cell) = word before (address cell)
    simp only [word,memory,bytesT_writeLog_out _ (outside cell member)]
  simpa only [placement_identity] using
    (wordFamily cells address accept).transport id pl 0 0 before after view image

end OCaml.Vm.Gc
