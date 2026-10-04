import OCaml.Refinement

namespace OCaml
set_option autoImplicit false
open Vsa.Machine

/-- Append a finite machine run while retaining the initial positive step count. -/
theorem Plus.append_steps {c d e : Config} (first : Plus c d) (rest : Steps d e) : Plus c e := by
  obtain ⟨n, first⟩ := first
  obtain ⟨k, rest⟩ := rest.toN
  refine ⟨n + k, ?_⟩
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using first.append rest

end OCaml
