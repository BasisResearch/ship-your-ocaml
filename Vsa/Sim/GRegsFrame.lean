import Vsa.Sim.SegToTripleFramed

namespace Vsa.Sim
open Vsa.Machine LeanRV64DExecutable

/-- Select a finite interface from reflected register observations. -/
theorem gholds_select {σ : MState} {L : GRegs} (holds : GHolds σ L)
    (wanted : GRegs)
    (select : ∀ n v, (n, v) ∈ wanted → lookupG n L = some v) : GHolds σ wanted := by
  induction wanted with
  | nil => trivial
  | cons pin rest ih =>
    rcases pin with ⟨n, v⟩
    exact ⟨gholds_lookup _ holds (select n v (List.mem_cons_self ..)),
      ih (fun n v h => select n v (List.mem_cons_of_mem _ h))⟩

/-- Transport a selected register interface through the segment kernel's
complete frame. This shares the finite-register adapter across call seams. -/
theorem gholds_of_frame {before after : MState} {writes : List Nat}
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ writes, (gprReg n == r) = false) →
      after.regs.get? r = before.regs.get? r)
    (L : GRegs) (keys : KeysOK (keysG L))
    (noise : ∀ n ∈ keysG L, ∀ q ∈ noiseRegs, (q == gprReg n) = false)
    (outside : ∀ n ∈ keysG L, ∀ m ∈ writes, (gprReg m == gprReg n) = false)
    (holds : GHolds before L) : GHolds after L := by
  induction L with
  | nil => trivial
  | cons pin rest ih =>
    rcases pin with ⟨n, v⟩
    have member : n ∈ keysG ((n, v) :: rest) := List.mem_cons_self ..
    have bound := keys n member
    refine ⟨(gprGet_of_frame n bound.1 bound.2 (noise n member) (outside n member) frame).trans holds.1, ?_⟩
    exact ih (fun n hn => keys n (List.mem_cons_of_mem _ hn))
      (fun n hn => noise n (List.mem_cons_of_mem _ hn))
      (fun n hn => outside n (List.mem_cons_of_mem _ hn)) holds.2

end Vsa.Sim
