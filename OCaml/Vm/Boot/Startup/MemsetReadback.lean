import OCaml.Vm.Boot.Startup.Memset56
import OCaml.Vm.Boot.Startup.BssReads
import Vsa.Sim.WriteLogRead
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The fixed tail's scalar addresses, independent of the backing memory. -/
theorem Memset56Region.tail_log {base} (r : Memset56Region base) :
    memsetBytesLog (pairCursor base 3) =
      [(base + 55, 1, 0#64), (base + 54, 1, 0#64), (base + 53, 1, 0#64),
       (base + 52, 1, 0#64), (base + 51, 1, 0#64), (base + 50, 1, 0#64),
       (base + 49, 1, 0#64), (base + 48, 1, 0#64)] := by
  simp only [memsetBytesLog, r.tail_nat 7 (by decide), r.tail_nat 6 (by decide),
    r.tail_nat 5 (by decide), r.tail_nat 4 (by decide), r.tail_nat 3 (by decide),
    r.tail_nat 2 (by decide), r.tail_nat 1 (by decide), r.pairs.cursor_nat (Nat.le_refl 3)]

theorem Memset56Region.tail_out {base} (r : Memset56Region base) (a : Nat)
    (outside : a < base + 48 ∨ base + 56 ≤ a) : OutL (memsetBytesLog (pairCursor base 3)) a := by
  rw [r.tail_log]
  simp only [OutL]
  repeat' apply And.intro
  all_goals first | trivial | omega

/-- Bytes outside the allocation are unchanged by the complete zeroing effect. -/
theorem memset56Memory_out {base} (r : Memset56Region base) (m : Std.ExtHashMap Nat (BitVec 8))
    (a : Nat) (outside : a < base ∨ base + 56 ≤ a) :
    (memset56Memory m base)[a]? = m[a]? := by
  unfold memset56Memory
  rw [writeLog_out _ _ _ (r.tail_out a (by omega))]
  rcases outside with below | above
  · exact clearWords_below _ _ _ _ below
  · exact clearWords_above _ _ _ _ (by omega)

/-- Every byte of the requested 56-byte extent is zero after the summary. -/
theorem memset56Memory_inside {base} (r : Memset56Region base) (m : Std.ExtHashMap Nat (BitVec 8))
    (a : Nat) (lo : base ≤ a) (hi : a < base + 56) :
    (memset56Memory m base)[a]? = some 0#8 := by
  unfold memset56Memory
  by_cases word : a < base + 48
  · rw [writeLog_out _ _ _ (r.tail_out a (Or.inl word))]
    exact clearWords_inside _ _ _ _ lo (by omega)
  · rw [r.tail_log, writeLog_getElem?_logRead]
    have cases : a = base + 48 ∨ a = base + 49 ∨ a = base + 50 ∨ a = base + 51 ∨
        a = base + 52 ∨ a = base + 53 ∨ a = base + 54 ∨ a = base + 55 := by omega
    rcases cases with eq | eq | eq | eq | eq | eq | eq | eq
    all_goals subst a
    all_goals simp (disch := omega) [logRead, logReadNewest, writeEntryByte]
    all_goals rfl
end OCaml.Vm.Boot.Startup
