import OCaml.Vm.Primitives.Register
import Vsa.Sim.RamReadLoad

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- A total scalar load lies in RAM and does not intersect the HTIF register. -/
structure ReadWindow (a : BitVec 64) (width : Nat) : Prop where
  lower : 0x80000000 ≤ a.toNat
  upper : a.toNat + width ≤ 0x100000000
  htif : a.toNat + width ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 8 ≤ a.toNat

/-- Byte observations for the segment evaluator; absent bytes have value zero. -/
def read8 (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : List (BitVec 8) :=
  [(m[a]?).getD 0, (m[a+1]?).getD 0, (m[a+2]?).getD 0, (m[a+3]?).getD 0,
   (m[a+4]?).getD 0, (m[a+5]?).getD 0, (m[a+6]?).getD 0, (m[a+7]?).getD 0]

theorem read8_pins (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    LPins8 m a (read8 m a) := by
  simp [LPins8, read8]

theorem read8_value (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    bytesVal .ld (read8 m a) = bytesT m a 8 := by
  rw [bytesT_eight_eq]
  simp [bytesVal, read8, bytesT8, LeanRV64DExecutable.Functions.sign_extend,
    Sail.BitVec.signExtend]

theorem byte_total (c : Config) (a : Nat) :
    byte c a = (c.σ.mem[a]?).getD 0 := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  rw [byte, getLsbD_bytesT c.σ.mem 1 a k hk]
  simp [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]

/-- Discharge one load using its effective address and total byte observations. -/
theorem ReadWindow.ld {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs}
    {a : MInstr} {x : BitVec 64} {bs : List (BitVec 8)} (h : ReadWindow x 8)
    (kind : a.kind = .ld) (address : eaddrM a L = x) (pins : LPins8 m x.toNat bs) :
    MemFacts m L bs a := by
  simp only [MemFacts, kind, address]
  refine ⟨⟨h.lower, h.upper, ?_⟩, pins⟩
  simpa only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] using h.htif

theorem ReadWindow.lbu {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs}
    {a : MInstr} {x : BitVec 64} {b : BitVec 8} (h : ReadWindow x 1)
    (kind : a.kind = .lbu) (address : eaddrM a L = x) (pin : (m[x.toNat]?).getD 0 = b) :
    MemFacts m L [b] a := by
  simp only [MemFacts, kind, address, List.getD_cons_zero]
  refine ⟨⟨h.lower, h.upper, ?_⟩, pin⟩
  simpa only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] using h.htif

end OCaml.Vm.Primitives
