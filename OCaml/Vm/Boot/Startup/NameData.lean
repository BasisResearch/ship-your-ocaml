import OCaml.Vm.Boot.Startup.NameStep
import Vsa.Sim.StrcmpSpec
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.MemRepr OCaml.Vm.Primitives

def nameCursor (p : BitVec 64) (k : Nat) : BitVec 64 := p + BitVec.ofNat 64 k

theorem nameCursor_next (p : BitVec 64) (k : Nat) : nameCursor p k + 1#64 = nameCursor p (k + 1) := by
  unfold nameCursor
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem nameCursor_nat {p : BitVec 64} {count k : Nat} (region : ReadWindow p (count + 1)) (bound : k ≤ count) :
    (nameCursor p k).toNat = p.toNat + k := by
  unfold nameCursor
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have upper := region.upper
  have kmod : k % 2^64 = k := Nat.mod_eq_of_lt (by omega)
  rw [kmod]
  exact Nat.mod_eq_of_lt (by omega)

theorem name_window {p : BitVec 64} {count k : Nat} (region : ReadWindow p (count + 1)) (bound : k ≤ count) :
    ReadWindow (nameCursor p k) 1 := by
  have addr := nameCursor_nat region bound
  have lower := region.lower
  have upper := region.upper
  have htif := region.htif
  constructor <;> rw [addr] <;> omega

/-- An ordinary C-string environment name has no embedded equals sign. -/
structure EnvName (p : BitVec 64) (cs : List Char) (c : Config) : Prop where
  bytes : CStr c.σ.mem p.toNat cs
  region : ReadWindow p (cs.length + 1)
  noEquals : ∀ k, k < cs.length → byteVal cs k ≠ 61

/-- Total byte facts consumed by one native scan, independent of map presence. -/
structure NameByteAt (c : Config) (base k count : Nat) (b : BitVec 8) : Prop where
  pin : (c.σ.mem[base + k]?).getD 0 = b
  zero : b = 0#8 ↔ k = count
  notEquals : b ≠ 61#8

theorem EnvName.byte {p cs c} (data : EnvName p cs c) {k : Nat} (bound : k ≤ cs.length) :
    ∃ b, NameByteAt c p.toNat k cs.length b := by
  obtain ⟨b, pin, zero, value⟩ := cstr_byte_val c.σ.mem p.toNat cs data.bytes k bound
  refine ⟨b, ?_, zero, ?_⟩
  · rw [pin]; rfl
  · by_cases last : k = cs.length
    · rw [zero.mpr last]
      decide
    · intro eq
      rw [eq] at value
      exact data.noEquals k (by omega) value.symm
end OCaml.Vm.Boot.Startup
