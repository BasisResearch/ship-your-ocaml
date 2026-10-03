import Vsa.Sim.Boot.ByteView
namespace Vsa.Sim.Boot
theorem nbytes_ext {n : Nat} (a b : NByteArray n) (h : a.bytes = b.bytes) : a = b := by
  cases a; cases b; cases h; rfl
/-- ELF header parsing observes only the first 64 bytes. -/
theorem elfHeader_prefix (b : ByteArray) (h : 64 ≤ b.size) :
    mkELF64Header b h = mkELF64Header (b.extract 0 64) (by simp; omega) := by
  have ident (h₁ : 16 ≤ b.size) (h₂ : 16 ≤ (b.extract 0 64).size) :
      NByteArray.extract b 16 h₁ = NByteArray.extract (b.extract 0 64) 16 h₂ := by
    apply nbytes_ext
    change b.extract 0 16 = (b.extract 0 64).extract 0 16
    simp [ByteArray.extract_extract]
  by_cases endian : b[5]'(by omega) == (2 : UInt8)
  all_goals simp (disch := (simp; omega)) [mkELF64Header, ident, endian, mkELF64Header.getUInt16from,
    mkELF64Header.getUInt32from, mkELF64Header.getUInt64from, mkELF64Header.isBigEndian,
    ByteArray.getUInt16LEfrom, ByteArray.getUInt32LEfrom, ByteArray.getUInt64LEfrom,
    ByteArray.getUInt16BEfrom, ByteArray.getUInt32BEfrom, ByteArray.getUInt64BEfrom,
    ByteArray.getElem_extract, Nat.zero_add]
/-- Specialize header locality to bounded views before instantiating a large file size. -/
theorem elfHeader_view (n : Nat) (byte : Nat → BitVec 8) (bound : 64 ≤ n) :
    mkELF64Header (bytesOfView n byte) (by simpa using bound) =
      mkELF64Header (bytesOfView 64 byte) (by simp) := by
  rw [elfHeader_prefix]
  have slice : (bytesOfView n byte).extract 0 64 = bytesOfView 64 byte := by
    simpa only [Nat.zero_add] using bytesOfView_extract n byte 0 64 bound
  simp only [slice]
theorem elfHeader_parse_view (n : Nat) (byte : Nat → BitVec 8) (bound : 64 ≤ n) :
    mkELF64Header? (bytesOfView n byte) =
      .ok (mkELF64Header (bytesOfView 64 byte) (by simp)) := by
  unfold mkELF64Header?
  rw [dif_pos (by simpa using bound), elfHeader_view n byte bound]
end Vsa.Sim.Boot
