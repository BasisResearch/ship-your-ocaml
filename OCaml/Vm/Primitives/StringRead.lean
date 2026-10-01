import OCaml.Vm.Primitives.Read
import OCaml.Vm.Primitives.StringArithmetic

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

def stringHeader (c : Config) (x : BitVec 64) : BitVec 64 :=
  word c (x - 8).toNat

def stringPadding (c : Config) (x : BitVec 64) : BitVec 8 :=
  byte c (x + stringLast (stringHeader c x)).toNat

def stringLoads (c : Config) (x : BitVec 64) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (x - 8).toNat, [stringPadding c x]]

/-- The complete object, including its header, lies in ordinary RAM. -/
structure StringGeometry (a length : Nat) : Prop where
  lower : 0x80000000 + 8 ≤ a
  upper : a + 8 * ((length + 8) / 8) ≤ 0x100000000
  htif : a + 8 * ((length + 8) / 8) ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 8 ≤ a - 8

theorem string_header_address {a n : Nat} (h : StringGeometry a n) :
    ((BitVec.ofNat 64 a) - 8).toNat = a - 8 := by
  have hl := h.lower
  have hu := h.upper
  change ((18446744073709551616 - 8 + a % 18446744073709551616) % 18446744073709551616) = a - 8
  omega

theorem string_padding_address {a n : Nat} {header : BitVec 64}
    (h : StringGeometry a n) (hs : header.toNat / 1024 = (n + 8) / 8) :
    ((BitVec.ofNat 64 a) + stringLast header).toNat = a + 8 * ((n + 8) / 8) - 1 := by
  have hl := h.lower
  have hu := h.upper
  rw [BitVec.toNat_add, stringLast_toNat header n hs]
  simp only [BitVec.toNat_ofNat]
  omega

theorem StringGeometry.header_window {a n : Nat} (h : StringGeometry a n) :
    ReadWindow ((BitVec.ofNat 64 a) - 8) 8 := by
  rw [show ((BitVec.ofNat 64 a) - 8) = BitVec.ofNat 64 (a - 8) from by
    apply BitVec.eq_of_toNat_eq
    rw [string_header_address h]
    have hu := h.upper
    simp only [BitVec.toNat_ofNat]
    omega]
  have hl := h.lower
  have hu := h.upper
  have ht := h.htif
  constructor <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem StringGeometry.padding_window {a n : Nat} {header : BitVec 64}
    (h : StringGeometry a n) (hs : header.toNat / 1024 = (n + 8) / 8) :
    ReadWindow ((BitVec.ofNat 64 a) + stringLast header) 1 := by
  have hl := h.lower
  have hu := h.upper
  have ht := h.htif
  constructor <;> rw [string_padding_address h hs] <;> omega

end OCaml.Vm.Primitives
