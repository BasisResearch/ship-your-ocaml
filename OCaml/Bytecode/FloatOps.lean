import OCaml.Bytecode.Value

/-!
Binary64 arithmetic uses Lean's Float model (with its compiled IEEE operations).
`atan64` transcribes newlib/libm/math/s_atan.c, Sun fdlibm 5.1 (1993-09-24).
Source: https://github.com/mirror/newlib-cygwin/blob/master/newlib/libm/math/s_atan.c

Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
Developed at SunPro, a Sun Microsystems, Inc. business.
Permission to use, copy, modify, and distribute this software is freely
granted, provided that this notice is preserved.

This is executable semantics, not a machine-level libm correctness claim.
-/
namespace OCaml.Bytecode

def floatFromBits (d : BitVec 64) : Float := Float.ofBits d.toNat.toUInt64
def floatBits (d : Float) : BitVec 64 := BitVec.ofNat 64 d.toBits.toNat

/-- fdlibm's range reduction and split odd/even polynomial. Inexact status
flags are not observable by the OCaml primitive. -/
def atan64 (input : Float) : Float := Id.run do
  let hi : Array Float := #[0x3fddac670561bb4f, 0x3fe921fb54442d18,
    0x3fef730bd281f69b, 0x3ff921fb54442d18].map Float.ofBits
  let lo : Array Float := #[0x3c7a2b7f222f65e2, 0x3c81a62633145c07,
    0x3c7007887af0cbbd, 0x3c91a62633145c07].map Float.ofBits
  let a : Array Float := #[0x3fd555555555550d, 0xbfc999999998ebc4,
    0x3fc24924920083ff, 0xbfbc71c6fe231671, 0x3fb745cdc54c206e,
    0xbfb3b0f2af749a6d, 0x3fb10d66a0d03d51, 0xbfadde2d52defd9a,
    0x3fa97b4b24760deb, 0xbfa2b4442c6a6c2f, 0x3f90ad3ae322da11].map Float.ofBits
  let bits := input.toBits.toNat
  let hx := bits / 2^32
  let ix := hx % 2^31
  let negative := hx ≥ 2^31
  if ix ≥ 0x44100000 then
    if ix > 0x7ff00000 || (ix == 0x7ff00000 && bits % 2^32 != 0) then return input + input
    return if negative then -hi[3]! - lo[3]! else hi[3]! + lo[3]!
  let mut x := input
  let mut id : Option Nat := none
  if ix < 0x3fdc0000 then
    if ix < 0x3e200000 then return input
  else
    x := input.abs
    if ix < 0x3ff30000 then
      if ix < 0x3fe60000 then
        id := some 0; x := (2.0*x - 1.0) / (2.0 + x)
      else
        id := some 1; x := (x - 1.0) / (x + 1.0)
    else if ix < 0x40038000 then
      id := some 2; x := (x - 1.5) / (1.0 + 1.5*x)
    else
      id := some 3; x := -1.0 / x
  let z := x*x
  let w := z*z
  let s1 := z*(a[0]! + w*(a[2]! + w*(a[4]! + w*(a[6]! + w*(a[8]! + w*a[10]!)))))
  let s2 := w*(a[1]! + w*(a[3]! + w*(a[5]! + w*(a[7]! + w*a[9]!))))
  match id with
  | none => return x - x*(s1+s2)
  | some index =>
    let z := hi[index]! - ((x*(s1+s2) - lo[index]!) - x)
    return if negative then -z else z

end OCaml.Bytecode
