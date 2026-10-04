import OCaml.Vm.Gc.BestFitSplit
import OCaml.Vm.Primitives.ScanArithmetic

namespace OCaml.Vm.Gc.BestFitSplit
open Primitives

/-- The machine subtraction computes the remnant's total word count. -/
theorem delta_nat (request header : BitVec 64)
    (fits : request.toNat ≤ header.toNat / 1024) :
    (delta request header).toNat = header.toNat / 1024 - request.toNat := by
  unfold delta sizeWord
  have bound := header.isLt
  simp only [BitVec.toNat_sub,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  omega

/-- The selected color/tag expression describes the remnant payload. -/
theorem remnant_header (request header : BitVec 64)
    (fits : request.toNat < header.toNat / 1024) :
    HeaderOk (remnantHeader (route request header) (delta request header))
      (header.toNat / 1024 - request.toNat - 1)
      (if route request header then 0 else Layout.tag_abstract) := by
  have rem := delta_nat request header (Nat.le_of_lt fits)
  have bound := header.isLt
  unfold remnantHeader
  generalize he : route request header = large
  cases large
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,HeaderOk,whiteHeader,blueHeader,
    Layout.tag_abstract,Layout.gc_white,Layout.gc_blue,BitVec.toNat_sub,
    BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,BitVec.toNat_ofNat]
  all_goals omega

/-- Read the remnant header back from the final machine memory. -/
theorem Post.remnant {ra request source before after}
    (post : Post ra request source before after)
    (fits : request.toNat < (header source before).toNat / 1024) :
    HeaderOk (word after (headerAddr source).toNat)
      ((header source before).toNat / 1024 - request.toNat - 1)
      (if route request (header source before) then 0 else Layout.tag_abstract) := by
  have stored : word after (headerAddr source).toNat =
      remnantHeader (route request (header source before)) (delta request (header source before)) := by
    rw [word,post.memory]
    exact word_writeLog_at _ _ 1 _ _ rfl trivial
  rw [stored]
  exact remnant_header request (header source before) fits

/-- Counter readback requires the source header to be separate from the
runtime accounting cell; the execution theorem itself needs no such alias rule. -/
theorem Post.counter {ra request source before after}
    (post : Post ra request source before after)
    (outside : Vsa.Sim.OutLRange ((effect request source before).drop 1) Layout.sym_caml_fl_cur_wsz 8) :
    word after Layout.sym_caml_fl_cur_wsz =
      word before Layout.sym_caml_fl_cur_wsz - 1#64 - sizeWord (header source before) := by
  rw [word,post.memory]
  exact word_writeLog_at _ _ 0 _ _ rfl outside

end OCaml.Vm.Gc.BestFitSplit
