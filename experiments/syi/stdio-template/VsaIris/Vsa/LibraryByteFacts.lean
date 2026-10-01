import Vsa.Sim.SnprintfSpec19
import Vsa.Sim.MemcpySpec
import Vsa.Sim.MemcpySites2
open Sail LeanRV64DExecutable.Functions
namespace Vsa.Sim

theorem extractLsb'_ldData8 (c0 c1 c2 c3 c4 c5 c6 c7 : BitVec 8) (k : Nat) (hk : k < 8)
    (ck : BitVec 8)
    (hck : [c0, c1, c2, c3, c4, c5, c6, c7][k]? = some ck) :
    (ldData8 c0 c1 c2 c3 c4 c5 c6 c7).extractLsb' (8 * k) 8 = ck := by
  show ((((((((c7 +++ c6) +++ c5) +++ c4) +++ c3) +++ c2) +++ c1) +++ c0).extractLsb' (8 * k) 8) = ck
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  match k, hk, hck with
  | 0, _, hck | 1, _, hck | 2, _, hck | 3, _, hck
  | 4, _, hck | 5, _, hck | 6, _, hck | 7, _, hck =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hck
    subst hck
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.reduceMul]
    rw [decide_eq_true (show i < 8 from hi), Bool.true_and]
    repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
    congr 1 <;> omega

theorem pinw4_sext_reassemble (v : BitVec (8 * 4)) :
    (sign_extend (m := 64)
      (((((v.extractLsb' 24 8).append (v.extractLsb' 16 8)).append (v.extractLsb' 8 8)).append (v.extractLsb' 0 8)) : BitVec (8 * 4)) : BitVec 64) = sign_extend (m := 64) v :=
  lw_cap_reassemble_sp v

end Vsa.Sim
