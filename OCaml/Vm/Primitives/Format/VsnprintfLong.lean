import OCaml.Vm.Primitives.Format.SvfLong
import VsaIris.Vsa.SnpFormatSupport
import OCaml.Vm.Primitives.LibraryFrame

/-! Entry-to-return `vsnprintf` on the LONGINT decimal format `%ld`.
The synthetic base is 48 bytes above the native entry stack pointer.
The wrapper borrows the existing FILE/formatter geometry and native adequacy.
-/
namespace VsaIris.Sym
open Vsa.MemRepr Vsa.Sim VsaIris.MallocFast

/-- Destination separation includes the wrapper's save bank, as well as
all formatter writes. Positive capacities below INT_MAX are supported. -/
structure VsnGeom (s dst n : Nat) : Prop where
  geom : SnpGeom s dst n
  destination : dst + n ≤ s - 1024 ∨ s - 48 ≤ dst

theorem vsn_epi {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (total : List (BitVec 8)) (R : Nat → BitVec 64) (Mt : Mem) (VG : VsnGeom s dst n)
    (h2 : R 2 = BitVec.ofNat 64 (s - 272)) (h8 : R 8 = BitVec.ofNat 64 n)
    (h10 : R 10 = BitVec.ofNat 64 total.length) (hlen : total.length < 2 ^ 31)
    (hB : BufAt Mt s dst n total) (ra s0 s1 : BitVec 64)
    (hra : ldv .ld Mt (BitVec.ofNat 64 (s - 272 + 216)).toNat = ra)
    (hS0 : ldv .ld Mt (BitVec.ofNat 64 (s - 272 + 208)).toNat = s0)
    (hS1 : ldv .ld Mt (BitVec.ofNat 64 (s - 272 + 200)).toNat = s1) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' Mt', R' 1 = ra → R' 2 = BitVec.ofNat 64 (s - 48) → R' 8 = s0 → R' 9 = s1 → R' 10 = R 10 →
      (∀ z, 18 ≤ z → z ≤ 27 → R' z = R z) →
      (∀ i, i < min total.length (n - 1) → imgM Mt' (dst + i) = total.getD i 0) →
      imgM Mt' (dst + min total.length (n - 1)) = 0#8 →
      (∀ a, ¬ (dst ≤ a ∧ a < dst + n) → imgM Mt' a = imgM Mt a) →
      SnpW live Dt DA (snpS s dst n) Q ra R' Mt') :
    SnpW live Dt DA (snpS s dst n) Q 0x800401ec#64 R Mt := by
  have SG := VG.geom
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have hn := SG.n_hi
  have hn0 := SG.n_pos
  have hd1 := SG.d_lo
  have hd2 := SG.d_hi
  have hdsep := VG.destination
  have hpw := hB.pw
  have hng : ¬ (BitVec.ofNat 64 total.length).toInt < (18446744073709551615#64).toInt := by
    rw [toInt_ofNat_small (by omega)]; simp
  have hn0' : BitVec.ofNat 64 n ≠ 0#64 := fun h => by
    have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hpw' : ldv .ld Mt (BitVec.ofNat 64 (s - 272 + 8)).toNat =
      BitVec.ofNat 64 (dst + min total.length (n - 1)) := by
    rw [toNat_ofNat_lt (by omega), show s - 272 + 8 = snpFP s by simp only [snpFP]; omega]; exact hpw
  snp_runF [20] hlive using [ofNat_add_ofNat, h2, h8, h10, hng, hn0', hpw', hra, hS0, hS1]
  have hmin : min total.length (n - 1) < n := by omega
  refine hk _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [show s - 272 + 224 = s - 48 by omega]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · intro z h1 h2
    simp only [upd_apply, show z ≠ 1 by omega, show z ≠ 2 by omega, show z ≠ 8 by omega,
      show z ≠ 9 by omega, show z ≠ 15 by omega, ite_false]
  · intro i hi
    rw [imgM_miss_nat _ _ (by omega) (by omega)]; exact hB.bytes i hi
  · rw [imgM_sb_ofNat' _ _ _ (by omega) (by decide)]
  · intro a ha
    rw [imgM_miss_nat _ _ (by omega) (by omega)]

theorem snez_pos {x : Nat} (h0 : 0 < x) (h : x < 2 ^ 64) :
    LeanRV64DExecutable.zero_extend (m := 64) (LeanRV64DExecutable.Functions.bool_to_bit
      (LeanRV64DExecutable.Functions.zopz0zI_u (0#64) (BitVec.ofNat 64 x))) = 1#64 := by
  have e : (LeanRV64DExecutable.Functions.zopz0zI_u (0#64) (BitVec.ofNat 64 x)) = true := by
    simp only [LeanRV64DExecutable.Functions.zopz0zI_u, decide_eq_true_eq]
    simp only [Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt h]
    exact Int.ofNat_lt.mpr h0
  rw [e]; rfl

theorem lh_flags (Mt : Mem) (a : Nat) : ldv .lh (writeLog Mt [(a, 4, 18446744073709486600#64)]) a = 0x208#64 := by
  obtain ⟨h0, h1, _, _⟩ := pin4_of_writeLog Mt [] [] a (18446744073709486600#64) (by simp [OutLRange])
  simp only [List.nil_append] at h0 h1
  simp only [ldv, bytesVal, bytesAt, widthOfM, imgM, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero,
    List.map_append, List.cons_append]
  rw [h0, h1]; decide

structure VsnAtSvf (s dst n : Nat) (R : Nat → BitVec 64) (Mt : Mem) (R' : Nat → BitVec 64) (Mt' : Mem) :
    Prop where
  r1 : R' 1 = 0x800401ec#64
  r2 : R' 2 = BitVec.ofNat 64 (s - 272)
  r8 : R' 8 = BitVec.ofNat 64 n
  r11 : R' 11 = BitVec.ofNat 64 (s - 264)
  r12 : R' 12 = R 12
  r13 : R' 13 = R 13
  keep : ∀ z, 18 ≤ z → z ≤ 27 → R' z = R z
  buf : BufAt Mt' s dst n []
  ra : ldv .ld Mt' (BitVec.ofNat 64 (s - 272 + 216)).toNat = R 1
  s0 : ldv .ld Mt' (BitVec.ofNat 64 (s - 272 + 208)).toNat = R 8
  s1 : ldv .ld Mt' (BitVec.ofNat 64 (s - 272 + 200)).toNat = R 9
  frame : ∀ a, (a < s - 272 ∨ s - 48 ≤ a) → imgM Mt' a = imgM Mt a

#ix_piece vsn_pro_p1 {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (R : Nat → BitVec 64) (Mt : Mem) (VG : VsnGeom s dst n)
    (h2 : R 2 = BitVec.ofNat 64 (s - 48)) (h10 : R 10 = BitVec.ofNat 64 dst) (h11 : R 11 = BitVec.ofNat 64 n)
    (hIm : InDA DA 0x800648f8 0x80064900)
    (hk : ∀ R' Mt', VsnAtSvf s dst n R Mt R' Mt' → SnpW live Dt DA (snpS s dst n) Q 0x8004789c#64 R' Mt') :
    SnpW live Dt DA (snpS s dst n) Q 0x8004018c#64 R Mt by
  have SG := VG.geom
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have hn := SG.n_hi
  have hn0 := SG.n_pos
  have hx : (18446744071562067968#64 ^^^ 18446744073709551615#64 : BitVec 64) = 2147483647#64 := by decide
  have hbl : ¬ (2147483647#64).toNat < (BitVec.ofNat 64 n).toNat := by
    rw [toNat_ofNat_lt (by omega)]; simp; omega
  have eS : BitVec.ofNat 64 (s - 48 + 18446744073709551392) = BitVec.ofNat 64 (s - 272) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  have hsz := snez_pos hn0 (by omega)
  have hsw := subw_ofNat' (w := n) (c := 1) (by omega) (by omega) (by omega)
  snp_runF [8] hlive using [ofNat_add_ofNat, h2, h10, h11, hx, hbl, eS, hsz, hsw] at 0x8004789c

#ix_piece vsn_pro_p2 from vsn_pro_p1 by
  snp_runF [8] hlive using [ofNat_add_ofNat, h2, h10, h11, hx, hbl, eS, hsz, hsw] at 0x8004789c

#ix_piece vsn_pro_close from vsn_pro_p2 by
  snp_runF hlive using [ofNat_add_ofNat, h2, h10, h11, hx, hbl, eS, hsz, hsw] at 0x8004789c
  refine hk _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [show s - 272 + 8 = s - 264 by omega]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · intro z h1 h2
    simp only [upd_apply, show z ≠ 1 by omega, show z ≠ 2 by omega, show z ≠ 6 by omega,
      show z ≠ 8 by omega, show z ≠ 9 by omega, show z ≠ 10 by omega, show z ≠ 11 by omega,
      show z ≠ 13 by omega, show z ≠ 14 by omega, show z ≠ 15 by omega, show z ≠ 16 by omega, ite_false]
  · rw [show snpFP s = (BitVec.ofNat 64 (s - 272 + 8)).toNat by rw [toNat_ofNat_lt (by omega)]; simp only [snpFP]; omega]
    svf_mem; simp
  · rw [show snpFP s + 12 = (BitVec.ofNat 64 (s - 272 + 20)).toNat by rw [toNat_ofNat_lt (by omega)]; simp only [snpFP]; omega]
    svf_mem; simp
  · rw [show snpFP s + 16 = (BitVec.ofNat 64 (s - 272 + 24)).toNat by rw [toNat_ofNat_lt (by omega)]; simp only [snpFP]; omega]
    exact lh_flags _ _
  · intro i hi; simp at hi
  · svf_mem
  · svf_mem
  · svf_mem
  · intro a ha; svf_mem


#ix_chain vsn_pro := [vsn_pro_p1, vsn_pro_p2, vsn_pro_close]

/-- Exact observed bytes, including truncation and the final NUL, with the
original native caller's saved registers and all other owned bytes retained. -/
structure VsnResult (s dst n : Nat) (R : Nat → BitVec 64) (Mt : Mem)
    (total : List (BitVec 8)) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = R 1
  ra : rv 1 = R 1
  sp : rv 2 = R 2
  saved : ∀ z, z = 8 ∨ z = 9 ∨ (18 ≤ z ∧ z ≤ 27) → rv z = R z
  length : rv 10 = BitVec.ofNat 64 total.length
  bytes : ∀ i, i < min total.length (n - 1) → mv (dst + i) = total.getD i 0
  nul : mv (dst + min total.length (n - 1)) = 0#8
  memory : ∀ a, snpS s dst n a →
    ¬ (s - 1024 ≤ a ∧ a < s - 48) → ¬ (dst ≤ a ∧ a < dst + n) → mv a = imgM Mt a

/-- Data-only contract for the plain signed-long decimal milestone. The
format is exactly `%ld`; general flags, width and precision are separate. -/
structure VsnLongEntry (Dt : Mem) (DA : List Nat) (s dst n p ap : Nat)
    (v : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  geometry : VsnGeom s dst n
  stack : R 2 = BitVec.ofNat 64 (s - 48)
  destination : R 10 = BitVec.ofNat 64 dst
  capacity : R 11 = BitVec.ofNat 64 n
  format : R 12 = BitVec.ofNat 64 p
  arguments : R 13 = BitVec.ofNat 64 ap
  aligned : (R 1).toNat % 4 = 0
  data : DataOff Dt DA s dst n
  dot : DotAt Dt DA
  impure : InDA DA 0x800648f8 0x80064900
  decimalPoint : ldv .ld Mt 0x800645a0 = 0x80053180#64
  mbtowc : ldv .ld Mt 0x80064588 = 0x80045798#64
  multibyte : ldv .lbu Mt 0x80064600 = 1#64
  formatGeom : FmtGeom DA p 3
  percent : imgM Dt p = 37#8
  long : imgM Dt (p + 1) = 0x6c#8
  decimal : imgM Dt (p + 2) = 0x64#8
  formatNul : imgM Dt (p + 3) = 0#8
  argument : ldv .ld Mt (BitVec.ofNat 64 ap).toNat = v
  argsOut : ArgsOut s dst n ap 1
  wrapperArgs : ap + 8 ≤ s - 272 ∨ s - 48 ≤ ap

theorem vsnprintf_long_symbolic {live Dt DA s dst n p ap v R Mt}
    (hlive : ∀ b ∈ snpText, live b.1)
    (E : VsnLongEntry Dt DA s dst n p ap v R Mt) :
    SnpW live Dt DA (snpS s dst n)
      (VsnResult s dst n R Mt (strBytes (Vsa.While.intToString v.toInt)))
      0x8004018c#64 R Mt := by
  have SG := E.geometry.geom
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hdsep := E.geometry.destination
  have hlen := intToString_length_le v
  refine vsn_pro hlive R Mt E.geometry E.stack E.destination E.capacity E.impure fun R1 Mt1 SA => ?_
  have ld1 : ∀ (k : MKind) a, a + widthOfM k ≤ s - 272 →
      ldv k Mt1 a = ldv k Mt a := fun k a ha =>
    ldv_agree k fun i hi => SA.frame _ (by omega)
  have hdp1 := (ld1 .ld 0x800645a0 (by simp only [widthOfM]; omega)).trans E.decimalPoint
  have hmb1 := (ld1 .ld 0x80064588 (by simp only [widthOfM]; omega)).trans E.mbtowc
  have hmx1 := (ld1 .lbu 0x80064600 (by simp only [widthOfM]; omega)).trans E.multibyte
  have hv1 : ldv .ld Mt1 (BitVec.ofNat 64 ap).toNat = v := by
    rw [toNat_ofNat_lt (by have := E.argsOut.hi; omega)]
    refine (ldv_agree .ld fun i hi => SA.frame _ ?_).trans ?_
    · have := E.wrapperArgs; simp only [widthOfM] at hi; omega
    · have arg := E.argument
      rw [toNat_ofNat_lt (by have := E.argsOut.hi; omega)] at arg
      exact arg
  have fmt1 : (R1 12).toNat = p := by rw [SA.r12, E.format, toNat_ofNat_lt (by have := E.formatGeom.hi; omega)]
  have ap1 : (R1 13).toNat = ap := by rw [SA.r13, E.arguments, toNat_ofNat_lt (by have := E.argsOut.hi; omega)]
  refine svf_entry hlive R1 Mt1 SG SA.r2 SA.r11 hdp1 E.dot SA.buf fun R2 Mt2 A => ?_
  rw [fmt1, ap1] at A
  refine svf_iterLD (total := []) hlive R2 Mt2 SG E.data hmb1 hmx1 A 0
    ⟨fun b h1 h2 => E.formatGeom.dom b h1 (by omega), E.formatGeom.lo,
      by have := E.formatGeom.hi; omega, by have := E.formatGeom.htif; omega⟩
    (fun i hi => by omega) (by simpa using E.percent) (by simpa using E.long)
    (by simpa using E.decimal) v hv1 E.argsOut (by simp) fun R3 Mt3 A3 => ?_
  simp only [List.length_nil, Nat.zero_add, Nat.add_zero, List.nil_append, pieceBytes_zero] at A3
  refine svf_iterEnd hlive R3 Mt3 SG E.data hmb1 hmx1 A3 0
    ⟨fun b h1 h2 => E.formatGeom.dom b (by omega) (by omega),
      by have := E.formatGeom.lo; omega, by have := E.formatGeom.hi; omega,
      by have := E.formatGeom.htif; omega⟩
    (fun i hi => by omega) (by simpa using E.formatNul) (by omega)
    (by rw [SA.r1]; decide) ?_
  simp only [Nat.add_zero, pieceBytes_zero, List.append_nil]
  intro R4 Mt4 h2 hkeep h10 hB hfr
  have ld4 : ∀ off, 200 ≤ off → off + 8 ≤ 224 →
      ldv .ld Mt4 (BitVec.ofNat 64 (s - 272 + off)).toNat =
      ldv .ld Mt1 (BitVec.ofNat 64 (s - 272 + off)).toNat := by
    intro off lower upper
    rw [toNat_ofNat_lt (by omega)]
    exact ldv_agree .ld fun i hi => hfr _ (by simp only [SvfW, snpFP, widthOfM] at *; omega)
  rw [SA.r1]
  refine vsn_epi hlive _ R4 Mt4 E.geometry h2 ((hkeep 8 (.inl rfl)).trans SA.r8) h10
    (by omega) hB (R 1) (R 8) (R 9)
    ((ld4 216 (by omega) (by omega)).trans SA.ra)
    ((ld4 208 (by omega) (by omega)).trans SA.s0)
    ((ld4 200 (by omega) (by omega)).trans SA.s1) E.aligned
    fun R5 Mt5 hra hsp hs0 hs1 hlength hk hb hnul hfr5 => ?_
  apply swp_done
  intro rv mv observed
  have regs := observed.regs
  refine ⟨observed.pc, (regs 1 (by decide) (by decide)).trans hra,
    (regs 2 (by decide) (by decide)).trans (hsp.trans E.stack.symm), ?_,
    (regs 10 (by decide) (by decide)).trans ?_, ?_, ?_, ?_⟩
  · intro z hz
    have member : z ∈ nRegs := by
      rcases hz with rfl | rfl | ⟨lo, hi⟩
      · decide
      · decide
      · simp only [nRegs, List.mem_cons, List.not_mem_nil]; omega
    refine (regs z member (by change z ≠ 32; rcases hz with rfl | rfl | ⟨lo, hi⟩ <;> omega)).trans ?_
    rcases hz with rfl | rfl | ⟨lo, hi⟩
    · exact hs0
    · exact hs1
    · exact (hk z lo hi).trans ((hkeep z (.inr (.inr ⟨lo, hi⟩))).trans (SA.keep z lo hi))
  · exact hlength.trans h10
  · intro i hi
    rw [observed.img _ (.inr (.inr ⟨by omega, by have := SG.n_pos; omega⟩))]
    exact hb i hi
  · rw [observed.img _ (.inr (.inr ⟨by omega, by have := SG.n_pos; omega⟩))]
    exact hnul
  · intro a owned frame dest
    rw [observed.img a owned, hfr5 a dest,
      hfr a (by simp only [SvfW, snpFP]; omega), SA.frame a (by omega)]

end VsaIris.Sym

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- Native entry-to-return summary, obtained from the proved symbolic run.
`SymbolicInput` supplies initial machine observations and `VsaOk`, never a
callee execution or a presumed return postcondition. -/
theorem vsnprintf_long_summary {live Dt DA s dst n p ap v R Mt}
    (c : Config) (codeLive : ∀ b ∈ snpText, live b.1)
    (entry : VsnLongEntry Dt DA s dst n p ap v R Mt)
    (separate : LocalSeparation roR (snpText ++ dataOf Dt DA) nRegs (snpS s dst n))
    (input : SymbolicInput live (snpText ++ dataOf Dt DA) nRegs (snpS s dst n) R Mt c) :
    FnSummary 0x8004018c#64 (fun d => d = c)
      (LocalPost live roR (snpText ++ dataOf Dt DA) nRegs (snpS s dst n)
        (VsnResult s dst n R Mt (strBytes (Vsa.While.intToString v.toInt))) c) :=
  symbolic_summary c separate input (vsnprintf_long_symbolic codeLive entry)

/-- The native frame and the symbolic byte frame together cover every
address outside the wrapper/formatter stack and the destination window. -/
theorem vsnprintf_long_memory {live Dt DA s dst n R Mt before after} {v : BitVec 64}
    (input : SymbolicInput live (snpText ++ dataOf Dt DA) nRegs (snpS s dst n) R Mt before)
    (post : LocalPost live roR (snpText ++ dataOf Dt DA) nRegs (snpS s dst n)
      (VsnResult s dst n R Mt (strBytes (Vsa.While.intToString v.toInt))) before after)
    (a : Nat) (stack : ¬ (s - 1024 ≤ a ∧ a < s - 48))
    (destination : ¬ (dst ≤ a ∧ a < dst + n)) :
    (vsaModel live).mem after a = (vsaModel live).mem before a := by
  by_cases owned : snpS s dst n a
  · exact (post.result.memory a owned stack destination).trans (input.memory a owned).symm
  · exact post.memory a owned

end OCaml.Vm.Primitives
