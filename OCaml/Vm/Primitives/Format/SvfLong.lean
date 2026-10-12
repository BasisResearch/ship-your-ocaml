import VsaIris.Vsa.SnpSvfLoop

/-!
# `_svfprintf_r` on `%ld` (LONGINT)

caml_format_int formats with `"%ld"` (parse_format appends
`ARCH_INTNAT_PRINTF_FORMAT` = `"l"`). newlib's `l` case sets `LONGINT`
(flag 16) when the next byte is not a second `l`; the signed argument is
then fetched as a `long`. The retargeted battery covers `%lld` (QUADINT,
`svf_convLL`, `svf_intQ`); these are the LONGINT siblings, over the same
step automation (`snp_runF`). `IntAt.r6` admits flag 16 (the digit and
print code test no LONGINT bit).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

/-- The LONGINT arm of the `l` case: `ori t1,t1,16`, then `j rflag`. Upstream
never ran it, so the retargeted step tables stop at the `beq`. -/
def nx_8004878c : List BBlock := [{ body := [mkLine 0x8004878c#64 0x01036313#32], term := none }]
def nx_80048790 : List BBlock := [⟨[], some (⟨0x80048790#64, 0xa54ff06f#32, 0x6f#8, 0xf0#8, 0x4f#8, 0xa5#8,
  .j, 0, 0, 0x0#13, 0x1ff254#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.MallocFast VsaIris.Inst

theorem nt_8004878c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80048790#64 (upd R 6 ((R 6) ||| sign_extend (m := 64) (0x010#12))) Mt) :
    SnpW live Dt DA S Q 0x8004878c#64 R Mt :=
  swp_stepD nx_8004878c [6] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8004878c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 6 ∈ [6])))) rfl hk

theorem nt_80048790 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800479e4#64 R Mt) :
    SnpW live Dt DA S Q 0x80048790#64 R Mt :=
  swp_stepD nx_80048790 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80048790 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

/-- The `l` case followed by `d`: `LONGINT`, back to `rflag` with the `d`. -/
theorem svf_convL {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat} (x : Nat)
    (R : Nat → BitVec 64) (Mt : Mem)
    (hx : InDA DA x (x + 1)) (hx1 : 0x80000000 ≤ x) (hx2 : x + 1 ≤ 0x100000000)
    (hx3 : x + 1 ≤ 0x80061fc0 ∨ 0x80061fc8 ≤ x)
    (hd : imgM Dt x = 0x64#8) (h25 : R 25 = BitVec.ofNat 64 x) (h6 : R 6 = 0#64)
    (hk : ∀ R', R' 25 = BitVec.ofNat 64 x → R' 24 = 100#64 → R' 6 = 16#64 →
      (∀ z, z ≠ 6 → z ≠ 15 → z ≠ 24 → R' z = R z) →
      SnpW live Dt DA (snpS s dst n) Q 0x800479e4#64 R' Mt) :
    SnpW live Dt DA (snpS s dst n) Q 0x80048780#64 R Mt := by
  have hb0 := lbu_img_ofNat Dt x (by omega)
  rw [hd] at hb0
  snp_runF hlive using [h25, h6, hb0] at 0x800479e4
  snp_runF hlive using [h25, h6, hb0] at 0x800479e4
  refine hk _ ?_ ?_ ?_ ?_
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
  · exact h25
  · rfl
  · intro z h6' h15 h24
    simp only [upd_apply, h6', h15, h24, ite_false]

/-! The signed `long` argument (flag 16), as `svf_intQ` for QUADINT. -/

#ix_piece svf_intL_p1 {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {rt : BitVec 64} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} (x : Nat) (v : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (St : SvfSt DA s dst n R0 Mt0 p ap rt total L R Mt)
    (h167 : ldv .lbu Mt (BitVec.ofNat 64 (s - 864 + 167)).toNat = 0#64)
    (h25 : R 25 = BitVec.ofNat 64 x) (h6 : R 6 = 16#64) (h20 : R 20 = 18446744073709551615#64)
    (h27 : R 27 = 0#64)
    (hv : ldv .ld Mt (BitVec.ofNat 64 ap).toNat = v) (hap1 : s - 40 ≤ ap) (hap2 : ap + 8 ≤ s)
    (hk : ∀ R' Mt', IntAt DA s dst n R0 Mt0 x (ap + 8) rt total L (vMag v) (vSg v) R' Mt' →
      SnpW live Dt DA (snpS s dst n) Q 0x8004834c#64 R' Mt') :
    SnpW live Dt DA (snpS s dst n) Q 0x80048254#64 R Mt by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have h2 := St.core.r2
  have hapf := St.core.ap

#ix_piece svf_intL_run1 from svf_intL_p1 by
  snp_runF [2] hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80048334

#ix_piece svf_intL_run2 from svf_intL_run1 by
  snp_runF [2] hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80048334

#ix_piece svf_intL_run3 from svf_intL_run2 by
  snp_runF [2] hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80048334

#ix_piece svf_intL_run4 from svf_intL_run3 by
  snp_runF [2] hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80048334

#ix_piece svf_intL_run5 from svf_intL_run4 by
  snp_runF [2] hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80048334

#ix_piece svf_intL_run6 from svf_intL_run5 by
  snp_runF [2] hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80048334

#ix_piece svf_intL_run7 from svf_intL_run6 by
  snp_runF [2] hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80048334

#ix_piece svf_intL_run8 from svf_intL_run7 by
  snp_runF [2] hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80048334

#ix_piece svf_intL_run9 from svf_intL_run8 by
  snp_runF [2] hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80048334

#ix_piece svf_intL_run10 from svf_intL_run9 by
  snp_runF [2] hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80048334

#ix_piece svf_intL_run11 from svf_intL_run10 by
  snp_runF [2] hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80048334

#ix_piece svf_intL_run12 from svf_intL_run11 by
  snp_runF [2] hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80048334

#ix_piece svf_intL_cases from svf_intL_run12 by
  snp_runF hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x8004834c

#ix_piece svf_intL_a from svf_intL_cases at 1 by
  all_goals rename_i hc _
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc)
  all_goals refine hk _ _ ⟨St.update SG ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try (intro z hz; rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]))
  all_goals (try (intro a ha; unfold StKeep SvfKeep at ha; svf_mem))
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
  all_goals (try (svf_mem; done))
  all_goals (try (svf_mem; exact St.core.ret))
  · svf_mem; rw [vSg_pos hc]; exact h167
  · exact vSg01 v
  · rw [vMag_pos hc]; simp
  · exact vMag_lt v
  · exact .inr (.inr h6)
  · exact h20

#ix_piece svf_intL_b from svf_intL_cases at 2 by
  all_goals rename_i hc _
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc)
  all_goals refine hk _ _ ⟨St.update SG ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try (intro z hz; rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]))
  all_goals (try (intro a ha; unfold StKeep SvfKeep at ha; svf_mem))
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
  all_goals (try (svf_mem; done))
  all_goals (try (svf_mem; exact St.core.ret))
  · rw [ldv_lbu_sb45, vSg_neg hc]
  · exact vSg01 v
  · rw [vMag_neg hc]; apply BitVec.eq_of_toNat_eq; simp
  · exact vMag_lt v
  · exact .inr (.inr h6)
  · exact h20


#ix_fork svf_intL_close := svf_intL_cases [svf_intL_a, svf_intL_b]

#ix_chain svf_intL := [svf_intL_p1, svf_intL_run1, svf_intL_run2, svf_intL_run3, svf_intL_run4, svf_intL_run5, svf_intL_run6, svf_intL_run7, svf_intL_run8, svf_intL_run9, svf_intL_run10, svf_intL_run11, svf_intL_run12, svf_intL_close]

/-- **One `%ld` conversion** (`l` then `d`), as `svf_iterLLD` for `%lld`. -/
theorem svf_iterLD {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {total : List (BitVec 8)}
    (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n) (DO : DataOff Dt DA s dst n)
    (hmb : ldv .ld Mt0 0x80064588 = 0x80045798#64) (hmx : ldv .lbu Mt0 0x80064600 = 1#64)
    (A : SvfAt s dst n R0 Mt0 p ap (BitVec.ofNat 64 total.length) total R Mt)
    (k : Nat) (FG : FmtGeom DA p (k + 2))
    (hb : ∀ i, i < k → imgM Dt (p + i) ≠ 0#8 ∧ imgM Dt (p + i) ≠ 37#8)
    (hpc : imgM Dt (p + k) = 37#8) (hl1 : imgM Dt (p + k + 1) = 0x6c#8)
    (hd : imgM Dt (p + k + 2) = 0x64#8)
    (v : BitVec 64) (hv : ldv .ld Mt0 (BitVec.ofNat 64 ap).toNat = v)
    (hap1 : s - 40 ≤ ap) (hap2 : ap + 8 ≤ s) (hc : total.length + k + 21 < 2 ^ 31)
    (hk : ∀ R' Mt', SvfAt s dst n R0 Mt0 (p + k + 3) (ap + 8)
      (BitVec.ofNat 64 (total.length + k + (strBytes (Vsa.While.intToString v.toInt)).length))
      (total ++ pieceBytes (imgM Dt) p k ++ strBytes (Vsa.While.intToString v.toInt)) R' Mt' →
      SnpW live Dt DA (snpS s dst n) Q 0x8004796c#64 R' Mt') :
    SnpW live Dt DA (snpS s dst n) Q 0x8004796c#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hFlo := FG.lo
  have hFhi := FG.hi
  have hFht := FG.htif
  refine svf_head hlive R Mt SG A fun R1 A1 h22 => ?_
  refine svf_scan hlive SG hmb hmx k p R1 Mt A1 h22 ⟨fun b h1 h2 => FG.dom b h1 (by omega), hFlo,
    by omega, by omega⟩ hb (fun h => absurd (h.symm.trans hpc) (by decide)) (fun _ R2 Mt2 A2 h22' h10 => ?_) (.inr hpc)
  refine svf_lit hlive 0x800479a8#64 0x800479b8#64 (.inl ⟨rfl, rfl⟩) R2 Mt2 SG A2 h22'
    (by simpa using h10) (by omega) (by omega) (by omega) (fun _ => pieceSrc_of_data DO SG (by omega)
      (fun b h1 h2 => FG.dom b h1 (by omega))) ?_
  intro R3 Mt3 L hL St3 h22''
  have hLl : L.length ≤ 1 := by rcases hL with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  have hLs : sumLen L = k := by rcases hL with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [sumLen] <;> omega
  refine svf_convStart hlive (p + k) R3 Mt3 SG St3 h22'' (fun b h1 h2 => FG.dom b (by omega) (by omega))
    (by omega) (by omega) (by omega) fun R4 Mt4 CA => ?_
  rw [hl1] at CA
  refine svf_disp hlive (p + k + 1) 0x6c _ (.inr (.inr ⟨rfl, rfl⟩)) R4 Mt4 (by omega) CA.r25 CA.r24
    CA.r26 CA.r22 DO.tab fun R5 h25 h24 hkp5 => ?_
  have h6 : R5 6 = 0#64 := (hkp5 6 (by decide) (by decide) (by decide) (by decide)).trans CA.r6
  refine svf_convL hlive (p + k + 2) R5 Mt4 (fun b h1 h2 => FG.dom b (by omega) (by omega))
    (by omega) (by omega) (by omega) hd h25 h6 fun R6 h25' h24' h6' hkp6 => ?_
  have k26 : R6 26 = 90#64 := (hkp6 26 (by decide) (by decide) (by decide)).trans
    ((hkp5 26 (by decide) (by decide) (by decide) (by decide)).trans CA.r26)
  have k22 : R6 22 = 0x8005a398#64 := (hkp6 22 (by decide) (by decide) (by decide)).trans
    ((hkp5 22 (by decide) (by decide) (by decide) (by decide)).trans CA.r22)
  refine svf_disp hlive (p + k + 2) 0x64 _ (.inr (.inl ⟨rfl, rfl⟩)) R6 Mt4 (by omega) h25'
    h24' k26 k22 DO.tab fun R7 h25'' _ hkp7 => ?_
  have kk : ∀ z, z ≠ 6 → z ≠ 14 → z ≠ 15 → z ≠ 24 → z ≠ 25 → R7 z = R4 z := fun z a b c d e =>
    (hkp7 z b c d e).trans ((hkp6 z a c d).trans (hkp5 z b c d e))
  have St7 := CA.st.update SG (R' := R7) (fun z hz => kk z (by omega) (by omega) (by omega) (by omega) (by omega))
    (kk 23 (by decide) (by decide) (by decide) (by decide) (by decide)) (fun _ _ => rfl) CA.st.core.fmt
    CA.st.core.ret CA.st.core.ap
  have hv' := (ld_ap SG CA.st.core.frame hap1 hap2).trans hv
  refine svf_intL hlive (p + k + 2 + 1) v R7 Mt4 SG St7 CA.sign h25''
    ((hkp7 6 (by decide) (by decide) (by decide) (by decide)).trans h6')
    ((kk 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans CA.r20)
    ((kk 27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans CA.r27) hv' hap1 hap2
    fun R8 Mt8 IA => ?_
  refine svf_intTail hlive v R8 Mt8 SG IA hLl (by omega) (by omega) fun R9 Mt9 g hg A9 => hk R9 Mt9 ?_
  rw [catPieces_lit g hL, show p + k - p = k by omega,
    pieceBytes_congr (g' := imgM Dt) fun i hi => hg _ (DO.stack _ (FG.dom _ (by omega) (by omega)))] at A9
  rw [show p + k + 2 + 1 = p + k + 3 by omega] at A9
  exact A9

end VsaIris.Sym
