import Vsa.Sim.DivLoops

/-!
# `__udivdi3` from any scratch-register state

`udivdi3_spec` pins `a2`/`a3` (`x12`/`x13`) at entry, but with a nonzero
divisor the code writes both before reading them (`mv a2,a1`; then
`li a3,1` after the not-taken `beqz a2`). `udivdi3_spec_any` drops that entry
requirement: `Ust0` pins the scratch registers only once known; five weak
prefix steps (reusing the same `site_*` facts) reach the fully pinned `Ust` at
`0xc0`, after which `udivdi3_spec`'s own composition (normalize loop, divide
loop, return) is restated over its public lemmas.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

namespace Vsa.Sim

/-- `Ust` with the scratch registers pinned only when known. -/
structure Ust0 (g : (R : Register) → Option (RegisterType R))
    (pc a0 a1 r : BitVec 64) (a2 a3 : Option (BitVec 64)) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (o : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : __hidden___udivdi3Loaded c.σ.mem
  mem : c.σ.mem = m0
  sailOut : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some pc
  a0 : c.σ.regs.get? Register.x10 = some a0
  a1 : c.σ.regs.get? Register.x11 = some a1
  a2 : ∀ v, a2 = some v → c.σ.regs.get? Register.x12 = some v
  a3 : ∀ v, a3 = some v → c.σ.regs.get? Register.x13 = some v
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  hframe : ∀ R : Register, NotWritten R → c.σ.regs.get? R = g R

/-- `mv a2,a1` (ac → b0). -/
theorem utr0_ac_b0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 r : BitVec 64) (a2 a3 : Option (BitVec 64)) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust0 g (0x800372a0#64) a0 a1 r a2 a3 m0 o) (Ust0 g (0x800372a4#64) a0 a1 r (some a1) a3 m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800372a0 c.σ c.tick c.steps (0x800372a0#64) vmi a1 hSt.good hSt.pc hmi hSt.a1 hSt.loaded rfl hSt.tick
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show a1 + sign_extend (m := 64) (0x000#12) = a1 from by rw [sext_zero]; exact BitVec.add_zero a1] at hrd
  exact ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    fun v hv => by cases hv; exact hrd,
    fun v hv => obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hSt.a3 v hv),
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x12 hR).trans (hSt.hframe R hR)⟩

/-- `mv a1,a0` (b0 → b4). -/
theorem utr0_b0_b4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1old r : BitVec 64) (a2 a3 : Option (BitVec 64)) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust0 g (0x800372a4#64) a0 a1old r a2 a3 m0 o) (Ust0 g (0x800372a8#64) a0 a0 r a2 a3 m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800372a4 c.σ c.tick c.steps (0x800372a4#64) vmi a0 hSt.good hSt.pc hmi hSt.a0 hSt.loaded rfl hSt.tick
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show a0 + sign_extend (m := 64) (0x000#12) = a0 from by rw [sext_zero]; exact BitVec.add_zero a0] at hrd
  exact ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    hrd,
    fun v hv => obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hSt.a2 v hv),
    fun v hv => obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hSt.a3 v hv),
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x11 hR).trans (hSt.hframe R hR)⟩

/-- `li a0,-1` (b4 → b8). -/
theorem utr0_b4_b8 (g : (R : Register) → Option (RegisterType R))
    (a0old a1 r : BitVec 64) (a2 a3 : Option (BitVec 64)) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust0 g (0x800372a8#64) a0old a1 r a2 a3 m0 o)
           (Ust0 g (0x800372ac#64) ((0#64) + sign_extend (m := 64) (0xfff#12)) a1 r a2 a3 m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800372a8 c.σ c.tick c.steps (0x800372a8#64) vmi hSt.good hSt.pc hmi hSt.loaded rfl hSt.tick
  exact ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide),
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    fun v hv => obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hSt.a2 v hv),
    fun v hv => obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hSt.a3 v hv),
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x10 hR).trans (hSt.hframe R hR)⟩

/-- `beqz a2` not taken (b8 → bc, a2 ≠ 0). -/
theorem utr0_b8_bc (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 r : BitVec 64) (a3 : Option (BitVec 64)) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : (a2 == (0#64)) = false) :
    Triple (Ust0 g (0x800372ac#64) a0 a1 r (some a2) a3 m0 o) (Ust0 g (0x800372b0#64) a0 a1 r (some a2) a3 m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046b8_nottaken c.σ c.tick c.steps (0x800372ac#64) vmi a2 hSt.good hSt.pc hmi (hSt.a2 _ rfl) hSt.loaded rfl hv hSt.tick
  exact ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_bnottaken_pc hobs,
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    fun v hv => obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hSt.a2 v hv),
    fun v hv => obs_bnottaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hSt.a3 v hv),
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_bnottaken_minstret hobs, hi',
    fun R hR => (frame_bnottaken hobs R hR).trans (hSt.hframe R hR)⟩

/-- `li a3,1` (bc → c0): `a3` is written, so the fully pinned `Ust` follows. -/
theorem utr0_bc_c0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 r : BitVec 64) (a3 : Option (BitVec 64)) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust0 g (0x800372b0#64) a0 a1 r (some a2) a3 m0 o)
           (Ust g (0x800372b4#64) a0 a1 a2 ((0#64) + sign_extend (m := 64) (0x001#12)) r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800372b0 c.σ c.tick c.steps (0x800372b0#64) vmi hSt.good hSt.pc hmi hSt.loaded rfl hSt.tick
  exact ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hSt.a2 _ rfl),
    obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide),
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x13 hR).trans (hSt.hframe R hR)⟩

/-- `li a0,-1`'s value (as `DivLoops`' private `udivNeg1`). -/
def udivNeg1 : BitVec 64 := (0#64) + sign_extend (m := 64) (0xfff#12)

theorem udiv_one_c : ((0#64) + sign_extend (m := 64) (0x001#12) : BitVec 64) = (1#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- Entry from any scratch-register state, a nonzero divisor and a 4-aligned return. -/
def udivdi3_pre_any (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  (∃ a2 a3, Ust0 g (0x800372a0#64) n d r a2 a3 m0 o c) ∧ 0 < d.toNat ∧ r.toNat % 4 = 0

/-- **`__udivdi3` without scratch-register presence at entry.** -/
theorem udivdi3_spec_any (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (udivdi3_pre_any g n d r m0 o) (udivdi3_post g n d r m0 o) := by
  have hpre : Triple (udivdi3_pre_any g n d r m0 o)
      (fun c => Ust g (0x800372b4#64) udivNeg1 n d (1#64) r m0 o c ∧ 0 < d.toNat ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨⟨a2, a3, hEntry⟩, hd, halign⟩ := hc
    obtain ⟨c1, hs1, hSt1⟩ := utr0_ac_b0 g n d r a2 a3 m0 o c hEntry
    obtain ⟨c2, hs2, hSt2⟩ := utr0_b0_b4 g n d r (some d) a3 m0 o c1 hSt1
    obtain ⟨c3, hs3, hSt3⟩ := utr0_b4_b8 g n n r (some d) a3 m0 o c2 hSt2
    have hbeq : (d == (0#64)) = false := by
      have hne : d ≠ 0#64 := by intro h; rw [h] at hd; simp at hd
      simpa using hne
    obtain ⟨c4, hs4, hSt4⟩ := utr0_b8_bc g udivNeg1 n d r a3 m0 o hbeq c3 hSt3
    obtain ⟨c5, hs5, hSt5⟩ := utr0_bc_c0 g udivNeg1 n d r a3 m0 o c4 hSt4
    rw [udiv_one_c] at hSt5
    exact ⟨c5, hs1.trans (hs2.trans (hs3.trans (hs4.trans hs5))), hSt5, hd, halign⟩
  -- entry_c0 → NrmI → AtDoneN g (normalize loop)
  have hnorm : Triple (fun c => Ust g (0x800372b4#64) udivNeg1 n d (1#64) r m0 o c ∧ 0 < d.toNat ∧ r.toNat % 4 = 0)
      (fun c => AtDoneN g d n udivNeg1 r m0 o c ∧ 0 < d.toNat ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨hSt, hd, halign⟩ := hc
    obtain ⟨c1, hs1, hI⟩ := entry_c0 g d n udivNeg1 r m0 o hd d.isLt c hSt
    obtain ⟨c2, hs2, hDone⟩ := norm_loop_to_done g d n udivNeg1 r m0 o hd c1 hI
    exact ⟨c2, hs1.trans hs2, hDone, hd, halign⟩
  -- d4 → d8 (li a0,0) entering divide loop, then div_loop_to_done → AtDoneD
  have hdiv : Triple (fun c => AtDoneN g d n udivNeg1 r m0 o c ∧ 0 < d.toNat ∧ r.toNat % 4 = 0)
      (fun c => AtDoneD g d n r m0 o c ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨⟨a2, a3, hSt, ⟨K, hk2, hk3, hkbnd⟩, hn2a2⟩, hd, halign⟩ := hc
    -- utr_d4_d8: a0 := 0
    obtain ⟨c1, hs1, hSt1⟩ := utr_d4_d8 g udivNeg1 n a2 a3 r m0 o c hSt
    -- AtHeadD g with j = K, a0 = 0
    have hHead : AtHeadD g d n r m0 o c1 := by
      refine ⟨0#64, n, a2, a3, hSt1, K, ⟨hk2, hk3, hkbnd⟩, ?_, ?_, hn2a2⟩
      · simp
      · simp
    obtain ⟨c2, hs2, hDone⟩ := div_loop_to_done g d n r m0 o hd c1 (Or.inl hHead)
    exact ⟨c2, hs1.trans hs2, hDone, halign⟩
  -- f0 → ret
  have hret : Triple (fun c => AtDoneD g d n r m0 o c ∧ r.toNat % 4 = 0) (udivdi3_post g n d r m0 o) := by
    -- Inline the `f0 → ret` step (mirrors `utr_f0_ret`) so we additionally read
    -- back `x12 = a2` and `x13 = a3` off the `ret` (`jr x0` writes only PC): the
    -- divide loop leaves them defined (`AtDoneD`'s `Ust` pins them).
    apply Triple.of_step
    intro c hc
    obtain ⟨⟨a0, a1, a2, a3, hSt, hq, hr⟩, halign⟩ := hc
    obtain ⟨vmi, hmi⟩ := hSt.minstret
    have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
      rw [ret_tgt r halign]; exact halign
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_800372e4 c.σ c.tick c.steps (0x800372e4#64) vmi r hSt.good hSt.pc hmi hSt.ra hSt.loaded rfl htgt hSt.tick
    -- a0 = n/d, a1 = n%d as BitVec
    have ha0eq : a0 = n / d := by apply BitVec.eq_of_toNat_eq; rw [hq, BitVec.toNat_udiv]
    have ha1eq : a1 = n % d := by apply BitVec.eq_of_toNat_eq; rw [hr, BitVec.toNat_umod]
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
      hG', by rw [hmem']; exact hSt.mem, by rw [hobs.out]; exact hSt.sailOut, by rw [obs_jr_pc hobs, ret_tgt r halign],
      ha0eq ▸ obs_jr_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
      ha1eq ▸ obs_jr_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
      obs_jr_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
      hi',
      fun R hR => (frame_jr hobs R hR).trans (hSt.hframe R hR),
      ⟨a2, obs_jr_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2⟩,
      ⟨a3, obs_jr_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3⟩⟩
  exact (((hpre.seq hnorm).seq hdiv).seq hret)

end Vsa.Sim
