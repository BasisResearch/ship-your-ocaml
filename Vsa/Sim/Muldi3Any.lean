import Vsa.Sim.Muldi3Spec

/-!
# `__muldi3` from any scratch-register state

`muldi3_spec` pins `a2`/`a3` (`x12`/`x13`) at entry, but the code writes both
before reading them (`mv a2,a0` at entry; `andi a3,a1,1` first in the loop
body, a do-while). `muldi3_spec_any` drops that entry requirement: the scratch
registers are only *conditionally* pinned (`St0`) until written, after which
the fully pinned states of `Muldi3Spec.lean` take over (the first loop
iteration from `0x40`, then `loop_to_done`). No step is re-derived: the same
`site_*` facts and `tr_*` transitions are reused.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__muldi3Loaded)

namespace Vsa.Sim

theorem muldi3_addi0 (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [sext_zero]; exact BitVec.add_zero v

theorem muldi3_andi1 (v : BitVec 64) : v &&& sign_extend (m := 64) (0x001#12) = v &&& 1#64 := by
  rw [sext_one]

/-- `St` with the scratch registers pinned only when known. -/
structure St0 (g : (R : Register) → Option (RegisterType R))
    (pc a0 a1 r : BitVec 64) (a2 a3 : Option (BitVec 64)) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (o : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : __muldi3Loaded c.σ.mem
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
  hframe : ∀ R : Register, NotWrittenM R → c.σ.regs.get? R = g R

/-- `mv a2,a0` (0x40 → 0x44) from any scratch state. -/
theorem tr0_40_44 (g : (R : Register) → Option (RegisterType R))
    (x y r : BitVec 64) (a2 a3 : Option (BitVec 64)) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St0 g (0x80037234#64) x y r a2 a3 m0 o) (St0 g (0x80037238#64) x y r (some x) a3 m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80037234 c.σ c.tick c.steps (0x80037234#64) vmi x hSt.good hSt.pc hmi hSt.a0 hSt.loaded rfl hSt.tick
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [muldi3_addi0 x] at hrd
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
    fun R hR => (frame_alu_m hobs R hR.x12 hR).trans (hSt.hframe R hR)⟩

/-- `li a0,0` (0x44 → 0x48) with `a3` still unknown. -/
theorem tr0_44_48 (g : (R : Register) → Option (RegisterType R))
    (x y r : BitVec 64) (a2 : Option (BitVec 64)) (a3 : Option (BitVec 64))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St0 g (0x80037238#64) x y r a2 a3 m0 o) (St0 g (0x8003723c#64) (0#64) y r a2 a3 m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80037238 c.σ c.tick c.steps (0x80037238#64) vmi hSt.good hSt.pc hmi hSt.loaded rfl hSt.tick
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [muldi3_addi0 (0#64)] at hrd
  exact ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs, hrd,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    fun v hv => obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hSt.a2 v hv),
    fun v hv => obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hSt.a3 v hv),
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x10 hR).trans (hSt.hframe R hR)⟩

/-- `andi a3,a1,1` (0x48 → 0x4c): `a3` is written, so the fully pinned `St` follows. -/
theorem tr0_48_4c (g : (R : Register) → Option (RegisterType R))
    (y r a0 a2 : BitVec 64) (a3 : Option (BitVec 64)) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St0 g (0x8003723c#64) a0 y r (some a2) a3 m0 o) (St g (0x80037240#64) a0 y a2 (y &&& 1#64) r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_8003723c c.σ c.tick c.steps (0x8003723c#64) vmi y hSt.good hSt.pc hmi hSt.a1 hSt.loaded rfl hSt.tick
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [muldi3_andi1 y] at hrd
  exact ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hSt.a2 _ rfl),
    hrd,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x13 hR).trans (hSt.hframe R hR)⟩

/-- The rest of one loop iteration, from `0x4c` (after the `andi`) to `0x5c`. -/
theorem iter_4c_5c (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hinv : a0 + a2 * a1 = x * y) :
    Triple (St g (0x80037240#64) a0 a1 a2 (a1 &&& 1#64) r m0 o)
           (fun c => ∃ a0', St g (0x80037250#64) a0' (a1 >>> (1:Nat)) (a2 <<< (1:Nat)) (a1 &&& 1#64) r m0 o c
             ∧ a0' + (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) = x * y) := by
  rcases and1_cases a1 with hev | hod
  · have hbeq : ((a1 &&& 1#64) == (0#64)) = true := by rw [hev]; rfl
    have h2 := tr_4c_54 g x a1 r a0 a2 m0 o hbeq
    have h3 := tr_54_58 g x y r a0 a1 a2 (a1 &&& 1#64) m0 o
    have h4 := tr_58_5c g x y r a0 (a1 >>> (1:Nat)) a2 (a1 &&& 1#64) m0 o
    exact (h2.seq (h3.seq h4)).conseq (fun _ h => h) (fun c hc =>
      ⟨a0, hc, by rw [inv_even a0 a1 a2 hev]; exact hinv⟩)
  · have hbne : ((a1 &&& 1#64) == (0#64)) = false := by rw [hod]; rfl
    have h2 := tr_4c_50 g x a1 r a0 a2 m0 o hbne
    have h2' := tr_50_54 g x a1 r a0 a2 (a1 &&& 1#64) m0 o
    have h3 := tr_54_58 g x a1 r (a0 + a2) a1 a2 (a1 &&& 1#64) m0 o
    have h4 := tr_58_5c g x a1 r (a0 + a2) (a1 >>> (1:Nat)) a2 (a1 &&& 1#64) m0 o
    exact ((h2.seq h2').seq (h3.seq h4)).conseq (fun _ h => h) (fun c hc =>
      ⟨a0 + a2, hc, by rw [inv_odd a0 a1 a2 hod]; exact hinv⟩)

/-- Entry from any scratch-register state, with a 4-aligned return address. -/
def muldi3_pre_any (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  (∃ a2 a3, St0 g (0x80037234#64) x y r a2 a3 m0 o c) ∧ r.toNat % 4 = 0

/-- **`__muldi3` without scratch-register presence at entry.** -/
theorem muldi3_spec_any (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (muldi3_pre_any g x y r m0 o) (muldi3_post g x y r m0 o) := by
  -- entry to the first `AtDone` or `AtHead`, through the first iteration
  have hfirst : Triple (muldi3_pre_any g x y r m0 o)
      (fun c => (AtDone g x y r m0 o c ∨ LoopI g x y r m0 o c) ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨⟨a2, a3, hEntry⟩, halign⟩ := hc
    obtain ⟨c1, hs1, hSt1⟩ := tr0_40_44 g x y r a2 a3 m0 o c hEntry
    obtain ⟨c2, hs2, hSt2⟩ := tr0_44_48 g x y r (some x) a3 m0 o c1 hSt1
    obtain ⟨c3, hs3, hSt3⟩ := tr0_48_4c g y r (0#64) x a3 m0 o c2 hSt2
    obtain ⟨c4, hs4, a0', h5c, hinv'⟩ :=
      iter_4c_5c g x y r (0#64) y x m0 o (by rw [BitVec.zero_add]) c3 hSt3
    by_cases hnew : (y >>> (1:Nat)) = 0#64
    · have hbne : ((y >>> (1:Nat)) != (0#64)) = false := by rw [hnew]; rfl
      obtain ⟨c5, hs5, hSt5⟩ :=
        tr_5c_60 g x y r a0' (x <<< (1:Nat)) (y &&& 1#64) (y >>> (1:Nat)) m0 o hbne c4 h5c
      have ha0' : a0' = x * y := by
        have := hinv'; rw [hnew, BitVec.mul_zero, BitVec.add_zero] at this; exact this
      exact ⟨c5, ((hs1.trans hs2).trans hs3).trans (hs4.trans hs5),
        .inl ⟨_, _, _, ha0' ▸ hSt5⟩, halign⟩
    · have hbne : ((y >>> (1:Nat)) != (0#64)) = true := by rw [bne_iff_ne]; exact hnew
      obtain ⟨c5, hs5, hSt5⟩ :=
        tr_5c_48 g x y r a0' (x <<< (1:Nat)) (y &&& 1#64) (y >>> (1:Nat)) m0 o hbne c4 h5c
      exact ⟨c5, ((hs1.trans hs2).trans hs3).trans (hs4.trans hs5),
        .inr (.inl ⟨a0', y >>> (1:Nat), x <<< (1:Nat), y &&& 1#64, hSt5, hinv'⟩), halign⟩
  have hdone : Triple (fun c => (AtDone g x y r m0 o c ∨ LoopI g x y r m0 o c) ∧ r.toNat % 4 = 0)
      (fun c => AtDone g x y r m0 o c ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨hI, halign⟩ := hc
    rcases hI with hDone | hLoop
    · exact ⟨c, .refl c, hDone, halign⟩
    · obtain ⟨c', hs, hDone⟩ := loop_to_done g x y r m0 o c hLoop
      exact ⟨c', hs, hDone, halign⟩
  have hret : Triple (fun c => AtDone g x y r m0 o c ∧ r.toNat % 4 = 0) (muldi3_post g x y r m0 o) := by
    intro c hc
    obtain ⟨⟨a1, a2, a3, hSt⟩, halign⟩ := hc
    obtain ⟨c', hs, hG, hmem, hout, hpc, ha0, ha1, ha2, hra, htick, hframe⟩ :=
      tr_60_ret g x y r (x*y) a1 a2 a3 m0 o halign c hSt
    exact ⟨c', hs, hG, hmem, hout, hpc, ha0, hra, htick, hframe⟩
  exact (hfirst.seq hdone).seq hret

end Vsa.Sim
