import OCaml.Vm.Primitives.FdWrite.Effects
import OCaml.Vm.Primitives.HtifFrame
import OCaml.Vm.Primitives.ExitPath.Machine
import Vsa.Sim.DeriveLoop
import OCaml.Vm.Primitives.Console.Loop

/-! The blocking-section entry and leave of `caml_write_fd`, with the default
hooks and no pending signals. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable
open FdWrite (enterHook leaveHook impurePtr pendingSignals)

/-- A call that changed no memory, kept every listed register and returned. -/
structure QuietReturn (writes : List Nat) (ra : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some ra
  memory : d.σ.mem = c.σ.mem
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ writes → gpr d n = gpr c n

/-- `caml_enter_blocking_section_no_pending` with the default (empty) hook. -/
theorem enter_blocking {ra c} (h : LeafInput ra c)
    (idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4))
    (a0 : ∃ v, gpr c 10 = some v)
    (hook : bytesVal .ld (read8 c.σ.mem enterHook.toNat) = 0x8000d2a4#64)
    (entry : pcOf c = some 0x8000d4ac#64) :
    ∃ d, Steps c d ∧ QuietReturn [15] ra c d := by
  obtain ⟨v, hv⟩ := a0
  let R : Nat → BitVec 64 := fun n => if n = 1 then ra else v
  obtain ⟨d1, run1, p1⟩ := (FdWrite.EnterBlocking.hook_fast c R 0x8000d2a4#64 h ⟨h.raReg, hv, True.intro⟩
    hook (by decide)).run c ⟨entry, rfl⟩
  have keep1 := fun n lo hi (hn : n ∉ [15]) => p1.toEffectPost.gpr_frame (by decide) n lo hi hn
  have ra1 : gpr d1 1 = some ra := (keep1 1 (by decide) (by decide) (by simp)).trans h.raReg
  obtain ⟨d2, run2, p2⟩ := (FdWrite.EnterDefault.leaf_fast d1 R ⟨p1.good, p1.image, p1.minstret, ra1, h.aligned, p1.tick⟩
    ⟨ra1, (keep1 10 (by decide) (by decide) (by simp)).trans hv, True.intro⟩).run d1 ⟨p1.pc, rfl⟩
  exact ⟨d2, run1.trans run2, p2.good, p2.image, p2.minstret, p2.tick,
    p2.toEffectPost.htifIdle (p1.toEffectPost.htifIdle idle), p2.pc,
    by rw [p2.memory, p1.memory]; rfl,
    by unfold Vsa.Machine.output; rw [p2.output, p1.output],
    fun n lo hi hn => (p2.toEffectPost.gpr_frame (by decide) n lo hi (by simp)).trans (keep1 n lo hi hn)⟩


/-- The signal scan's index step: `addiw a5, a5, 1` on a small index. -/
theorem scan_next : ∀ i, i < 32 →
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 i + 1#64)) = BitVec.ofNat 64 (i + 1) := by
  decide

/-- No signal is pending: every `caml_pending_signals` slot reads zero. -/
def NoPendingSignals (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ i, i < 32 → bytesVal .ld (read8 m (pendingSignals + Sail.shift_bits_left (BitVec.ofNat 64 i) 3#6).toNat) = 0#64

theorem slot_window : ∀ i, i < 32 →
    ReadWindow (pendingSignals + Sail.shift_bits_left (BitVec.ofNat 64 i) 3#6) 8 := by
  intro i hi
  have : ∀ i, i < 32 → let a := (pendingSignals + Sail.shift_bits_left (BitVec.ofNat 64 i) 3#6).toNat
      0x80000000 ≤ a ∧ a + 8 ≤ 0x100000000 ∧ Layout.sym_tohost + 8 ≤ a := by decide
  obtain ⟨l, u, t⟩ := this i hi
  exact ⟨l, u, Or.inr t⟩

/-- Fixed facts of the scan, relative to its entry `e`. -/
structure ScanFrame (e d : Config) : Prop where
  ok : LoopOk d
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  memory : d.σ.mem = e.σ.mem
  output : Vsa.Machine.output d.σ = Vsa.Machine.output e.σ
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [14, 15] → gpr d n = gpr e n

inductive ScanState (e : Config) : Config → Prop where
  | scanning {d : Config} (i : Nat) (hi : i < 32) (frame : ScanFrame e d)
      (pc : pcOf d = some 0x8000d4f0#64) (index : gpr d 15 = some (BitVec.ofNat 64 i)) : ScanState e d
  | done {d : Config} (frame : ScanFrame e d) (pc : pcOf d = some 0x8000d528#64) : ScanState e d

def scanMeasure (d : Config) : Nat := 32 - ((gpr d 15).getD 0).toNat

theorem scan_iteration {e d : Config} {i : Nat} (hi : i < 32) (frame : ScanFrame e d)
    (pc : pcOf d = some 0x8000d4f0#64) (index : gpr d 15 = some (BitVec.ofNat 64 i))
    (raE : ∃ v, gpr e 1 = some v ∧ v.toNat % 4 = 0) (spE : ∃ v, gpr e 2 = some v)
    (s0E : ∃ v, gpr e 8 = some v) (a0E : ∃ v, gpr e 10 = some v)
    (bound : gpr e 12 = some 32#64) (base : gpr e 13 = some pendingSignals)
    (clear : NoPendingSignals e.σ.mem) :
    ∃ d', Steps d d' ∧ ScanState e d' ∧ scanMeasure d' < scanMeasure d := by
  obtain ⟨ra, hra, al⟩ := raE; obtain ⟨sp, hsp⟩ := spE; obtain ⟨s0, hs0⟩ := s0E; obtain ⟨a0, ha0⟩ := a0E
  have keep := frame.kept
  let R : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else if n = 8 then s0 else
    if n = 10 then a0 else if n = 12 then 32#64 else if n = 13 then pendingSignals else BitVec.ofNat 64 i
  have regs : GHolds d.σ (FdWrite.LeaveBlocking.slot_input R) :=
    ⟨(keep 1 (by decide) (by decide) (by simp)).trans hra, (keep 2 (by decide) (by decide) (by simp)).trans hsp,
     (keep 8 (by decide) (by decide) (by simp)).trans hs0, (keep 10 (by decide) (by decide) (by simp)).trans ha0,
     (keep 12 (by decide) (by decide) (by simp)).trans bound, (keep 13 (by decide) (by decide) (by simp)).trans base,
     index, True.intro⟩
  have leaf : LeafInput (R 1) d := ⟨frame.ok.good, frame.image, frame.minstret,
    (keep 1 (by decide) (by decide) (by simp)).trans hra, al, frame.ok.tick⟩
  obtain ⟨d1, run1, p1⟩ := (FdWrite.LeaveBlocking.slot_fast d R leaf regs (slot_window i hi)
    (by rw [frame.memory]; exact clear i hi)).run d ⟨pc, rfl⟩
  have next : gpr d1 15 = some (BitVec.ofNat 64 (i + 1)) := by
    have l : gpr d1 15 = some (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (R 15 + 1#64))) :=
      gholds_lookup _ p1.regs rfl
    rw [l]; simp only [R, ↓reduceIte, Nat.reduceEqDiff]; rw [scan_next i hi]
  have keep1 := fun n lo hi' (hn : n ∉ [14, 15]) => p1.toEffectPost.gpr_frame (by decide) n lo hi' hn
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else if n = 8 then s0 else
    if n = 10 then a0 else if n = 12 then 32#64 else if n = 13 then pendingSignals else BitVec.ofNat 64 (i + 1)
  have regs1 : GHolds d1.σ (FdWrite.LeaveBlocking.more_input R1) :=
    ⟨(keep1 1 (by decide) (by decide) (by simp)).trans ((keep 1 (by decide) (by decide) (by simp)).trans hra),
     (keep1 2 (by decide) (by decide) (by simp)).trans ((keep 2 (by decide) (by decide) (by simp)).trans hsp),
     (keep1 8 (by decide) (by decide) (by simp)).trans ((keep 8 (by decide) (by decide) (by simp)).trans hs0),
     (keep1 10 (by decide) (by decide) (by simp)).trans ((keep 10 (by decide) (by decide) (by simp)).trans ha0),
     (keep1 12 (by decide) (by decide) (by simp)).trans ((keep 12 (by decide) (by decide) (by simp)).trans bound),
     (keep1 13 (by decide) (by decide) (by simp)).trans ((keep 13 (by decide) (by decide) (by simp)).trans base),
     next, True.intro⟩
  have leaf1 : LeafInput (R1 1) d1 := ⟨p1.good, p1.image, p1.minstret,
    (keep1 1 (by decide) (by decide) (by simp)).trans ((keep 1 (by decide) (by decide) (by simp)).trans hra), al, p1.tick⟩
  have ok1 := p1.loopOk frame.ok
  have frame2 := fun {pc' : BitVec 64} {regs' : GRegs} {d2 : Config}
      (p2 : WriteRegistersPost [] [] d1 pc' (R1 10) regs' d2) =>
    (⟨p2.loopOk ok1, p2.image, p2.minstret, by rw [p2.memory, p1.memory]; exact frame.memory,
      by unfold Vsa.Machine.output at *; rw [p2.output, p1.output]; exact frame.output,
      fun n lo hi' hn => (p2.toEffectPost.gpr_frame (by decide) n lo hi' (by simp)).trans
        ((keep1 n lo hi' hn).trans (keep n lo hi' hn))⟩ : ScanFrame e d2)
  have measure0 : scanMeasure d = 32 - i := by
    unfold scanMeasure; rw [index]; simp only [Option.getD_some, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  by_cases more : i + 1 < 32
  · obtain ⟨d2, run2, p2⟩ := (FdWrite.LeaveBlocking.more_fast d1 R1 leaf1 regs1 (by
      simp only [R1, ↓reduceIte, Nat.reduceEqDiff]
      intro eq; have := congrArg BitVec.toNat eq; simp at this; omega)).run d1 ⟨p1.pc, rfl⟩
    have idx2 : gpr d2 15 = some (BitVec.ofNat 64 (i + 1)) :=
      (p2.toEffectPost.gpr_frame (by decide) 15 (by decide) (by decide) (by simp)).trans next
    refine ⟨d2, run1.trans run2, .scanning (i + 1) more (frame2 p2) p2.pc idx2, ?_⟩
    rw [measure0]; unfold scanMeasure; rw [idx2]; simp only [Option.getD_some, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · have last : i + 1 = 32 := by omega
    obtain ⟨d2, run2, p2⟩ := (FdWrite.LeaveBlocking.last_fast d1 R1 leaf1 regs1 (by
      simp only [R1, ↓reduceIte, Nat.reduceEqDiff, last])).run d1 ⟨p1.pc, rfl⟩
    have idx2 : gpr d2 15 = some (BitVec.ofNat 64 (i + 1)) :=
      (p2.toEffectPost.gpr_frame (by decide) 15 (by decide) (by decide) (by simp)).trans next
    refine ⟨d2, run1.trans run2, .done (frame2 p2) p2.pc, ?_⟩
    rw [measure0]; unfold scanMeasure; rw [idx2, last]; simp only [Option.getD_some, BitVec.toNat_ofNat]; omega

end OCaml.Vm.Primitives.ConsoleWrite
