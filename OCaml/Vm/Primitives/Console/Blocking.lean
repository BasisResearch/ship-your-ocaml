import OCaml.Vm.Primitives.FdWrite.Effects
import OCaml.Vm.Primitives.HtifFrame
import OCaml.Vm.Primitives.ExitPath.Machine
import Vsa.Sim.DeriveLoop
import OCaml.Vm.Primitives.Console.Loop
import OCaml.Vm.Primitives.Console.Write

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


/-- The whole scan: 32 empty slots, then the exit at `0x8000d528`. -/
theorem scan_loop {e : Config} (ok : LoopOk e) (image : ExecutableImage e)
    (minstret : ∃ v, e.σ.regs.get? Register.minstret = some v)
    (pc : pcOf e = some 0x8000d4f0#64) (index : gpr e 15 = some 0#64)
    (raE : ∃ v, gpr e 1 = some v ∧ v.toNat % 4 = 0) (spE : ∃ v, gpr e 2 = some v)
    (s0E : ∃ v, gpr e 8 = some v) (a0E : ∃ v, gpr e 10 = some v)
    (bound : gpr e 12 = some 32#64) (base : gpr e 13 = some pendingSignals)
    (clear : NoPendingSignals e.σ.mem) :
    ∃ d, Steps e d ∧ ScanFrame e d ∧ pcOf d = some 0x8000d528#64 := by
  have body : ∀ n, Vsa.Logic.Triple
      (fun d => ScanState e d ∧ pcOf d = some 0x8000d4f0#64 ∧ scanMeasure d = n)
      (fun d => ScanState e d ∧ scanMeasure d < n) := by
    intro n d pre
    obtain ⟨state, head, measure⟩ := pre
    cases state with
    | scanning i hi frame _ idx =>
      obtain ⟨d', run, state', lt⟩ := scan_iteration hi frame head idx raE spE s0E a0E bound base clear
      exact ⟨d', run, state', measure ▸ lt⟩
    | done _ pc' =>
      exact absurd (pc'.symm.trans head) (by decide)
  have start : ScanState e e := .scanning 0 (by decide)
    ⟨ok, image, minstret, rfl, rfl, fun _ _ _ _ => rfl⟩ pc (by rw [index])
  obtain ⟨d, run, state, stopped⟩ := loopFromBody scanMeasure body e start
  cases state with
  | scanning _ _ _ pc' _ => exact absurd pc' stopped
  | done frame pc' => exact ⟨d, run, frame, pc'⟩


/-- `caml_leave_blocking_section`'s requirements: its 16-byte frame, the
default leave hook, the reentrancy structure's `errno` word, and no pending
signal; the frame misses all of them. -/
structure LeaveInput (ra sp s0 rp errv : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  stack : gpr c 2 = some sp
  s0Reg : gpr c 8 = some s0
  a0 : ∃ v, gpr c 10 = some v
  frameLow : WriteWindow (sp - 16#64) 8
  frameHigh : WriteWindow (sp - 16#64 + 8#64) 8
  text : Image.textBase + Image.textSize ≤ sp.toNat - 16 ∨ sp.toNat ≤ Image.textBase
  rodata : Image.rodataBase + Image.rodataSize ≤ sp.toNat - 16 ∨ sp.toNat ≤ Image.rodataBase
  hook : bytesVal .ld (read8 c.σ.mem leaveHook.toNat) = 0x8000d2a8#64
  impure : bytesVal .ld (read8 c.σ.mem impurePtr.toNat) = rp
  errnoWrite : WriteWindow rp 4
  errnoValue : bytesVal .lw (read8 c.σ.mem rp.toNat) = errv
  errnoText : rp.toNat + 4 ≤ Image.textBase ∨ Image.textBase + Image.textSize ≤ rp.toNat
  errnoRodata : rp.toNat + 4 ≤ Image.rodataBase ∨ Image.rodataBase + Image.rodataSize ≤ rp.toNat
  apart : ∀ a ∈ [leaveHook.toNat, impurePtr.toNat, rp.toNat], a + 8 ≤ sp.toNat - 16 ∨ sp.toNat ≤ a
  errnoFrame : rp.toNat + 4 ≤ sp.toNat - 16 ∨ sp.toNat ≤ rp.toNat
  pending : pendingSignals.toNat + 256 ≤ sp.toNat - 16 ∨ sp.toNat ≤ pendingSignals.toNat
  clear : NoPendingSignals c.σ.mem

structure LeavePost (ra sp s0 rp : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some ra
  raReg : gpr d 1 = some ra
  stack : gpr d 2 = some sp
  s0Reg : gpr d 8 = some s0
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 8, 10, 12, 13, 14, 15] → gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ
  frame : ∀ x, (x < sp.toNat - 16 ∨ sp.toNat ≤ x) → (x < rp.toNat ∨ rp.toNat + 4 ≤ x) →
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0

theorem leave_blocking {ra sp s0 rp errv c} (h : LeaveInput ra sp s0 rp errv c)
    (entry : pcOf c = some 0x8000d4b8#64) :
    ∃ d, Steps c d ∧ LeavePost ra sp s0 rp c d := by
  obtain ⟨a0v, ha0⟩ := h.a0
  have sp16 : (sp - 16#64).toNat = sp.toNat - 16 := by
    have l := h.frameLow.lower; have u := h.frameLow.upper
    rw [BitVec.toNat_sub] at l u ⊢
    have := sp.isLt
    simp only [BitVec.toNat_ofNat] at l u ⊢
    omega
  have sp8 : (sp - 16#64 + 8#64).toNat = sp.toNat - 8 := by
    have l := h.frameLow.lower; have u := h.frameLow.upper; rw [sp16] at l u
    rw [BitVec.toNat_add, sp16]; simp; omega
  have low := h.frameLow.lower; rw [sp16] at low
  -- save ra and s0
  let R0 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else if n = 8 then s0 else a0v
  have within : ExitPath.LogWithin (FdWrite.LeaveBlocking.enterLog R0) (sp.toNat - 16) sp.toNat := by
    intro e he
    simp only [FdWrite.LeaveBlocking.enterLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl <;> (simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; omega)
  obtain ⟨d1, run1, p1⟩ := (FdWrite.LeaveBlocking.enter_fast c R0 h.toLeafInput
    ⟨h.raReg, h.stack, h.s0Reg, ha0, True.intro⟩ h.frameLow h.frameHigh
    ⟨within.outLRange h.text, within.outLRange h.rodata⟩).run c ⟨entry, rfl⟩
  have mem1 : d1.σ.mem = writeLog c.σ.mem (FdWrite.LeaveBlocking.enterLog R0) := p1.memory
  have read1 : ∀ a, (a + 8 ≤ sp.toNat - 16 ∨ sp.toNat ≤ a) → read8 d1.σ.mem a = read8 c.σ.mem a := by
    intro a ha; rw [mem1]; exact read8_outside within ha
  have loop0 : LoopOk c := ⟨h.good, h.tick, h.idle⟩
  -- __errno: a0 = the reentrancy pointer
  have J1 := call_registers_summary FdWrite.LeaveBlocking.enter_call_shape FdWrite.LeaveBlocking.enter_call_decode d1
    (FdWrite.LeaveBlocking.enter_call_pins p1.image) p1.good p1.image p1.tick p1.minstret
    [(2, sp - 16#64), (8, s0), (10, a0v)]
    ⟨gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, True.intro⟩
    (by change KeysOK [2, 8, 10]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  obtain ⟨d2, run2, q2⟩ := J1.run d1 ⟨p1.pc, rfl⟩
  let R2 : Nat → BitVec 64 := fun _ => FdWrite.LeaveBlocking.enter_call.link
  obtain ⟨d3, run3, p3⟩ := (FdWrite.Errno.leaf_fast d2 R2
    ⟨q2.good, q2.image, q2.minstret, gholds_lookup _ q2.regs rfl, by simp only [R2]; decide, q2.tick⟩
    ⟨gholds_lookup _ q2.regs rfl, True.intro⟩).run d2 ⟨by show pcOf _ = _; rw [q2.pc]; rfl, rfl⟩
  have mem3 : d3.σ.mem = writeLog c.σ.mem (FdWrite.LeaveBlocking.enterLog R0) := by
    rw [p3.memory, show writeLog d2.σ.mem [] = d2.σ.mem from rfl, q2.memory, mem1]
  have rp3 : gpr d3 10 = some rp := by
    have l : gpr d3 10 = some (bytesVal .ld (read8 d2.σ.mem impurePtr.toNat)) := gholds_lookup _ p3.regs rfl
    rw [l, q2.memory, read1 _ (h.apart _ (by simp))]; rw [h.impure]
  -- load the hook and the saved errno
  let R3 : Nat → BitVec 64 := fun n => if n = 1 then FdWrite.LeaveBlocking.enter_call.link else
    if n = 2 then sp - 16#64 else rp
  have link3 : gpr d3 1 = some FdWrite.LeaveBlocking.enter_call.link := gholds_lookup _ p3.regs rfl
  have sp3 : gpr d3 2 = some (sp - 16#64) :=
    (p3.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by simp)).trans
      ((q2.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl))
  obtain ⟨d4, run4, p4⟩ := (FdWrite.LeaveBlocking.hook_fast d3 R3
    ⟨p3.good, p3.image, p3.minstret, link3, by simp only [R3, ↓reduceIte]; decide, p3.tick⟩ ⟨link3, sp3, rp3, True.intro⟩
    h.errnoWrite.read).run d3 ⟨p3.pc, rfl⟩
  have hook4 : gpr d4 15 = some 0x8000d2a8#64 := by
    have l : gpr d4 15 = some (bytesVal .ld (read8 d3.σ.mem leaveHook.toNat)) := gholds_lookup _ p4.regs rfl
    rw [l, mem3, read8_outside within (h.apart _ (by simp)), h.hook]
  have errv4 : gpr d4 8 = some errv := by
    have l : gpr d4 8 = some (bytesVal .lw (read8 d3.σ.mem rp.toNat)) := gholds_lookup _ p4.regs rfl
    rw [l, mem3, read8_outside within (h.apart _ (by simp)), h.errnoValue]
  -- the default leave hook
  have J4 := indirect_registers_summary FdWrite.LeaveBlocking.hook_call_shape FdWrite.LeaveBlocking.hook_call_decode d4
    (FdWrite.LeaveBlocking.hook_call_pins p4.image) p4.good p4.image p4.tick p4.minstret
    [(2, sp - 16#64), (8, errv), (10, rp), (15, 0x8000d2a8#64)]
    ⟨gholds_lookup _ p4.regs rfl, errv4, gholds_lookup _ p4.regs rfl, hook4, True.intro⟩
    (by change KeysOK [2, 8, 10, 15]; decide) (by simp [KeysAvoidRa, keysG]) 0x8000d2a8#64 rfl (by decide) rfl
  obtain ⟨d5, run5, q5⟩ := J4.run d4 ⟨p4.pc, rfl⟩
  let R5 : Nat → BitVec 64 := fun n => if n = 1 then FdWrite.LeaveBlocking.hook_call.link else rp
  obtain ⟨d6, run6, p6⟩ := (FdWrite.LeaveDefault.leaf_fast d5 R5
    ⟨q5.good, q5.image, q5.minstret, gholds_lookup _ q5.regs rfl, by simp only [R5, ↓reduceIte]; decide, q5.tick⟩
    ⟨gholds_lookup _ q5.regs rfl, gholds_lookup _ q5.regs rfl, True.intro⟩).run d5 ⟨by show pcOf _ = _; rw [q5.pc]; rfl, rfl⟩
  -- the pending-signal scan
  let R6 : Nat → BitVec 64 := fun n => if n = 1 then FdWrite.LeaveBlocking.hook_call.link else
    if n = 2 then sp - 16#64 else if n = 8 then errv else rp
  have keep6 := fun n lo hi (hn : n ≠ 1) =>
    (p6.toEffectPost.gpr_frame (by decide) n lo hi (by simp)).trans
      (q5.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn))
  have link6 : gpr d6 1 = some FdWrite.LeaveBlocking.hook_call.link := gholds_lookup _ p6.regs rfl
  obtain ⟨d7, run7, p7⟩ := (FdWrite.LeaveBlocking.scan_fast d6 R6
    ⟨p6.good, p6.image, p6.minstret, link6, by simp only [R6, ↓reduceIte]; decide, p6.tick⟩
    ⟨link6, (keep6 2 (by decide) (by decide) (by decide)).trans (gholds_lookup _ p4.regs rfl),
      (keep6 8 (by decide) (by decide) (by decide)).trans errv4,
      (keep6 10 (by decide) (by decide) (by decide)).trans (gholds_lookup _ p4.regs rfl), True.intro⟩).run d6 ⟨p6.pc, rfl⟩
  have mem7 : d7.σ.mem = writeLog c.σ.mem (FdWrite.LeaveBlocking.enterLog R0) := by
    rw [p7.memory, show writeLog d6.σ.mem [] = d6.σ.mem from rfl, p6.memory, show writeLog d5.σ.mem [] = d5.σ.mem from rfl,
      q5.memory, p4.memory, show writeLog d3.σ.mem [] = d3.σ.mem from rfl, mem3]
  have slots : ∀ i, i < 32 → (pendingSignals + Sail.shift_bits_left (BitVec.ofNat 64 i) 3#6).toNat =
      pendingSignals.toNat + 8 * i := by decide
  have clear7 : NoPendingSignals d7.σ.mem := by
    intro i hi
    rw [mem7, read8_outside within (by rw [slots i hi]; have := h.pending; omega)]
    exact h.clear i hi
  have ok7 : LoopOk d7 := p7.loopOk (p6.loopOk (q5.loopOk (p4.loopOk (p3.loopOk (q2.loopOk (p1.loopOk loop0))))))
  obtain ⟨d8, run8, f8, pc8⟩ := scan_loop ok7 p7.image p7.minstret p7.pc (gholds_lookup _ p7.regs rfl)
    ⟨_, gholds_lookup _ p7.regs rfl, by simp only [R6, ↓reduceIte]; decide⟩ ⟨_, gholds_lookup _ p7.regs rfl⟩ ⟨_, gholds_lookup _ p7.regs rfl⟩
    ⟨_, gholds_lookup _ p7.regs rfl⟩ (gholds_lookup _ p7.regs rfl) (gholds_lookup _ p7.regs rfl) clear7
  have keep8 := fun n lo hi (hn : n ∉ [14, 15]) => f8.kept n lo hi hn
  have r8 := fun n (hn : n ∈ [1, 2, 8, 10]) (v : BitVec 64) (hv : lookupG n (FdWrite.LeaveBlocking.scan_regs R6 []) = some v) =>
    (keep8 n (by simp at hn; omega) (by simp at hn; omega) (by simp at hn ⊢; omega)).trans (gholds_lookup _ p7.regs hv)
  -- __errno again, then restore errno and return
  obtain ⟨d9, run9, p9⟩ := (FdWrite.LeaveBlocking.errno_fast d8 R6
    ⟨f8.ok.good, f8.image, f8.minstret, r8 1 (by simp) _ rfl, by simp only [R6, ↓reduceIte]; decide, f8.ok.tick⟩
    ⟨r8 1 (by simp) _ rfl, r8 2 (by simp) _ rfl, r8 8 (by simp) _ rfl, r8 10 (by simp) _ rfl, True.intro⟩).run d8 ⟨pc8, rfl⟩
  have J9 := call_registers_summary FdWrite.LeaveBlocking.errno_call_shape FdWrite.LeaveBlocking.errno_call_decode d9
    (FdWrite.LeaveBlocking.errno_call_pins p9.image) p9.good p9.image p9.tick p9.minstret
    [(2, sp - 16#64), (8, errv), (10, rp)]
    ⟨gholds_lookup _ p9.regs rfl, gholds_lookup _ p9.regs rfl, gholds_lookup _ p9.regs rfl, True.intro⟩
    (by change KeysOK [2, 8, 10]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  obtain ⟨d10, run10, q10⟩ := J9.run d9 ⟨p9.pc, rfl⟩
  let R10 : Nat → BitVec 64 := fun _ => FdWrite.LeaveBlocking.errno_call.link
  obtain ⟨d11, run11, p11⟩ := (FdWrite.Errno.leaf_fast d10 R10
    ⟨q10.good, q10.image, q10.minstret, gholds_lookup _ q10.regs rfl, by simp only [R10]; decide, q10.tick⟩
    ⟨gholds_lookup _ q10.regs rfl, True.intro⟩).run d10 ⟨by show pcOf _ = _; rw [q10.pc]; rfl, rfl⟩
  have mem11 : d11.σ.mem = writeLog c.σ.mem (FdWrite.LeaveBlocking.enterLog R0) := by
    rw [p11.memory, show writeLog d10.σ.mem [] = d10.σ.mem from rfl, q10.memory, p9.memory,
      show writeLog d8.σ.mem [] = d8.σ.mem from rfl, f8.memory, mem7]
  let R11 : Nat → BitVec 64 := fun n => if n = 1 then FdWrite.LeaveBlocking.errno_call.link else
    if n = 2 then sp - 16#64 else if n = 8 then errv else rp
  have keep11 := fun n lo hi (hn : n ∉ [1, 10]) =>
    (p11.toEffectPost.gpr_frame (by decide) n lo hi (by simp at hn ⊢; omega)).trans
      (q10.toEffectPost.gpr_frame (by decide) n lo hi (by simp at hn ⊢; omega))
  have rp11 : gpr d11 10 = some rp := by
    have l : gpr d11 10 = some (bytesVal .ld (read8 d10.σ.mem impurePtr.toNat)) := gholds_lookup _ p11.regs rfl
    rw [l, q10.memory, p9.memory, show writeLog d8.σ.mem [] = d8.σ.mem from rfl, f8.memory, mem7,
      read8_outside within (h.apart _ (by simp)), h.impure]
  have retWithin : ExitPath.LogWithin (FdWrite.LeaveBlocking.retLog R11) rp.toNat (rp.toNat + 4) := by
    intro e he
    simp only [FdWrite.LeaveBlocking.retLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he; simp only [R11, ↓reduceIte, Nat.reduceEqDiff]; omega
  have back : ∀ a, sp.toNat - 16 ≤ a → a + 8 ≤ sp.toNat →
      read8 (writeLog d11.σ.mem (FdWrite.LeaveBlocking.retLog R11)) a = read8 d11.σ.mem a := by
    intro a ha hb
    have := h.errnoFrame
    exact read8_outside retWithin (by omega)
  have raBack : bytesVal .ld (read8 (writeLog d11.σ.mem (FdWrite.LeaveBlocking.retLog R11)) (R11 2 + 8#64).toNat) = ra := by
    simp only [R11, ↓reduceIte, Nat.reduceEqDiff]
    rw [back _ (by rw [sp8]; omega) (by rw [sp8]; omega), mem11, read8_value]
    exact Gc.word_writeLog_at _ _ 0 _ _ rfl ⟨by simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; rw [sp16, sp8]; omega, trivial⟩
  have s0Back : bytesVal .ld (read8 (writeLog d11.σ.mem (FdWrite.LeaveBlocking.retLog R11)) (R11 2).toNat) = s0 := by
    simp only [R11, ↓reduceIte, Nat.reduceEqDiff]
    rw [back _ (by rw [sp16]; omega) (by rw [sp16]; omega), mem11, read8_value]
    exact Gc.word_writeLog_at _ _ 1 _ _ rfl trivial
  have link11 : gpr d11 1 = some FdWrite.LeaveBlocking.errno_call.link := gholds_lookup _ p11.regs rfl
  obtain ⟨d12, run12, p12⟩ := (FdWrite.LeaveBlocking.ret_fast d11 ra R11
    ⟨p11.good, p11.image, p11.minstret, link11, by simp only [R11, ↓reduceIte]; decide, p11.tick⟩
    ⟨(keep11 2 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p9.regs rfl),
      (keep11 8 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p9.regs rfl), rp11, True.intro⟩
    h.errnoWrite h.frameHigh.read h.frameLow.read
    ⟨retWithin.outLRange (by have := h.errnoText; omega), retWithin.outLRange (by have := h.errnoRodata; omega)⟩
    raBack h.aligned).run d11 ⟨p11.pc, rfl⟩
  have ok12 : LoopOk d12 := p12.loopOk (p11.loopOk (q10.loopOk (p9.loopOk f8.ok)))
  refine ⟨d12, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
    (run9.trans (run10.trans (run11.trans run12)))))))))),
    p12.good, p12.image, p12.minstret, p12.tick, ok12.htifIdle, p12.pc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have l : gpr d12 1 = some (bytesVal .ld (read8 (writeLog d11.σ.mem (FdWrite.LeaveBlocking.retLog R11))
        (R11 2 + 8#64).toNat)) := gholds_lookup _ p12.regs rfl
    rw [l, raBack]
  · have l : gpr d12 2 = some (R11 2 + 16#64) := gholds_lookup _ p12.regs rfl
    rw [l]; simp only [R11, ↓reduceIte, Nat.reduceEqDiff, BitVec.sub_add_cancel]
  · have l : gpr d12 8 = some (bytesVal .ld (read8 (writeLog d11.σ.mem (FdWrite.LeaveBlocking.retLog R11))
        (R11 2).toNat)) := gholds_lookup _ p12.regs rfl
    rw [l, s0Back]
  · intro n lo hi hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    obtain ⟨n1, n2, n8, n10, n12, n13, n14, n15⟩ := hn
    rw [p12.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p11.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      q10.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p9.toEffectPost.gpr_frame (by decide) n lo hi (by simp),
      f8.kept n lo hi (by simp; omega),
      p7.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p6.toEffectPost.gpr_frame (by decide) n lo hi (by simp),
      q5.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p4.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p3.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      q2.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p1.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)]
  · have o8 := f8.output
    unfold Vsa.Machine.output at *
    rw [p12.output, p11.output, q10.output, p9.output, o8, p7.output, p6.output, q5.output, p4.output, p3.output,
      q2.output, p1.output]
  · intro x stack errno
    rw [p12.memory, writeLog_out _ _ _ (retWithin.outL (by omega)), mem11, writeLog_out _ _ _ (within.outL (by omega))]

end OCaml.Vm.Primitives.ConsoleWrite
