import OCaml.Vm.Primitives.Channel.Lseek
import OCaml.Vm.Primitives.Channel.LseekR
import OCaml.Vm.Primitives.Channel.HtifLseek
import OCaml.Vm.Primitives.Console.WriteCall

/-! `lseek(fd, off, whence)` on a descriptor that is open but not a file (the
console streams): newlib's `lseek` tail-jumps to `_lseek_r`, which clears
`errno` and calls htif.c's `_lseek`. That finds the descriptor live and not
a file, sets `reent->_errno = ESPIPE` through `__errno` and returns -1;
`_lseek_r` sees the global `errno` still clear and returns -1. This is the
offset `caml_open_descriptor_in` records for every F1 channel. -/
namespace OCaml.Vm.Primitives.Channel
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable
open ExitPath (LogWithin LogWithin.outLRange)
open FdWrite (errnoGlobal impurePtr)
open ConsoleWrite (fsReady read8_outside)

/-- `fds[fd]`: the 24-byte descriptor entry, whose first word is its kind. -/
def slotAddress (fd : BitVec 64) : BitVec 64 := 2147896728#64 + (fd <<< 1 + fd) <<< 3

/-- A descriptor `_lseek` finds open and not a file: the file system is up,
`fd < 32`, and its kind is neither free (0) nor a file (4). -/
structure SeekFd (fd : BitVec 64) (c : Config) : Prop where
  ready : bytesVal .lw (read8 c.σ.mem fsReady.toNat) ≠ 0#64
  range : fd.toNat < 32
  slotWindow : ReadWindow (slotAddress fd) 4
  live : bytesVal .lw (read8 c.σ.mem (slotAddress fd).toNat) ≠ 0#64
  notFile : bytesVal .lw (read8 c.σ.mem (slotAddress fd).toNat) ≠ 4#64

theorem slotAddress_toNat {fd : BitVec 64} (h : fd.toNat < 32) :
    (slotAddress fd).toNat = 2147896728 + 24 * fd.toNat := by
  unfold slotAddress
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- A signed word load reads the first four bytes. -/
theorem lw_read8 (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    bytesVal .lw (read8 m a) = Functions.sign_extend (m := 64) (bytesT m a 4) := by
  rw [← read4_value]; simp [bytesVal, read8, read4]

theorem guard_bne {a b : BitVec 64} (h : a ≠ b) : guardB .BNE a b = true := by
  simp [guardB, h]

theorem guard_beq_false {a b : BitVec 64} (h : a ≠ b) : guardB .BEQ a b = false := by
  simp [guardB, h]

theorem guard_bltu_false {a b : BitVec 64} (h : b.toNat ≤ a.toNat) : guardB .BLTU a b = false := by
  simp [guardB, Functions.zopz0zI_u, Sail.BitVec.toNatInt]; omega

/-- `_lseek`'s frame: the return-address slot `sp - 8` of its 48-byte frame,
apart from the descriptor entry, the reentrancy pointer and the `errno` word
`rp` it writes. -/
structure HtifSeekInput (ra sp fd off whence rp : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  stack : gpr c 2 = some sp
  fdReg : gpr c 10 = some fd
  offReg : gpr c 11 = some off
  whenceReg : gpr c 12 = some whence
  whenceOk : whence.toNat ≤ 2
  descriptor : SeekFd fd c
  deep : 48 ≤ sp.toNat
  slot : WriteWindow (sp - 48#64 + 40#64) 8
  text : Image.textBase + Image.textSize ≤ sp.toNat - 8 ∨ sp.toNat ≤ Image.textBase
  rodata : Image.rodataBase + Image.rodataSize ≤ sp.toNat - 8 ∨ sp.toNat ≤ Image.rodataBase
  apart : ∀ a ∈ [(slotAddress fd).toNat, impurePtr.toNat], a + 8 ≤ sp.toNat - 8 ∨ sp.toNat ≤ a
  impure : bytesVal .ld (read8 c.σ.mem impurePtr.toNat) = rp
  errnoWindow : WriteWindow rp 4
  errnoText : rp.toNat + 4 ≤ Image.textBase ∨ Image.textBase + Image.textSize ≤ rp.toNat
  errnoRodata : rp.toNat + 4 ≤ Image.rodataBase ∨ Image.rodataBase + Image.rodataSize ≤ rp.toNat
  errnoSlot : rp.toNat + 4 ≤ sp.toNat - 8 ∨ sp.toNat ≤ rp.toNat

/-- `_lseek`'s two stores: the saved return address and `reent->_errno = ESPIPE`. -/
def htifSeekLog (ra sp rp : BitVec 64) : List WEntry :=
  [((sp - 48#64 + 40#64).toNat, 8, ra), (rp.toNat, 4, 29#64)]

/-- Return from `_lseek`: -1, every register but the temporaries kept. -/
structure SeekPost (writes : List Nat) (log : List WEntry) (ra sp : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some ra
  raReg : gpr d 1 = some ra
  stack : gpr d 2 = some sp
  result : gpr d 10 = some (-1#64)
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ writes → gpr d n = gpr c n
  memory : d.σ.mem = writeLog c.σ.mem log
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ
  gprs : GprsKept c d

/-- The registers `_lseek` may change. -/
def htifSeekWrites : List Nat := [1, 2, 6, 10, 13, 14, 15, 16, 17]

theorem htif_lseek {ra sp fd off whence rp c} (h : HtifSeekInput ra sp fd off whence rp c)
    (entry : pcOf c = some 0x80001098#64) :
    ∃ d, Steps c d ∧ SeekPost htifSeekWrites (htifSeekLog ra sp rp) ra sp c d := by
  have D := h.descriptor
  have deep := h.deep
  have slotNat : (sp - 48#64 + 40#64).toNat = sp.toNat - 8 := by
    have := sp.isLt
    rw [BitVec.toNat_add, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    omega
  -- ready: fs_ready is set; save ra
  let R0 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else if n = 10 then fd else
    if n = 11 then off else whence
  have within0 : LogWithin (HtifLseek.readyLog R0 []) (sp.toNat - 8) sp.toNat := by
    intro e he
    simp only [HtifLseek.readyLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he
    simp only [R0, ↓reduceIte, Nat.reduceEqDiff]
    rw [slotNat]; omega
  obtain ⟨d1, run1, p1⟩ := (HtifLseek.ready_fast c R0 h.toLeafInput
    ⟨h.raReg, h.stack, h.fdReg, h.offReg, h.whenceReg, True.intro⟩ h.slot
    ⟨within0.outLRange h.text, within0.outLRange h.rodata⟩
    (guard_bne (by simpa [HtifLseek.ready_loads, fsReady, Layout.sym_fs_ready] using D.ready))).run c ⟨entry, rfl⟩
  have mem1 : d1.σ.mem = writeLog c.σ.mem [((sp - 48#64 + 40#64).toNat, 8, ra)] := p1.memory
  have read1 : ∀ a, (a + 8 ≤ sp.toNat - 8 ∨ sp.toNat ≤ a) → read8 d1.σ.mem a = read8 c.σ.mem a := by
    intro a ha; rw [mem1]; exact read8_outside within0 ha
  have keep1 := fun n lo hi (hn : n ∉ [2, 15]) => p1.toEffectPost.gpr_frame (by decide) n lo hi hn
  -- range: fd < 32
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then (sp - 48#64) else if n = 10 then fd else
    if n = 11 then off else whence
  have regs1 : GHolds d1.σ (HtifLseek.range_input R1) :=
    ⟨gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl,
      gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, True.intro⟩
  have leaf1 : LeafInput ra d1 := ⟨p1.good, p1.image, p1.minstret, regs1.1, h.aligned, p1.tick⟩
  obtain ⟨d2, run2, p2⟩ := (HtifLseek.range_fast d1 R1 leaf1 regs1
    (guard_bltu_false (by simp only [R1, ↓reduceIte, Nat.reduceEqDiff]; have := D.range; simp; omega))).run d1
    ⟨p1.pc, rfl⟩
  -- slot: the descriptor is live
  have regs2 : GHolds d2.σ (HtifLseek.slot_input R1) :=
    ⟨gholds_lookup _ p2.regs rfl, gholds_lookup _ p2.regs rfl, gholds_lookup _ p2.regs rfl,
      gholds_lookup _ p2.regs rfl, gholds_lookup _ p2.regs rfl, True.intro⟩
  have kindSame : read8 d2.σ.mem (slotAddress fd).toNat = read8 c.σ.mem (slotAddress fd).toNat := by
    rw [p2.memory]; exact read1 _ (h.apart _ (by simp))
  obtain ⟨d3, run3, p3⟩ := (HtifLseek.slot_fast d2 R1 ⟨p2.good, p2.image, p2.minstret, regs2.1, h.aligned, p2.tick⟩
    regs2 D.slotWindow
    (guard_beq_false (by
      change bytesVal .lw (read8 d2.σ.mem (slotAddress fd).toNat) ≠ 0#64
      rw [kindSame]; exact D.live))).run d2 ⟨p2.pc, rfl⟩
  let kind : BitVec 64 := bytesVal .lw (read8 c.σ.mem (slotAddress fd).toNat)
  have kind3 : gpr d3 17 = some kind := by
    have l : gpr d3 17 = some (bytesVal .lw (read8 d2.σ.mem (slotAddress fd).toNat)) := gholds_lookup _ p3.regs rfl
    rw [l, kindSame]
  let R3 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then (sp - 48#64) else if n = 10 then fd else
    if n = 11 then off else if n = 12 then whence else kind
  -- whence ≤ 2
  have regs3 : GHolds d3.σ (HtifLseek.whence_input R3) :=
    ⟨gholds_lookup _ p3.regs rfl, gholds_lookup _ p3.regs rfl, gholds_lookup _ p3.regs rfl,
      gholds_lookup _ p3.regs rfl, gholds_lookup _ p3.regs rfl, kind3, True.intro⟩
  obtain ⟨d4, run4, p4⟩ := (HtifLseek.whence_fast d3 R3 ⟨p3.good, p3.image, p3.minstret, regs3.1, h.aligned, p3.tick⟩
    regs3 (guard_bltu_false (by simp only [R3, ↓reduceIte, Nat.reduceEqDiff]; have := h.whenceOk; simp; omega))).run d3
    ⟨p3.pc, rfl⟩
  -- kind: not a file
  have regs4 : GHolds d4.σ (HtifLseek.kind_input R3) :=
    ⟨gholds_lookup _ p4.regs rfl, gholds_lookup _ p4.regs rfl, gholds_lookup _ p4.regs rfl,
      gholds_lookup _ p4.regs rfl, True.intro⟩
  obtain ⟨d5, run5, p5⟩ := (HtifLseek.kind_fast d4 R3 ⟨p4.good, p4.image, p4.minstret, regs4.1, h.aligned, p4.tick⟩
    regs4 (guard_bne D.notFile)).run d4 ⟨p4.pc, rfl⟩
  -- espipe: call __errno
  have regs5 : GHolds d5.σ (HtifLseek.espipe_input R3) :=
    ⟨gholds_lookup _ p5.regs rfl, gholds_lookup _ p5.regs rfl, gholds_lookup _ p5.regs rfl, True.intro⟩
  obtain ⟨d6, run6, p6⟩ := (HtifLseek.espipe_fast d5 R3 ⟨p5.good, p5.image, p5.minstret, regs5.1, h.aligned, p5.tick⟩
    regs5).run d5 ⟨p5.pc, rfl⟩
  have J6 := call_registers_summary HtifLseek.espipe_call_shape HtifLseek.espipe_call_decode d6
    (HtifLseek.espipe_call_pins p6.image) p6.good p6.image p6.tick p6.minstret
    [(2, (sp - 48#64)), (10, fd)] ⟨gholds_lookup _ p6.regs rfl, gholds_lookup _ p6.regs rfl, True.intro⟩
    (by change KeysOK [2, 10]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  obtain ⟨d7, run7, q7⟩ := J6.run d6 ⟨p6.pc, rfl⟩
  let R7 : Nat → BitVec 64 := fun _ => HtifLseek.espipe_call.link
  obtain ⟨d8, run8, p8⟩ := (FdWrite.Errno.leaf_fast d7 R7
    ⟨q7.good, q7.image, q7.minstret, gholds_lookup _ q7.regs rfl, by simp only [R7]; decide, q7.tick⟩
    ⟨gholds_lookup _ q7.regs rfl, True.intro⟩).run d7 ⟨by show pcOf _ = _; rw [q7.pc]; rfl, rfl⟩
  have mem8 : d8.σ.mem = d1.σ.mem := by
    rw [p8.memory, show writeLog d7.σ.mem [] = d7.σ.mem from rfl, q7.memory, p6.memory, p5.memory, p4.memory,
      p3.memory, p2.memory]; rfl
  have rp8 : gpr d8 10 = some rp := by
    have l : gpr d8 10 = some (bytesVal .ld (read8 d7.σ.mem impurePtr.toNat)) := gholds_lookup _ p8.regs rfl
    rw [l, show d7.σ.mem = d1.σ.mem from by rw [q7.memory, p6.memory, p5.memory, p4.memory, p3.memory, p2.memory]; rfl,
      read1 _ (h.apart _ (by simp)), h.impure]
  -- fail: reent->_errno = ESPIPE, -1
  have keep8 := fun n lo hi (hn : n ∉ [1, 10]) =>
    (p8.toEffectPost.gpr_frame (by decide) n lo hi (by simp at hn ⊢; omega)).trans
      (q7.toEffectPost.gpr_frame (by decide) n lo hi (by simp at hn ⊢; omega))
  have sp8 : gpr d8 2 = some (sp - 48#64) := (keep8 2 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p6.regs rfl)
  let R8 : Nat → BitVec 64 := fun n => if n = 1 then HtifLseek.espipe_call.link else if n = 2 then sp - 48#64 else rp
  have failWithin : LogWithin (HtifLseek.failLog R8 []) rp.toNat (rp.toNat + 4) := by
    intro e he
    simp only [HtifLseek.failLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he; simp only [R8, ↓reduceIte, Nat.reduceEqDiff]; omega
  have link8 : gpr d8 1 = some HtifLseek.espipe_call.link := gholds_lookup _ p8.regs rfl
  obtain ⟨d9, run9, p9⟩ := (HtifLseek.fail_fast d8 R8
    ⟨p8.good, p8.image, p8.minstret, link8, by simp only [R8, ↓reduceIte]; decide, p8.tick⟩ ⟨sp8, rp8, True.intro⟩ h.errnoWindow
    ⟨failWithin.outLRange h.errnoText.symm, failWithin.outLRange h.errnoRodata.symm⟩).run d8 ⟨p8.pc, rfl⟩
  have mem9 : d9.σ.mem = writeLog c.σ.mem (htifSeekLog ra sp rp) := by
    rw [p9.memory, mem8, mem1]; rfl
  -- done: restore ra, return
  have raBack : bytesVal .ld (read8 d9.σ.mem (sp - 48#64 + 40#64).toNat) = ra := by
    rw [read8_value, mem9]
    exact Gc.word_writeLog_at _ _ 0 _ _ rfl ⟨by simp only; rw [slotNat]; have := h.errnoSlot; omega, trivial⟩
  have link9 : gpr d9 1 = some HtifLseek.espipe_call.link :=
    (p9.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by simp)).trans link8
  let R9 : Nat → BitVec 64 := fun n => if n = 1 then HtifLseek.espipe_call.link else if n = 2 then sp - 48#64 else -1#64
  obtain ⟨d10, run10, p10⟩ := (HtifLseek.done_fast d9 ra R9
    ⟨p9.good, p9.image, p9.minstret, link9, by simp only [R9, ↓reduceIte]; decide, p9.tick⟩
    ⟨gholds_lookup _ p9.regs rfl, gholds_lookup _ p9.regs rfl, True.intro⟩
    h.slot.read raBack h.aligned).run d9 ⟨p9.pc, rfl⟩
  have keepAll : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ htifSeekWrites → gpr d10 n = gpr c n := by
    intro n lo hi hn
    simp only [htifSeekWrites, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    rw [p10.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p9.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p8.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      q7.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p6.toEffectPost.gpr_frame (by decide) n lo hi (by simp),
      p5.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p4.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p3.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p2.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p1.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)]
  refine ⟨d10, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
    (run9.trans run10)))))))), p10.good, p10.image, p10.minstret, p10.tick, ?_, p10.pc, ?_, ?_, ?_, keepAll,
    by rw [p10.memory]; exact mem9, ?_, ?_⟩
  · exact p10.toEffectPost.htifIdle (p9.toEffectPost.htifIdle (p8.toEffectPost.htifIdle (q7.toEffectPost.htifIdle
      (p6.toEffectPost.htifIdle (p5.toEffectPost.htifIdle (p4.toEffectPost.htifIdle (p3.toEffectPost.htifIdle
        (p2.toEffectPost.htifIdle (p1.toEffectPost.htifIdle h.idle)))))))))
  · have l : gpr d10 1 = some (bytesVal .ld (read8 d9.σ.mem (R9 2 + 40#64).toNat)) := gholds_lookup _ p10.regs rfl
    rw [l]; exact congrArg some raBack
  · have l : gpr d10 2 = some (R9 2 + 48#64) := gholds_lookup _ p10.regs rfl
    rw [l]; simp only [R9, ↓reduceIte, Nat.reduceEqDiff, BitVec.sub_add_cancel]
  · exact gholds_lookup _ p10.regs rfl
  · unfold Vsa.Machine.output
    rw [p10.output, p9.output, p8.output, q7.output, p6.output, p5.output, p4.output, p3.output, p2.output, p1.output]
  · exact (GprsKept.of_pins p1 (by decide) (by decide) (by simp [keysG, HtifLseek.ready_regs])).trans
      ((GprsKept.of_pins p2 (by decide) (by decide) (by simp [keysG, HtifLseek.range_regs])).trans
      ((GprsKept.of_pins p3 (by decide) (by decide) (by simp [keysG, HtifLseek.slot_regs])).trans
      ((GprsKept.of_pins p4 (by decide) (by decide) (by simp [keysG, HtifLseek.whence_regs])).trans
      ((GprsKept.of_pins p5 (by decide) (by decide) (by simp [keysG, HtifLseek.kind_regs])).trans
      ((GprsKept.of_pins p6 (by decide) (by decide) (by simp [keysG, HtifLseek.espipe_regs])).trans
      ((GprsKept.of_pins q7 (by decide) (by decide) (by simp [keysG])).trans
      ((GprsKept.of_pins p8 (by decide) (by decide) (by simp [keysG, FdWrite.Errno.leaf_regs])).trans
      ((GprsKept.of_pins p9 (by decide) (by decide) (by simp [keysG, HtifLseek.fail_regs])).trans
      (GprsKept.of_pins p10 (by decide) (by decide) (by simp [keysG, HtifLseek.done_regs]))))))))))

/-- `lseek`'s native stack: `_lseek_r`'s 16-byte frame and `_lseek`'s saved
return address at `sp - 24`, apart from the globals they read and from the
`errno` word `rp` of the reentrancy structure. -/
structure SeekInput (ra sp s0 fd off whence rp : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  stack : gpr c 2 = some sp
  s0Reg : gpr c 8 = some s0
  fdReg : gpr c 10 = some fd
  offReg : gpr c 11 = some off
  whenceReg : gpr c 12 = some whence
  whenceOk : whence.toNat ≤ 2
  descriptor : SeekFd fd c
  deep : 64 ≤ sp.toNat
  frameLow : WriteWindow (sp - 16#64) 8
  frameHigh : WriteWindow (sp - 16#64 + 8#64) 8
  slot : WriteWindow (sp - 16#64 - 48#64 + 40#64) 8
  text : Image.textBase + Image.textSize ≤ sp.toNat - 24 ∨ sp.toNat ≤ Image.textBase
  rodata : Image.rodataBase + Image.rodataSize ≤ sp.toNat - 24 ∨ sp.toNat ≤ Image.rodataBase
  apart : ∀ a ∈ [fsReady.toNat, impurePtr.toNat, errnoGlobal.toNat, (slotAddress fd).toNat],
    a + 8 ≤ sp.toNat - 24 ∨ sp.toNat ≤ a
  impure : bytesVal .ld (read8 c.σ.mem impurePtr.toNat) = rp
  errnoWindow : WriteWindow rp 4
  errnoText : rp.toNat + 4 ≤ Image.textBase ∨ Image.textBase + Image.textSize ≤ rp.toNat
  errnoRodata : rp.toNat + 4 ≤ Image.rodataBase ∨ Image.rodataBase + Image.rodataSize ≤ rp.toNat
  errnoStack : rp.toNat + 4 ≤ sp.toNat - 24 ∨ sp.toNat ≤ rp.toNat
  errnoApart : rp.toNat + 4 ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 8 ≤ rp.toNat

/-- `lseek`'s stores: `_lseek_r`'s saves and its clearing of `errno`, then `_lseek`'s. -/
def seekLog (ra sp s0 rp : BitVec 64) : List WEntry :=
  [((sp - 16#64).toNat, 8, s0), ((sp - 16#64 + 8#64).toNat, 8, ra), (errnoGlobal.toNat, 4, 0#64)] ++
    htifSeekLog LseekR.pro_call.link (sp - 16#64) rp

/-- The registers `lseek` may change (ra and sp come back restored). -/
def seekWrites : List Nat := [1, 2, 6, 10, 11, 12, 13, 14, 15, 16, 17]

theorem lseek_call {ra sp s0 fd off whence rp c} (h : SeekInput ra sp s0 fd off whence rp c)
    (entry : pcOf c = some 0x80042574#64) :
    ∃ d, Steps c d ∧ SeekPost seekWrites (seekLog ra sp s0 rp) ra sp c d ∧ gpr d 8 = some s0 := by
  have D := h.descriptor
  have deep := h.deep
  have sp16 : (sp - 16#64).toNat = sp.toNat - 16 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := sp.isLt; omega
  have sp8 : (sp - 16#64 + 8#64).toNat = sp.toNat - 8 := by
    rw [BitVec.toNat_add, sp16]; simp only [BitVec.toNat_ofNat]; have := sp.isLt; omega
  have slotTo := slotAddress_toNat D.range
  -- lseek: load the reentrancy pointer, tail-jump to _lseek_r
  let R0 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 10 then fd else if n = 11 then off else whence
  obtain ⟨d1, run1, p1⟩ := (Lseek.tail_fast c R0 h.toLeafInput
    ⟨h.raReg, h.fdReg, h.offReg, h.whenceReg, True.intro⟩).run c ⟨entry, rfl⟩
  have keep1 := fun n lo hi (hn : n ∉ [10, 11, 12, 13, 14]) => p1.toEffectPost.gpr_frame (by decide) n lo hi hn
  have rp1 : gpr d1 10 = some rp := by
    have l : gpr d1 10 = some (bytesVal .ld (read8 c.σ.mem (2147895544#64 : BitVec 64).toNat)) :=
      gholds_lookup _ p1.regs rfl
    rw [l]; exact congrArg some h.impure
  -- _lseek_r: save s0/ra, clear errno, call _lseek(fd, off, whence)
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else if n = 8 then s0 else
    if n = 10 then rp else if n = 11 then fd else if n = 12 then off else whence
  have outside1 : ImageOutside (LseekR.proLog R1 []) := by
    constructor <;> simp only [OutLRange, LseekR.proLog, R1, ↓reduceIte, Nat.reduceEqDiff, sp16, sp8] <;>
      refine ⟨?_, ?_, ?_, trivial⟩ <;> first | decide | (have := h.text; have := h.rodata; omega)
  obtain ⟨d2, run2, p2⟩ := (LseekR.pro_fast d1 R1
    ⟨p1.good, p1.image, p1.minstret, gholds_lookup _ p1.regs rfl, h.aligned, p1.tick⟩
    ⟨gholds_lookup _ p1.regs rfl, (keep1 2 (by decide) (by decide) (by simp)).trans h.stack,
      (keep1 8 (by decide) (by decide) (by simp)).trans h.s0Reg, rp1, gholds_lookup _ p1.regs rfl,
      gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, True.intro⟩
    h.frameLow h.frameHigh outside1).run d1 ⟨p1.pc, rfl⟩
  have J2 := call_registers_summary LseekR.pro_call_shape LseekR.pro_call_decode d2
    (LseekR.pro_call_pins p2.image) p2.good p2.image p2.tick p2.minstret
    [(2, sp - 16#64), (8, rp), (10, fd), (11, off), (12, whence)]
    ⟨gholds_lookup _ p2.regs rfl, gholds_lookup _ p2.regs rfl, gholds_lookup _ p2.regs rfl,
      gholds_lookup _ p2.regs rfl, gholds_lookup _ p2.regs rfl, True.intro⟩
    (by change KeysOK [2, 8, 10, 11, 12]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  obtain ⟨d3, run3, q3⟩ := J2.run d2 ⟨p2.pc, rfl⟩
  let pro : List WEntry := [((sp - 16#64).toNat, 8, s0), ((sp - 16#64 + 8#64).toNat, 8, ra), (errnoGlobal.toNat, 4, 0#64)]
  have mem3 : d3.σ.mem = writeLog c.σ.mem pro := by rw [q3.memory, p2.memory, p1.memory]; rfl
  have read3 : ∀ a, (a + 8 ≤ sp.toNat - 16 ∨ sp.toNat ≤ a) → (a + 8 ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ a) →
      read8 d3.σ.mem a = read8 c.σ.mem a := by
    intro a s e
    rw [mem3]
    simp only [read8]
    have out : ∀ k, k < 8 → OutL pro (a + k) := by
      intro k hk
      simp only [OutL, pro, sp16, sp8]
      exact ⟨by omega, by omega, by omega, trivial⟩
    rw [writeLog_out _ _ _ (by simpa using out 0 (by decide)), writeLog_out _ _ _ (out 1 (by decide)),
      writeLog_out _ _ _ (out 2 (by decide)), writeLog_out _ _ _ (out 3 (by decide)),
      writeLog_out _ _ _ (out 4 (by decide)), writeLog_out _ _ _ (out 5 (by decide)),
      writeLog_out _ _ _ (out 6 (by decide)), writeLog_out _ _ _ (out 7 (by decide))]
  have errnoNat : errnoGlobal.toNat = 2147896648 := rfl
  have readyNat : fsReady.toNat = 2147895576 := rfl
  have impureNat : impurePtr.toNat = 2147895544 := rfl
  have aReady := h.apart fsReady.toNat (by simp)
  have aImpure := h.apart impurePtr.toNat (by simp)
  have aSlot := h.apart (slotAddress fd).toNat (by simp)
  have kindSame := read3 (slotAddress fd).toNat (by omega) (by rw [slotTo, errnoNat]; omega)
  have input3 : HtifSeekInput LseekR.pro_call.link (sp - 16#64) fd off whence rp d3 :=
    { good := q3.good, image := q3.image, minstret := q3.minstret, raReg := gholds_lookup _ q3.regs rfl,
      aligned := by decide, tick := q3.tick
      idle := q3.toEffectPost.htifIdle (p2.toEffectPost.htifIdle (p1.toEffectPost.htifIdle h.idle))
      stack := gholds_lookup _ q3.regs rfl, fdReg := gholds_lookup _ q3.regs rfl
      offReg := gholds_lookup _ q3.regs rfl, whenceReg := gholds_lookup _ q3.regs rfl
      whenceOk := h.whenceOk
      descriptor := ⟨by rw [read3 _ (by rw [readyNat] at aReady ⊢; omega) (by rw [readyNat, errnoNat]; omega)]; exact D.ready,
        D.range, D.slotWindow, by rw [kindSame]; exact D.live, by rw [kindSame]; exact D.notFile⟩
      deep := by rw [sp16]; omega
      slot := h.slot
      text := by rw [sp16]; have := h.text; omega
      rodata := by rw [sp16]; have := h.rodata; omega
      apart := by
        intro a ha
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
        rw [sp16]
        rcases ha with rfl | rfl <;> omega
      impure := by
        rw [read3 _ (by omega) (by rw [impureNat, errnoNat]; omega)]; exact h.impure
      errnoWindow := h.errnoWindow, errnoText := h.errnoText, errnoRodata := h.errnoRodata
      errnoSlot := by rw [sp16]; have := h.errnoStack; omega }
  obtain ⟨d4, run4, P4⟩ := htif_lseek input3 (by rw [q3.pc]; rfl)
  have mem4 : d4.σ.mem = writeLog c.σ.mem (seekLog ra sp s0 rp) := by
    rw [P4.memory, mem3, seekLog, writeLog_append]
  have slotNat : (sp - 16#64 - 48#64 + 40#64).toNat = sp.toNat - 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub, sp16]; simp only [BitVec.toNat_ofNat]; have := sp.isLt; omega
  have aErrno := h.apart errnoGlobal.toNat (by simp)
  -- _lseek_r: -1, and the global errno is still clear
  let R4 : Nat → BitVec 64 := fun n => if n = 1 then LseekR.pro_call.link else if n = 2 then sp - 16#64 else
    if n = 8 then rp else -1#64
  have rp4 : gpr d4 8 = some rp :=
    (P4.kept 8 (by decide) (by decide) (by decide)).trans (gholds_lookup _ q3.regs rfl)
  obtain ⟨d5, run5, p5⟩ := (LseekR.check_fast d4 R4
    ⟨P4.good, P4.image, P4.minstret, P4.raReg, by simp only [R4, ↓reduceIte]; decide, P4.tick⟩ ⟨P4.raReg, P4.stack, rp4, P4.result, True.intro⟩
    (by simp only [R4, ↓reduceIte, Nat.reduceEqDiff]; decide)).run d4 ⟨P4.pc, rfl⟩
  have keep5 := fun n lo hi (hn : n ∉ [15]) => p5.toEffectPost.gpr_frame (by decide) n lo hi hn
  have errnoZero : bytesVal .lw (read8 d5.σ.mem (2147896648#64 : BitVec 64).toNat) = 0#64 := by
    rw [p5.memory, show writeLog d4.σ.mem [] = d4.σ.mem from rfl, mem4, lw_read8, seekLog, writeLog_append,
      bytesT_writeLog_out _ (by
        simp only [OutLRange, htifSeekLog, slotNat]
        have e : (2147896648#64 : BitVec 64).toNat = 2147896648 := rfl
        rw [e]; rw [errnoNat] at aErrno
        exact ⟨by omega, by have := h.errnoApart; rw [errnoNat] at this; omega, trivial⟩),
      show ([((sp - 16#64).toNat, 8, s0), ((sp - 16#64 + 8#64).toNat, 8, ra), (errnoGlobal.toNat, 4, 0#64)] : List WEntry) =
        [((sp - 16#64).toNat, 8, s0), ((sp - 16#64 + 8#64).toNat, 8, ra)] ++ [(errnoGlobal.toNat, 4, 0#64)] from rfl,
      writeLog_append, show (2147896648#64 : BitVec 64).toNat = errnoGlobal.toNat from rfl, word32_writeLog]
    decide
  obtain ⟨d6, run6, p6⟩ := (LseekR.errno_fast d5 R4
    ⟨p5.good, p5.image, p5.minstret, (keep5 1 (by decide) (by decide) (by simp)).trans P4.raReg, by simp only [R4, ↓reduceIte]; decide, p5.tick⟩
    ⟨(keep5 1 (by decide) (by decide) (by simp)).trans P4.raReg, (keep5 2 (by decide) (by decide) (by simp)).trans P4.stack,
      (keep5 8 (by decide) (by decide) (by simp)).trans rp4, (keep5 10 (by decide) (by decide) (by simp)).trans P4.result,
      True.intro⟩
    (by rw [show (LseekR.errno_loads d5.σ.mem R4).getD 0 [] = read8 d5.σ.mem (2147896648#64 : BitVec 64).toNat from rfl,
      errnoZero]; decide)).run d5 ⟨p5.pc, rfl⟩
  have keep6 := fun n lo hi (hn : n ∉ [15]) =>
    (p6.toEffectPost.gpr_frame (by decide) n lo hi hn).trans (keep5 n lo hi hn)
  have mem6 : d6.σ.mem = writeLog c.σ.mem (seekLog ra sp s0 rp) := by
    rw [p6.memory, show writeLog d5.σ.mem [] = d5.σ.mem from rfl, p5.memory]; exact mem4
  -- restore s0 and ra, return -1
  have rest : OutLRange (htifSeekLog LseekR.pro_call.link (sp - 16#64) rp) (sp.toNat - 16) 16 := by
    simp only [OutLRange, htifSeekLog, slotNat]
    exact ⟨by omega, by have := h.errnoStack; omega, trivial⟩
  have raBack : bytesVal .ld (read8 d6.σ.mem (sp - 16#64 + 8#64).toNat) = ra := by
    rw [read8_value, mem6]
    exact Gc.word_writeLog_at _ _ 1 _ _ rfl (by
      simp only [seekLog, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
      simp only [OutLRange, htifSeekLog, slotNat, sp8] at rest ⊢
      exact ⟨by rw [errnoNat] at aErrno ⊢; omega, by omega, by omega, trivial⟩)
  have s0Back : bytesVal .ld (read8 d6.σ.mem (sp - 16#64).toNat) = s0 := by
    rw [read8_value, mem6]
    exact Gc.word_writeLog_at _ _ 0 _ _ rfl (by
      simp only [seekLog, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
      simp only [OutLRange, htifSeekLog, slotNat, sp8, sp16] at rest ⊢
      exact ⟨by omega, by rw [errnoNat] at aErrno ⊢; omega, by omega, by omega, trivial⟩)
  let R6 : Nat → BitVec 64 := fun n => if n = 1 then LseekR.pro_call.link else if n = 2 then sp - 16#64 else -1#64
  have link6 : gpr d6 1 = some LseekR.pro_call.link := (keep6 1 (by decide) (by decide) (by simp)).trans P4.raReg
  obtain ⟨d7, run7, p7⟩ := (LseekR.done_fast d6 ra R6
    ⟨p6.good, p6.image, p6.minstret, link6, by simp only [R6, ↓reduceIte]; decide, p6.tick⟩
    ⟨(keep6 2 (by decide) (by decide) (by simp)).trans P4.stack, (keep6 10 (by decide) (by decide) (by simp)).trans P4.result,
      True.intro⟩ h.frameHigh.read h.frameLow.read raBack h.aligned).run d6 ⟨p6.pc, rfl⟩
  have s07 : gpr d7 8 = some s0 := by
    have l : gpr d7 8 = some (bytesVal .ld (read8 d6.σ.mem (R6 2).toNat)) := gholds_lookup _ p7.regs rfl
    rw [l]; exact congrArg some s0Back
  refine ⟨d7, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))),
    ⟨p7.good, p7.image, p7.minstret, p7.tick, ?_, p7.pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, s07⟩
  · exact p7.toEffectPost.htifIdle (p6.toEffectPost.htifIdle (p5.toEffectPost.htifIdle P4.idle))
  · have l : gpr d7 1 = some (bytesVal .ld (read8 d6.σ.mem (R6 2 + 8#64).toNat)) := gholds_lookup _ p7.regs rfl
    rw [l]; exact congrArg some raBack
  · have l : gpr d7 2 = some (R6 2 + 16#64) := gholds_lookup _ p7.regs rfl
    rw [l]; simp only [R6, ↓reduceIte, Nat.reduceEqDiff, BitVec.sub_add_cancel]
  · exact gholds_lookup _ p7.regs rfl
  · intro n lo hi hn
    by_cases n8 : n = 8
    · subst n8; rw [s07, h.s0Reg]
    simp only [seekWrites, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    rw [p7.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega), keep6 n lo hi (by simp; omega),
      P4.kept n lo hi (by simp [htifSeekWrites]; omega), q3.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p2.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega), keep1 n lo hi (by simp; omega)]
  · rw [p7.memory]; exact mem6
  · rw [show Vsa.Machine.output d7.σ = Vsa.Machine.output d4.σ by unfold Vsa.Machine.output; rw [p7.output, p6.output, p5.output],
      P4.output]
    unfold Vsa.Machine.output; rw [q3.output, p2.output, p1.output]
  · exact (GprsKept.of_pins p1 (by decide) (by decide) (by simp [keysG, Lseek.tail_regs])).trans
      ((GprsKept.of_pins p2 (by decide) (by decide) (by simp [keysG, LseekR.pro_regs])).trans
      ((GprsKept.of_pins q3 (by decide) (by decide) (by simp [keysG])).trans (P4.gprs.trans
      ((GprsKept.of_pins p5 (by decide) (by decide) (by simp [keysG, LseekR.check_regs])).trans
      ((GprsKept.of_pins p6 (by decide) (by decide) (by simp [keysG, LseekR.errno_regs])).trans
      (GprsKept.of_pins p7 (by decide) (by decide) (by simp [keysG, LseekR.done_regs])))))))

end OCaml.Vm.Primitives.Channel
