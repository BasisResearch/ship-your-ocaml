import OCaml.Vm.Primitives.Console.Blocking
import OCaml.Vm.Primitives.Console.WriteCall

/-! `caml_write_fd(fd, flags, buf, n)` on a console descriptor: save the
callee-saved registers, enter the blocking section, `write` the buffer, leave
the blocking section, find no error and return `n`. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable
open ExitPath (LogWithin LogWithin.outL LogWithin.outLRange)
open FdWrite (errnoGlobal impurePtr enterHook leaveHook pendingSignals)

/-- `(int) n` is `n` for a length below 2^31. -/
theorem int32_small (n : Nat) (h : n < 2 ^ 31) :
    BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 n) 31 0) = BitVec.ofNat 64 n := by
  have e : Sail.BitVec.extractLsb (BitVec.ofNat 64 n) 31 0 = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.extractLsb]
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  have m : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  simp [m]; omega

/-- The native stack of `caml_write_fd`: its 80-byte frame at `sp - 80`, and
below it `write`'s frames (`WriteCallLayout`), all within `[sp - 192, sp)`;
the runtime globals, the descriptor table, the buffer and the reentrancy
structure's `errno` word `rp` lie outside it. -/
structure WriteFdLayout (sp fd buf rp : BitVec 64) (len : Nat) : Prop where
  call : WriteCallLayout (sp - 80#64) fd buf len
  slots : ∀ k ∈ [8, 16, 24, 32, 40, 48, 56, 64, 72], WriteWindow (sp - 80#64 + BitVec.ofNat 64 k) 8
  floor : 0x80000000 + 192 ≤ sp.toNat
  top : sp.toNat ≤ 0x100000000
  text : Image.textBase + Image.textSize ≤ sp.toNat - 192 ∨ sp.toNat ≤ Image.textBase
  rodata : Image.rodataBase + Image.rodataSize ≤ sp.toNat - 192 ∨ sp.toNat ≤ Image.rodataBase
  ready : fsReady.toNat + 8 ≤ sp.toNat - 192 ∨ sp.toNat ≤ fsReady.toNat
  kind : (kindAddress fd).toNat + 8 ≤ sp.toNat - 192 ∨ sp.toNat ≤ (kindAddress fd).toNat
  buffer : buf.toNat + len ≤ sp.toNat - 192 ∨ sp.toNat ≤ buf.toNat
  errno : errnoGlobal.toNat + 4 ≤ sp.toNat - 192 ∨ sp.toNat ≤ errnoGlobal.toNat
  globals : ∀ a ∈ [enterHook.toNat, leaveHook.toNat, impurePtr.toNat, rp.toNat], a + 8 ≤ sp.toNat - 192 ∨ sp.toNat ≤ a
  pending : pendingSignals.toNat + 256 ≤ sp.toNat - 192 ∨ sp.toNat ≤ pendingSignals.toNat
  errnoWindow : WriteWindow rp 4
  errnoText : rp.toNat + 4 ≤ Image.textBase ∨ Image.textBase + Image.textSize ≤ rp.toNat
  errnoRodata : rp.toNat + 4 ≤ Image.rodataBase ∨ Image.rodataBase + Image.rodataSize ≤ rp.toNat
  errnoApart : rp.toNat + 8 ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ rp.toNat

structure WriteFdInput (ra sp fd buf rp : BitVec 64) (bs : List UInt8) (c : Config) : Prop
    extends LeafInput ra c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23], (gprGet c.σ n).isSome
  stack : gpr c 2 = some sp
  fdReg : gpr c 10 = some fd
  bufReg : gpr c 12 = some buf
  lenReg : gpr c 13 = some (BitVec.ofNat 64 bs.length)
  short : bs.length < 2 ^ 31
  layout : WriteFdLayout sp fd buf rp bs.length
  descriptor : ConsoleFd fd c
  ram : 0x80000000 ≤ buf.toNat ∧ buf.toNat + bs.length ≤ 0x100000000 ∧
    (buf.toNat + bs.length ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 8 ≤ buf.toNat)
  bytes : ∀ i x, bs[i]? = some x → (c.σ.mem[(buf + BitVec.ofNat 64 i).toNat]?).getD 0 = BitVec.ofNat 8 x.toNat
  enterHookWord : bytesVal .ld (read8 c.σ.mem enterHook.toNat) = 0x8000d2a4#64
  leaveHookWord : bytesVal .ld (read8 c.σ.mem leaveHook.toNat) = 0x8000d2a8#64
  impure : bytesVal .ld (read8 c.σ.mem impurePtr.toNat) = rp
  clear : NoPendingSignals c.σ.mem

/-- Return from `caml_write_fd`: `n`, the bytes on the console, the
callee-saved registers restored; only the native stack below `sp`, `errno`
and the reentrancy `errno` word were written. -/
structure WriteFdPost (ra sp rp : BitVec 64) (bs : List UInt8) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some ra
  raReg : gpr d 1 = some ra
  result : gpr d 10 = some (BitVec.ofNat 64 bs.length)
  stack : gpr d 2 = some sp
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23], gpr d n = gpr c n
  rest : ∀ n ∈ [24, 25, 26, 27], gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ ++ bytesToString bs
  frame : ∀ x, (x < sp.toNat - 192 ∨ sp.toNat ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
    (x < rp.toNat ∨ rp.toNat + 4 ≤ x) → (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0

theorem write_fd {ra sp fd buf rp bs c} (h : WriteFdInput ra sp fd buf rp bs c)
    (entry : pcOf c = some 0x80025274#64) :
    ∃ d, Steps c d ∧ WriteFdPost ra sp rp bs c d := by
  have L := h.layout
  have present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23], gpr c n = some ((gpr c n).getD 0) := by
    intro n hn
    have := h.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  let len : BitVec 64 := BitVec.ofNat 64 bs.length
  have floor := L.floor
  have off : ∀ k, k ≤ 80 → (sp - 80#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 80 + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  have sp80 : (sp - 80#64).toNat = sp.toNat - 80 := by
    rw [BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  -- prologue: save ra, s0–s7 and set up the retry constants
  let R0 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else if n = 10 then fd else
    if n = 12 then buf else if n = 13 then len else (gpr c n).getD 0
  have within : LogWithin (FdWrite.WriteFd.proLog R0) (sp.toNat - 80) sp.toNat := by
    intro e he
    simp only [FdWrite.WriteFd.proLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; rw [off _ (by decide)]; omega)
  obtain ⟨d1, run1, p1⟩ := (FdWrite.WriteFd.pro_fast c R0 h.toLeafInput
    ⟨h.raReg, h.stack, present 8 (by simp), present 9 (by simp), h.fdReg, h.bufReg, h.lenReg,
      present 18 (by simp), present 19 (by simp), present 20 (by simp), present 21 (by simp),
      present 22 (by simp), present 23 (by simp), True.intro⟩
    L.slots ⟨within.outLRange (by have := L.text; omega), within.outLRange (by have := L.rodata; omega)⟩).run
    c ⟨entry, rfl⟩
  have mem1 : d1.σ.mem = writeLog c.σ.mem (FdWrite.WriteFd.proLog R0) := p1.memory
  have read1 : ∀ a, (a + 8 ≤ sp.toNat - 80 ∨ sp.toNat ≤ a) → read8 d1.σ.mem a = read8 c.σ.mem a := by
    intro a ha; rw [mem1]; exact read8_outside within ha
  -- enter the blocking section
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 9 then len else if n = 10 then fd else
    if n = 22 then fd else buf
  obtain ⟨d2, run2, p2⟩ := (FdWrite.WriteFd.enter_fast d1 R1
    ⟨p1.good, p1.image, p1.minstret, gholds_lookup _ p1.regs rfl, h.aligned, p1.tick⟩
    ⟨gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl,
      gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, True.intro⟩).run d1 ⟨p1.pc, rfl⟩
  have J2 := call_registers_summary FdWrite.WriteFd.enter_call_shape FdWrite.WriteFd.enter_call_decode d2
    (FdWrite.WriteFd.enter_call_pins p2.image) p2.good p2.image p2.tick p2.minstret
    [(10, fd)] ⟨gholds_lookup _ p2.regs rfl, True.intro⟩
    (by change KeysOK [10]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  obtain ⟨d3, run3, q3⟩ := J2.run d2 ⟨p2.pc, rfl⟩
  have idle3 := q3.toEffectPost.htifIdle (p2.toEffectPost.htifIdle (p1.toEffectPost.htifIdle h.idle))
  obtain ⟨d4, run4, e4⟩ := enter_blocking (ra := FdWrite.WriteFd.enter_call.link)
    ⟨q3.good, q3.image, q3.minstret, gholds_lookup _ q3.regs rfl, by decide, q3.tick⟩ idle3
    ⟨fd, gholds_lookup _ q3.regs rfl⟩
    (by rw [q3.memory, p2.memory, show writeLog d1.σ.mem [] = d1.σ.mem from rfl,
          read1 _ (by have := L.globals enterHook.toNat (by simp); omega)]; exact h.enterHookWord)
    (by rw [q3.pc]; rfl)
  -- keep: d4 against d1, outside a0, ra and a5
  have k4 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 15] → gpr d4 n = gpr d1 n := fun n lo hi hn => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    rw [e4.kept n lo hi (by simp; omega), q3.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p2.toEffectPost.gpr_frame (by decide) n lo hi (by simp)]
  have link4 : gpr d4 1 = some FdWrite.WriteFd.enter_call.link :=
    (e4.kept 1 (by decide) (by decide) (by simp)).trans (gholds_lookup _ q3.regs rfl)
  -- write(fd, buf, n)
  let R4 : Nat → BitVec 64 := fun n => if n = 1 then FdWrite.WriteFd.enter_call.link else R1 n
  obtain ⟨d5, run5, p5⟩ := (FdWrite.WriteFd.call_fast d4 R4
    ⟨e4.good, e4.image, e4.minstret, link4, by simp only [R4, ↓reduceIte]; decide, e4.tick⟩
    ⟨link4, (k4 9 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl),
      (k4 10 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl),
      (k4 22 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl),
      (k4 23 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl), True.intro⟩).run d4 ⟨e4.pc, rfl⟩
  have J5 := call_registers_summary FdWrite.WriteFd.call_call_shape FdWrite.WriteFd.call_call_decode d5
    (FdWrite.WriteFd.call_call_pins p5.image) p5.good p5.image p5.tick p5.minstret
    [(10, fd), (11, buf), (12, len)]
    ⟨gholds_lookup _ p5.regs rfl, gholds_lookup _ p5.regs rfl, gholds_lookup _ p5.regs rfl, True.intro⟩
    (by change KeysOK [10, 11, 12]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  obtain ⟨d6, run6, q6⟩ := J5.run d5 ⟨p5.pc, rfl⟩
  have k6 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 10, 11, 12, 15] → gpr d6 n = gpr d1 n := fun n lo hi hn => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    rw [q6.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p5.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega), k4 n lo hi (by simp; omega)]
  have mem6 : d6.σ.mem = writeLog c.σ.mem (FdWrite.WriteFd.proLog R0) := by
    rw [q6.memory, p5.memory, show writeLog d4.σ.mem [] = d4.σ.mem from rfl, e4.memory, q3.memory, p2.memory,
      show writeLog d1.σ.mem [] = d1.σ.mem from rfl, mem1]
  have read6 : ∀ a, (a + 8 ≤ sp.toNat - 80 ∨ sp.toNat ≤ a) → read8 d6.σ.mem a = read8 c.σ.mem a := by
    intro a ha; rw [mem6]; exact read8_outside within ha
  have idle6 := q6.toEffectPost.htifIdle (p5.toEffectPost.htifIdle e4.idle)
  have D := h.descriptor
  have kind6 := read6 (kindAddress fd).toNat (by have := L.kind; omega)
  have input : WriteCallInput FdWrite.WriteFd.call_call.link (sp - 80#64) fd buf bs d6 :=
    { good := q6.good, image := q6.image, minstret := q6.minstret, raReg := gholds_lookup _ q6.regs rfl,
      aligned := by decide, tick := q6.tick, idle := idle6
      saved := by
        intro n hn
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
        rcases hn with rfl | rfl | rfl
        · change (gpr d6 8).isSome; have l : gpr d1 8 = some (R0 8) := gholds_lookup _ p1.regs rfl
          rw [k6 8 (by decide) (by decide) (by simp), l]; rfl
        · change (gpr d6 9).isSome; have l : gpr d1 9 = some (len) := gholds_lookup _ p1.regs rfl
          rw [k6 9 (by decide) (by decide) (by simp), l]; rfl
        · change (gpr d6 18).isSome; have l : gpr d1 18 = some (11#64) := gholds_lookup _ p1.regs rfl
          rw [k6 18 (by decide) (by decide) (by simp), l]; rfl
      stack := (k6 2 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl)
      fdReg := gholds_lookup _ q6.regs rfl
      bufReg := gholds_lookup _ q6.regs rfl
      lenReg := gholds_lookup _ q6.regs rfl
      layout := L.call
      descriptor := ⟨by rw [read6 _ (by have := L.ready; omega)]; exact D.ready, D.range, D.kindWindow,
        by rw [kind6]; exact D.console, by rw [kind6]; exact D.notFile⟩
      ram := h.ram
      bytes := by
        intro i x hx
        have hi := (List.getElem?_eq_some_iff.mp hx).1
        have addr := cursor_toNat h.ram.2.1 (Nat.le_of_lt hi)
        rw [mem6, writeLog_out _ _ _ (within.outL (by rw [addr]; have := L.buffer; omega))]
        exact h.bytes i x hx }
  obtain ⟨d7, run7, p7⟩ := write_call input (by rw [q6.pc]; rfl)
  have errnoSp := L.errno
  have frame7 : ∀ x, (x < sp.toNat - 192 ∨ sp.toNat - 80 ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
      (d7.σ.mem[x]?).getD 0 = ((writeLog c.σ.mem (FdWrite.WriteFd.proLog R0))[x]?).getD 0 := by
    intro x hx e
    rw [p7.frame x (by rw [sp80]; omega) e, mem6]
  -- leave: s0 := (int) n, then leave the blocking section
  let R7 : Nat → BitVec 64 := fun n => if n = 1 then FdWrite.WriteFd.call_call.link else len
  obtain ⟨d8, run8, p8⟩ := (FdWrite.WriteFd.leave_fast d7 R7
    ⟨p7.good, p7.image, p7.minstret, p7.raReg, by simp only [R7, ↓reduceIte]; decide, p7.tick⟩
    ⟨p7.raReg, p7.result, True.intro⟩).run d7 ⟨p7.pc, rfl⟩
  have s08 : gpr d8 8 = some len := by
    have l : gpr d8 8 = some (BitVec.signExtend 64 (Sail.BitVec.extractLsb (R7 10) 31 0)) := gholds_lookup _ p8.regs rfl
    rw [l]; exact congrArg some (int32_small _ h.short)
  have J8 := call_registers_summary FdWrite.WriteFd.leave_call_shape FdWrite.WriteFd.leave_call_decode d8
    (FdWrite.WriteFd.leave_call_pins p8.image) p8.good p8.image p8.tick p8.minstret
    [(2, sp - 80#64), (8, len), (10, len)]
    ⟨(p8.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by simp)).trans p7.stack, s08,
      gholds_lookup _ p8.regs rfl, True.intro⟩
    (by change KeysOK [2, 8, 10]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  obtain ⟨d9, run9, q9⟩ := J8.run d8 ⟨p8.pc, rfl⟩
  have mem9 : d9.σ.mem = d7.σ.mem := by rw [q9.memory, p8.memory]; rfl
  have read9 : ∀ a, (a + 8 ≤ sp.toNat - 192 ∨ sp.toNat ≤ a) → (a + 8 ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ a) →
      read8 d9.σ.mem a = read8 c.σ.mem a := by
    intro a s e
    rw [mem9, ← read8_outside (m := c.σ.mem) within (by omega)]
    simp only [read8]
    rw [frame7 a (by omega) (by omega), frame7 (a + 1) (by omega) (by omega), frame7 (a + 2) (by omega) (by omega),
      frame7 (a + 3) (by omega) (by omega), frame7 (a + 4) (by omega) (by omega), frame7 (a + 5) (by omega) (by omega),
      frame7 (a + 6) (by omega) (by omega), frame7 (a + 7) (by omega) (by omega)]
  have g := L.globals
  have gRp := g rp.toNat (by simp)
  have leave : LeaveInput FdWrite.WriteFd.leave_call.link (sp - 80#64) len rp
      (bytesVal .lw (read8 d9.σ.mem rp.toNat)) d9 :=
    { good := q9.good, image := q9.image, minstret := q9.minstret, raReg := gholds_lookup _ q9.regs rfl,
      aligned := by decide, tick := q9.tick
      idle := q9.toEffectPost.htifIdle (p8.toEffectPost.htifIdle p7.idle)
      stack := gholds_lookup _ q9.regs rfl
      s0Reg := gholds_lookup _ q9.regs rfl
      a0 := ⟨len, gholds_lookup _ q9.regs rfl⟩
      frameLow := L.call.frameLow, frameHigh := L.call.frameHigh, text := L.call.text, rodata := L.call.rodata
      hook := by
        rw [read9 _ (by have := g leaveHook.toNat (by simp); omega) (Or.inl (by decide))]; exact h.leaveHookWord
      impure := by
        rw [read9 _ (by have := g impurePtr.toNat (by simp); omega) (Or.inl (by decide))]; exact h.impure
      errnoWrite := L.errnoWindow
      errnoValue := rfl
      errnoText := L.errnoText
      errnoRodata := L.errnoRodata
      apart := by
        intro a ha
        rw [sp80]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · have := g leaveHook.toNat (by simp); omega
        · have := g impurePtr.toNat (by simp); omega
        · omega
      errnoFrame := by rw [sp80]; omega
      pending := by
        rw [sp80]; have hp := L.pending; generalize pendingSignals.toNat = P at hp ⊢; omega
      clear := by
        intro i hi
        have pe : errnoGlobal.toNat + 4 ≤ pendingSignals.toNat := by decide
        rw [read9 _ (by rw [slot_toNat i hi]; have := L.pending; omega) (by rw [slot_toNat i hi]; omega)]
        exact h.clear i hi }
  obtain ⟨d10, run10, l10⟩ := leave_blocking leave (by rw [q9.pc]; rfl)
  -- no error: s0 ≠ -1
  let R10 : Nat → BitVec 64 := fun n => if n = 1 then FdWrite.WriteFd.leave_call.link else if n = 8 then len else
    if n = 10 then rp else 18446744073709551615#64
  have s3 : gpr d10 19 = some 18446744073709551615#64 := by
    have l : gpr d1 19 = some 18446744073709551615#64 := gholds_lookup _ p1.regs rfl
    rw [l10.kept 19 (by decide) (by decide) (by simp), q9.toEffectPost.gpr_frame (by decide) 19 (by decide) (by decide) (by simp),
      p8.toEffectPost.gpr_frame (by decide) 19 (by decide) (by decide) (by simp), p7.rest 19 (by simp),
      k6 19 (by decide) (by decide) (by simp), l]
  obtain ⟨d11, run11, p11⟩ := (FdWrite.WriteFd.check_fast d10 R10
    ⟨l10.good, l10.image, l10.minstret, l10.raReg, by simp only [R10, ↓reduceIte]; decide, l10.tick⟩
    ⟨l10.raReg, l10.s0Reg, l10.result, s3, True.intro⟩
    (by
      simp only [R10, ↓reduceIte, Nat.reduceEqDiff]
      intro eq
      have := congrArg BitVec.toNat eq
      have hs := h.short
      simp only [len, BitVec.toNat_ofNat] at this
      omega)).run d10 ⟨l10.pc, rfl⟩
  -- epilogue: reload the saves from the prologue frame
  have frame11 : ∀ x, (x < sp.toNat - 192 ∨ sp.toNat - 80 ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
      (x < rp.toNat ∨ rp.toNat + 4 ≤ x) →
      (d11.σ.mem[x]?).getD 0 = ((writeLog c.σ.mem (FdWrite.WriteFd.proLog R0))[x]?).getD 0 := by
    intro x s e r
    rw [p11.memory, show writeLog d10.σ.mem [] = d10.σ.mem from rfl, l10.frame x (by rw [sp80]; omega) r, mem9]
    exact frame7 x s e
  have read11 : ∀ a, sp.toNat - 80 ≤ a → a + 8 ≤ sp.toNat →
      read8 d11.σ.mem a = read8 (writeLog c.σ.mem (FdWrite.WriteFd.proLog R0)) a := by
    intro a lo hi
    simp only [read8]
    rw [frame11 a (by omega) (by omega) (by omega), frame11 (a + 1) (by omega) (by omega) (by omega),
      frame11 (a + 2) (by omega) (by omega) (by omega), frame11 (a + 3) (by omega) (by omega) (by omega),
      frame11 (a + 4) (by omega) (by omega) (by omega), frame11 (a + 5) (by omega) (by omega) (by omega),
      frame11 (a + 6) (by omega) (by omega) (by omega), frame11 (a + 7) (by omega) (by omega) (by omega)]
  have back := fun (i k : Nat) (hk : k ≤ 72) (v : BitVec 64)
      (sel : (FdWrite.WriteFd.proLog R0)[i]? = some ((sp - 80#64 + BitVec.ofNat 64 k).toNat, 8, v))
      (after : OutLRange ((FdWrite.WriteFd.proLog R0).drop (i + 1)) (sp - 80#64 + BitVec.ofNat 64 k).toNat 8) =>
    (show bytesVal .ld (read8 d11.σ.mem (sp - 80#64 + BitVec.ofNat 64 k).toNat) = v by
      rw [read11 _ (by rw [off k (by omega)]; omega) (by rw [off k (by omega)]; omega), read8_value]
      exact Gc.word_writeLog_at _ _ i _ _ sel after)
  have apart := fun (j k : Nat) (hj : j ≤ 72) (hk : k ≤ 72) (ne : j + 8 ≤ k ∨ k + 8 ≤ j) =>
    (show (sp - 80#64 + BitVec.ofNat 64 j).toNat + 8 ≤ (sp - 80#64 + BitVec.ofNat 64 k).toNat ∨
        (sp - 80#64 + BitVec.ofNat 64 k).toNat + 8 ≤ (sp - 80#64 + BitVec.ofNat 64 j).toNat by
      rw [off j (by omega), off k (by omega)]; omega)
  have raBack := back 7 72 (by decide) ra rfl ⟨apart 72 64 (by decide) (by decide) (by decide), trivial⟩
  let R11 : Nat → BitVec 64 := fun n => if n = 1 then FdWrite.WriteFd.leave_call.link else
    if n = 2 then sp - 80#64 else len
  have keep11 := fun n lo hi => p11.toEffectPost.gpr_frame (by decide) n lo hi (by simp)
  obtain ⟨d12, run12, p12⟩ := (FdWrite.WriteFd.epi_fast d11 ra R11
    ⟨p11.good, p11.image, p11.minstret, (keep11 1 (by decide) (by decide)).trans l10.raReg,
      by simp only [R11, ↓reduceIte]; decide, p11.tick⟩
    ⟨(keep11 2 (by decide) (by decide)).trans l10.stack, (keep11 8 (by decide) (by decide)).trans l10.s0Reg, True.intro⟩
    (fun k hk => (L.slots k hk).read) raBack h.aligned).run d11 ⟨p11.pc, rfl⟩
  have later := fun (k : Nat) (hk : k ≤ 72) (ks : List Nat) (hks : ∀ j ∈ ks, j ≤ 72 ∧ (j + 8 ≤ k ∨ k + 8 ≤ j)) =>
    (show ∀ j ∈ ks, (sp - 80#64 + BitVec.ofNat 64 k).toNat + 8 ≤ (sp - 80#64 + BitVec.ofNat 64 j).toNat ∨
        (sp - 80#64 + BitVec.ofNat 64 j).toNat + 8 ≤ (sp - 80#64 + BitVec.ofNat 64 k).toNat from
      fun j hj => apart k j hk (hks j hj).1 (hks j hj).2.symm)
  have s0Back := back 8 64 (by decide) (R0 8) rfl trivial
  have s1Back := back 0 56 (by decide) (R0 9) rfl
    (by have a := later 56 (by decide) [48, 40, 32, 24, 16, 8, 72, 64] (by decide); exact ⟨a 48 (by simp), a 40 (by simp), a 32 (by simp), a 24 (by simp), a 16 (by simp), a 8 (by simp), a 72 (by simp),
      a 64 (by simp), trivial⟩)
  have s2Back := back 1 48 (by decide) (R0 18) rfl
    (by have a := later 48 (by decide) [40, 32, 24, 16, 8, 72, 64] (by decide); exact ⟨a 40 (by simp), a 32 (by simp), a 24 (by simp), a 16 (by simp), a 8 (by simp), a 72 (by simp), a 64 (by simp), trivial⟩)
  have s3Back := back 2 40 (by decide) (R0 19) rfl
    (by have a := later 40 (by decide) [32, 24, 16, 8, 72, 64] (by decide); exact ⟨a 32 (by simp), a 24 (by simp), a 16 (by simp), a 8 (by simp), a 72 (by simp), a 64 (by simp), trivial⟩)
  have s4Back := back 3 32 (by decide) (R0 20) rfl
    (by have a := later 32 (by decide) [24, 16, 8, 72, 64] (by decide); exact ⟨a 24 (by simp), a 16 (by simp), a 8 (by simp), a 72 (by simp), a 64 (by simp), trivial⟩)
  have s5Back := back 4 24 (by decide) (R0 21) rfl
    (by have a := later 24 (by decide) [16, 8, 72, 64] (by decide); exact ⟨a 16 (by simp), a 8 (by simp), a 72 (by simp), a 64 (by simp), trivial⟩)
  have s6Back := back 5 16 (by decide) (R0 22) rfl
    (by have a := later 16 (by decide) [8, 72, 64] (by decide); exact ⟨a 8 (by simp), a 72 (by simp), a 64 (by simp), trivial⟩)
  have s7Back := back 6 8 (by decide) (R0 23) rfl
    (by have a := later 8 (by decide) [72, 64] (by decide); exact ⟨a 72 (by simp), a 64 (by simp), trivial⟩)
  have restore : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23], gpr c n = some (R0 n) := fun n hn => by
    have := present n hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact this
  have load := fun (n k : Nat) (v : BitVec 64)
      (l : gpr d12 n = some (bytesVal .ld (read8 d11.σ.mem (sp - 80#64 + BitVec.ofNat 64 k).toNat)))
      (b : bytesVal .ld (read8 d11.σ.mem (sp - 80#64 + BitVec.ofNat 64 k).toNat) = v) =>
    (show gpr d12 n = some v by rw [l, b])
  have out6 : Vsa.Machine.output d6.σ = Vsa.Machine.output c.σ := by
    have o4 := e4.output
    unfold Vsa.Machine.output at *
    rw [q6.output, p5.output, o4, q3.output, p2.output, p1.output]
  refine ⟨d12, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
    (run9.trans (run10.trans (run11.trans run12)))))))))),
    p12.good, p12.image, p12.minstret, p12.tick, p12.toEffectPost.htifIdle (p11.toEffectPost.htifIdle l10.idle),
    p12.pc, load 1 72 ra (gholds_lookup _ p12.regs rfl) raBack, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have l : gpr d12 10 = some (R11 8) := gholds_lookup _ p12.regs rfl
    exact l
  · have l : gpr d12 2 = some (R11 2 + 80#64) := gholds_lookup _ p12.regs rfl
    rw [l]; simp only [R11, ↓reduceIte, Nat.reduceEqDiff, BitVec.sub_add_cancel]
  · intro n hn
    rw [restore n hn]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact load 8 64 _ (gholds_lookup _ p12.regs rfl) s0Back
    · exact load 9 56 _ (gholds_lookup _ p12.regs rfl) s1Back
    · exact load 18 48 _ (gholds_lookup _ p12.regs rfl) s2Back
    · exact load 19 40 _ (gholds_lookup _ p12.regs rfl) s3Back
    · exact load 20 32 _ (gholds_lookup _ p12.regs rfl) s4Back
    · exact load 21 24 _ (gholds_lookup _ p12.regs rfl) s5Back
    · exact load 22 16 _ (gholds_lookup _ p12.regs rfl) s6Back
    · exact load 23 8 _ (gholds_lookup _ p12.regs rfl) s7Back
  · intro n hn
    have b := hn; simp only [List.mem_cons, List.mem_nil_iff, or_false] at b
    rw [p12.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega),
      p11.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp),
      l10.kept n (by omega) (by omega) (by simp; omega),
      q9.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega),
      p8.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega),
      p7.rest n (by simp; omega), k6 n (by omega) (by omega) (by simp; omega),
      p1.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega)]
  · have o := p7.output
    have o10 := l10.output
    unfold Vsa.Machine.output at *
    rw [p12.output, p11.output, o10, q9.output, p8.output, o, out6]
  · intro x s e r
    rw [p12.memory, show writeLog d11.σ.mem [] = d11.σ.mem from rfl, frame11 x (by omega) e r,
      writeLog_out _ _ _ (within.outL (by omega))]

end OCaml.Vm.Primitives.ConsoleWrite
