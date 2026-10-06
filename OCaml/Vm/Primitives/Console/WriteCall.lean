import OCaml.Vm.Primitives.Console.Write
import OCaml.Vm.Primitives.FdWrite.Effects
import OCaml.Vm.Primitives.HtifFrame

/-! `write(fd, buf, n)` on a console descriptor: newlib's `write` tail-jumps
to `_write_r`, which clears `errno`, calls `_write` (`write_console`), finds
no error and returns `n`. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable
open ExitPath (LogWithin LogWithin.outL LogWithin.outLRange)
open FdWrite (errnoGlobal impurePtr)

/-- `write`'s native stack: `_write_r`'s 16-byte frame above `_write`'s, plus
the `errno` word, all apart from the descriptor table and the buffer. -/
structure WriteCallLayout (sp fd buf : BitVec 64) (len : Nat) : Prop where
  inner : WriteLayout (sp - 16#64) fd buf len
  frameLow : WriteWindow (sp - 16#64) 8
  frameHigh : WriteWindow (sp - 16#64 + 8#64) 8
  text : Image.textBase + Image.textSize ≤ sp.toNat - 16 ∨ sp.toNat ≤ Image.textBase
  rodata : Image.rodataBase + Image.rodataSize ≤ sp.toNat - 16 ∨ sp.toNat ≤ Image.rodataBase
  ready : fsReady.toNat + 8 ≤ sp.toNat - 16 ∨ sp.toNat ≤ fsReady.toNat
  kind : (kindAddress fd).toNat + 8 ≤ sp.toNat - 16 ∨ sp.toNat ≤ (kindAddress fd).toNat
  buffer : buf.toNat + len ≤ sp.toNat - 16 ∨ sp.toNat ≤ buf.toNat
  errnoReady : fsReady.toNat + 8 ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ fsReady.toNat
  errnoKind : (kindAddress fd).toNat + 8 ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ (kindAddress fd).toNat
  errnoBuffer : buf.toNat + len ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ buf.toNat
  errnoStack : errnoGlobal.toNat + 4 ≤ sp.toNat - 112 ∨ sp.toNat ≤ errnoGlobal.toNat

structure WriteCallInput (ra sp fd buf : BitVec 64) (bs : List UInt8) (c : Config) : Prop
    extends LeafInput ra c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  saved : ∀ n ∈ [8, 9, 18], (gprGet c.σ n).isSome
  stack : gpr c 2 = some sp
  fdReg : gpr c 10 = some fd
  bufReg : gpr c 11 = some buf
  lenReg : gpr c 12 = some (BitVec.ofNat 64 bs.length)
  layout : WriteCallLayout sp fd buf bs.length
  descriptor : ConsoleFd fd c
  ram : 0x80000000 ≤ buf.toNat ∧ buf.toNat + bs.length ≤ 0x100000000 ∧
    (buf.toNat + bs.length ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 8 ≤ buf.toNat)
  bytes : ∀ i x, bs[i]? = some x → (c.σ.mem[(buf + BitVec.ofNat 64 i).toNat]?).getD 0 = BitVec.ofNat 8 x.toNat

/-- Return from `write`: `n`, the bytes on the console, s0–s2 restored; only
the two native frames and `errno` were written. -/
structure WriteCallPost (ra sp : BitVec 64) (bs : List UInt8) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some ra
  result : gpr d 10 = some (BitVec.ofNat 64 bs.length)
  stack : gpr d 2 = some sp
  saved : ∀ n ∈ [8, 9, 18], gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ ++ bytesToString bs
  frame : ∀ x, ((sp.toNat - 112) > x ∨ sp.toNat ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0

theorem write_call {ra sp fd buf bs c} (h : WriteCallInput ra sp fd buf bs c)
    (entry : pcOf c = some 0x80042628#64) :
    ∃ d, Steps c d ∧ WriteCallPost ra sp bs c d := by
  have L := h.layout
  have present := fun n (hn : n ∈ [8, 9, 18]) => by
    have := h.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  let len : BitVec 64 := BitVec.ofNat 64 bs.length
  -- write: load the reentrancy pointer, tail-jump to _write_r
  let R0 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 10 then fd else if n = 11 then buf else len
  obtain ⟨d1, run1, p1⟩ := (FdWrite.Write.tail_fast c R0 h.toLeafInput
    ⟨h.raReg, h.fdReg, h.bufReg, h.lenReg, True.intro⟩).run c ⟨entry, rfl⟩
  have keep1 := fun n lo hi (hn : n ∉ [10, 11, 12, 13, 14]) => p1.toEffectPost.gpr_frame (by decide) n lo hi hn
  -- _write_r: save s0/ra, clear errno, call _write(fd, buf, n)
  let impure : BitVec 64 := bytesVal .ld (read8 c.σ.mem impurePtr.toNat)
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else
    if n = 8 then (gpr c 8).getD 0 else if n = 10 then impure else if n = 11 then fd else
    if n = 12 then buf else len
  have sp1 : gpr d1 2 = some sp := (keep1 2 (by decide) (by decide) (by simp)).trans h.stack
  have s01 : gpr d1 8 = some ((gpr c 8).getD 0) := (keep1 8 (by decide) (by decide) (by simp)).trans (present 8 (by simp))
  have sp16 : (sp - 16#64).toNat = sp.toNat - 16 := by
    have l := L.inner.low; have u := L.inner.high
    rw [BitVec.toNat_sub] at l u ⊢
    have := sp.isLt
    simp only [BitVec.toNat_ofNat] at l u ⊢
    omega
  have sp8 : (sp - 16#64 + 8#64).toNat = sp.toNat - 8 := by
    rw [BitVec.toNat_add, sp16]; have := L.inner.low; have := L.inner.high; rw [sp16] at *; simp; omega
  have imageText : OutLRange (FdWrite.WriteR.enterLog R1) Image.textBase Image.textSize := by
    simp only [OutLRange, FdWrite.WriteR.enterLog, R1, ↓reduceIte, Nat.reduceEqDiff]
    have t := L.text; have l := L.inner.low; rw [sp16] at l
    refine ⟨?_, ?_, ?_, trivial⟩
    · rw [sp16]; omega
    · rw [sp8]; omega
    · simp only [errnoGlobal]; decide
  have imageRodata : OutLRange (FdWrite.WriteR.enterLog R1) Image.rodataBase Image.rodataSize := by
    simp only [OutLRange, FdWrite.WriteR.enterLog, R1, ↓reduceIte, Nat.reduceEqDiff]
    have t := L.rodata; have l := L.inner.low; rw [sp16] at l
    refine ⟨?_, ?_, ?_, trivial⟩
    · rw [sp16]; omega
    · rw [sp8]; omega
    · simp only [errnoGlobal]; decide
  obtain ⟨d2, run2, p2⟩ := (FdWrite.WriteR.enter_fast d1 R1
    ⟨p1.good, p1.image, p1.minstret, gholds_lookup _ p1.regs rfl, h.aligned, p1.tick⟩
    ⟨gholds_lookup _ p1.regs rfl, sp1, s01, gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl,
      gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, True.intro⟩
    L.frameLow L.frameHigh
    ⟨imageText, imageRodata⟩).run d1 ⟨p1.pc, rfl⟩
  have keep2 := fun n lo hi (hn : n ∉ [2, 8, 10, 11, 12, 15]) => p2.toEffectPost.gpr_frame (by decide) n lo hi hn
  let a2 : GRegs := [(2, sp - 16#64), (8, impure), (10, fd), (11, buf), (12, len)]
  have J2 := call_registers_summary FdWrite.WriteR.enter_call_shape FdWrite.WriteR.enter_call_decode d2
    (FdWrite.WriteR.enter_call_pins p2.image) p2.good p2.image p2.tick p2.minstret a2
    ⟨gholds_lookup _ p2.regs rfl, gholds_lookup _ p2.regs rfl, gholds_lookup _ p2.regs rfl,
      gholds_lookup _ p2.regs rfl, gholds_lookup _ p2.regs rfl, True.intro⟩
    (by change KeysOK [2, 8, 10, 11, 12]; decide) (by simp [KeysAvoidRa, a2, keysG]) rfl
  obtain ⟨d3, run3, q3⟩ := J2.run d2 ⟨p2.pc, rfl⟩
  have mem3 : d3.σ.mem = writeLog c.σ.mem (FdWrite.WriteR.enterLog R1) := by
    rw [q3.memory, p2.memory, p1.memory]; rfl
  -- the stores miss everything _write reads from the caller
  have outside3 : ∀ x, (x < sp.toNat - 16 ∨ sp.toNat ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
      (d3.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    intro x stack errno
    rw [mem3, writeLog_out _ _ _ ?_]
    simp only [OutL, FdWrite.WriteR.enterLog, R1, ↓reduceIte, Nat.reduceEqDiff]
    have e1 := sp16; have e2 := sp8
    have low := L.inner.low; rw [sp16] at low
    refine ⟨by omega, by omega, by omega, trivial⟩
  have read3 : ∀ a, (a + 8 ≤ sp.toNat - 16 ∨ sp.toNat ≤ a) → (a + 8 ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ a) →
      read8 d3.σ.mem a = read8 c.σ.mem a := by
    intro a s e
    simp only [read8]
    rw [outside3 a (by omega) (by omega), outside3 (a + 1) (by omega) (by omega), outside3 (a + 2) (by omega) (by omega),
      outside3 (a + 3) (by omega) (by omega), outside3 (a + 4) (by omega) (by omega), outside3 (a + 5) (by omega) (by omega),
      outside3 (a + 6) (by omega) (by omega), outside3 (a + 7) (by omega) (by omega)]
  have keepq := fun n lo hi (hn : n ≠ 1) => q3.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn)
  have idle3 : d3.σ.regs.get? Register.htif_payload_writes = some (0#4) :=
    q3.toEffectPost.htifIdle (p2.toEffectPost.htifIdle (p1.toEffectPost.htifIdle h.idle))
  have saved3 : ∀ n ∈ [9, 18], gpr d3 n = gpr c n := by
    intro n hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl <;>
      exact (keepq _ (by decide) (by decide) (by decide)).trans ((keep2 _ (by decide) (by decide) (by simp)).trans
        (keep1 _ (by decide) (by decide) (by simp)))
  have D := h.descriptor
  have kindSame := read3 _ L.kind L.errnoKind
  have input : WriteInput FdWrite.WriteR.enter_call.link (sp - 16#64) fd buf bs d3 :=
    { good := q3.good, image := q3.image, minstret := q3.minstret, raReg := gholds_lookup _ q3.regs rfl,
      aligned := by decide, tick := q3.tick, idle := idle3
      saved := by
        intro n hn
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
        rcases hn with rfl | rfl | rfl
        · have l : gpr d3 8 = some impure := gholds_lookup _ q3.regs rfl
          change (gpr d3 8).isSome; rw [l]; rfl
        · change (gpr d3 9).isSome; rw [saved3 9 (by simp)]; exact h.saved 9 (by simp)
        · change (gpr d3 18).isSome; rw [saved3 18 (by simp)]; exact h.saved 18 (by simp)
      stack := gholds_lookup _ q3.regs rfl
      fdReg := gholds_lookup _ q3.regs rfl
      bufReg := gholds_lookup _ q3.regs rfl
      lenReg := gholds_lookup _ q3.regs rfl
      layout := L.inner
      descriptor := ⟨by rw [read3 _ L.ready L.errnoReady]; exact D.ready, D.range, D.kindWindow,
        by rw [kindSame]; exact D.console, by rw [kindSame]; exact D.notFile⟩
      ram := h.ram
      bytes := by
        intro i x hx
        have hi := (List.getElem?_eq_some_iff.mp hx).1
        have addr := cursor_toNat h.ram.2.1 (Nat.le_of_lt hi)
        rw [outside3 _ (by rw [addr]; have := L.buffer; omega) (by rw [addr]; have := L.errnoBuffer; omega)]
        exact h.bytes i x hx }
  obtain ⟨d4, run4, p4⟩ := write_console input (by rw [q3.pc]; rfl)
  have lenNat : len.toNat = bs.length := by
    have := h.ram.2.1; simp only [len, BitVec.toNat_ofNat]; omega
  let R4 : Nat → BitVec 64 := fun n => if n = 1 then FdWrite.WriteR.enter_call.link else if n = 2 then sp - 16#64 else
    if n = 8 then impure else len
  have s04 : gpr d4 8 = some impure := by
    rw [p4.saved 8 (by simp)]; exact gholds_lookup _ q3.regs rfl
  have link4 : gpr d4 1 = some FdWrite.WriteR.enter_call.link := by
    rw [p4.saved 1 (by simp)]; exact gholds_lookup _ q3.regs rfl
  obtain ⟨d5, run5, p5⟩ := (FdWrite.WriteR.check_fast d4 R4
    ⟨p4.good, p4.image, p4.minstret, link4, by simp only [R4, ↓reduceIte]; decide, p4.tick⟩
    ⟨link4, p4.stack, s04, p4.result, True.intro⟩
    (by
      simp only [R4, ↓reduceIte, Nat.reduceEqDiff]
      intro eq
      have h1 := congrArg BitVec.toNat eq
      rw [lenNat] at h1
      have h2 : (18446744073709551615#64 : BitVec 64).toNat = 18446744073709551615 := rfl
      have := h.ram.2.1
      omega)).run d4 ⟨p4.pc, rfl⟩
  -- the frame bytes read back through _write's footprint
  have frame45 : ∀ x, ((sp - 16#64).toNat - 96 > x ∨ (sp - 16#64).toNat ≤ x) →
      (d5.σ.mem[x]?).getD 0 = (d3.σ.mem[x]?).getD 0 := by
    intro x hx; rw [p5.memory]; exact p4.frame x hx
  have read5 : ∀ a, (sp - 16#64).toNat ≤ a → read8 d5.σ.mem a = read8 d3.σ.mem a := by
    intro a ha
    simp only [read8]
    rw [frame45 a (by omega), frame45 (a + 1) (by omega), frame45 (a + 2) (by omega), frame45 (a + 3) (by omega),
      frame45 (a + 4) (by omega), frame45 (a + 5) (by omega), frame45 (a + 6) (by omega), frame45 (a + 7) (by omega)]
  have errnoApart := L.errnoStack
  have low := L.inner.low; rw [sp16] at low
  have raBack : bytesVal .ld (read8 d5.σ.mem (sp - 16#64 + 8#64).toNat) = ra := by
    rw [read5 _ (by rw [sp8, sp16]; omega), read8_value, mem3]
    exact Gc.word_writeLog_at _ _ 1 _ _ rfl ⟨by
      simp only [R1, ↓reduceIte, Nat.reduceEqDiff, errnoGlobal] at errnoApart ⊢; rw [sp8]; omega, trivial⟩
  have s0Back : bytesVal .ld (read8 d5.σ.mem (sp - 16#64).toNat) = (gpr c 8).getD 0 := by
    rw [read5 _ (Nat.le_refl _), read8_value, mem3]
    exact Gc.word_writeLog_at _ _ 0 _ _ rfl ⟨by simp only [R1, ↓reduceIte, Nat.reduceEqDiff]; rw [sp16, sp8]; omega,
      by simp only [R1, ↓reduceIte, Nat.reduceEqDiff, errnoGlobal] at errnoApart ⊢; rw [sp16]; omega, trivial⟩
  let R5 : Nat → BitVec 64 := fun n => if n = 1 then FdWrite.WriteR.enter_call.link else
    if n = 2 then sp - 16#64 else len
  obtain ⟨d6, run6, p6⟩ := (FdWrite.WriteR.ret_fast d5 ra R5
    ⟨p5.good, p5.image, p5.minstret,
      (p5.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by simp)).trans link4,
      by simp only [R5, ↓reduceIte]; decide, p5.tick⟩
    ⟨(p5.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by simp)).trans p4.stack,
      (p5.toEffectPost.gpr_frame (by decide) 10 (by decide) (by decide) (by simp)).trans p4.result, True.intro⟩
    L.frameHigh.read L.frameLow.read raBack h.aligned).run d5 ⟨p5.pc, rfl⟩
  have keep56 := fun n lo hi (h1 : n ∉ [1, 2, 8, 15]) =>
    (p6.toEffectPost.gpr_frame (by decide) n lo hi (by simp at h1 ⊢; omega)).trans
      (p5.toEffectPost.gpr_frame (by decide) n lo hi (by simp at h1 ⊢; omega))
  have out3 : Vsa.Machine.output d3.σ = Vsa.Machine.output c.σ := by
    unfold Vsa.Machine.output; rw [q3.output, p2.output, p1.output]
  refine ⟨d6, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))),
    p6.good, p6.image, p6.minstret, p6.tick,
    p6.toEffectPost.htifIdle (p5.toEffectPost.htifIdle p4.idle), p6.pc, ?_, ?_, ?_, ?_, ?_⟩
  · have l : gpr d6 10 = some (R5 10) := gholds_lookup _ p6.regs rfl
    exact l
  · have l : gpr d6 2 = some (R5 2 + 16#64) := gholds_lookup _ p6.regs rfl
    rw [l]; simp only [R5, ↓reduceIte, Nat.reduceEqDiff, BitVec.sub_add_cancel]
  · intro n hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · have l : gpr d6 8 = some (bytesVal .ld (read8 d5.σ.mem (R5 2).toNat)) := gholds_lookup _ p6.regs rfl
      rw [l]
      simp only [R5, ↓reduceIte, Nat.reduceEqDiff]
      rw [s0Back]; exact (present 8 (by simp)).symm
    · rw [keep56 9 (by decide) (by decide) (by simp), p4.saved 9 (by simp)]; exact saved3 9 (by simp)
    · rw [keep56 18 (by decide) (by decide) (by simp), p4.saved 18 (by simp)]; exact saved3 18 (by simp)
  · have o6 : Vsa.Machine.output d6.σ = Vsa.Machine.output d4.σ := by
      unfold Vsa.Machine.output; rw [p6.output, p5.output]
    rw [o6, p4.output, out3]
  · intro x stack errno
    rw [p6.memory, show writeLog d5.σ.mem [] = d5.σ.mem from rfl, frame45 x (by rw [sp16]; omega)]
    exact outside3 x (by omega) errno
