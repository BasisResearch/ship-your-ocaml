import OCaml.Vm.Primitives.Console.WriteFd
import OCaml.Vm.Primitives.Flush.FlushPartial
import OCaml.Vm.Primitives.Flush.CheckPending

/-! `caml_flush_partial(channel)` on a console output channel with a nonempty
buffer and no pending actions: one `caml_write_fd` of the whole buffer, then
`offset += n`, `curr := buff`, and the result 1 (the buffer is empty). -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable
open ExitPath (LogWithin LogWithin.outL LogWithin.outLRange)
open FdWrite (errnoGlobal impurePtr enterHook leaveHook pendingSignals)

/-- `caml_something_to_do`: a pending-action request. -/
def somethingToDo : BitVec 64 := 0x80064b30#64

/-- `(curr - buff)` as `subw` computes it, for a length below 2^31. -/
theorem subw_len (b : BitVec 64) (n : Nat) (h : n < 2 ^ 31) :
    BitVec.signExtend 64 (Sail.BitVec.extractLsb (b + BitVec.ofNat 64 n) 31 0 - Sail.BitVec.extractLsb b 31 0) =
      BitVec.ofNat 64 n := by
  have e : Sail.BitVec.extractLsb (b + BitVec.ofNat 64 n) 31 0 - Sail.BitVec.extractLsb b 31 0 = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.extractLsb, BitVec.toNat_sub, BitVec.toNat_add]
    have := b.isLt
    omega
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  have m : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  simp [m]; omega

theorem positive_len (n : Nat) (h0 : 0 < n) (h : n < 2 ^ 31) : guardB .BLT 0#64 (BitVec.ofNat 64 n) = true := by
  simp only [guardB, Functions.zopz0zI_s, decide_eq_true_eq]
  have t : (BitVec.ofNat 64 n).toInt = n := by
    rw [BitVec.toInt_eq_toNat_of_lt] <;> simp <;> omega
  rw [t]; simp; omega

theorem not_minus_one (n : Nat) (h : n < 2 ^ 31) : guardB .BNE (BitVec.ofNat 64 n) 18446744073709551615#64 = true := by
  simp only [guardB, bne_iff_ne, ne_eq]
  intro e; have := congrArg BitVec.toNat e; simp at this; omega

theorem whole_len (x : BitVec 64) : guardB .BLT x x = false := by
  simp [guardB, Functions.zopz0zI_s]

theorem seqz_same (x : BitVec 64) : compareValue true (x - x) 1#64 = 1#64 := by
  simp [compareValue]; decide

/-- The native stack of `caml_flush_partial` (an 80-byte frame above
`caml_write_fd`'s `WriteFdLayout`) and the channel's header, apart from it,
from `errno` and from the reentrancy `errno` word. -/
structure FlushLayout (sp ch fd rp : BitVec 64) (len : Nat) : Prop where
  inner : WriteFdLayout (sp - 80#64) fd (ch + 72#64) rp len
  slots : ∀ k ∈ [24, 32, 40, 48, 56, 64, 72], WriteWindow (sp - 80#64 + BitVec.ofNat 64 k) 8
  floor : 0x80000000 + 272 ≤ sp.toNat
  top : sp.toNat ≤ 0x100000000
  text : Image.textBase + Image.textSize ≤ sp.toNat - 80 ∨ sp.toNat ≤ Image.textBase
  rodata : Image.rodataBase + Image.rodataSize ≤ sp.toNat - 80 ∨ sp.toNat ≤ Image.rodataBase
  outer : ∀ a ∈ [fsReady.toNat, (kindAddress fd).toNat, enterHook.toNat, leaveHook.toNat, impurePtr.toNat,
    rp.toNat, errnoGlobal.toNat, somethingToDo.toNat], a + 8 ≤ sp.toNat - 80 ∨ sp.toNat ≤ a
  pending : pendingSignals.toNat + 256 ≤ sp.toNat - 80 ∨ sp.toNat ≤ pendingSignals.toNat
  buffer : ch.toNat + 72 + len ≤ sp.toNat - 80 ∨ sp.toNat ≤ ch.toNat + 72
  chan : ch.toNat + 72 ≤ sp.toNat - 272 ∨ sp.toNat ≤ ch.toNat
  chanRam : ch.toNat + 72 ≤ 0x100000000
  chanErrno : ch.toNat + 72 ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ ch.toNat
  chanRp : ch.toNat + 72 ≤ rp.toNat ∨ rp.toNat + 4 ≤ ch.toNat
  fdWindow : ReadWindow ch 4
  flagsWindow : ReadWindow (ch + 68#64) 4
  offsetWindow : WriteWindow (ch + 8#64) 8
  currWindow : WriteWindow (ch + 24#64) 8
  chanText : ch.toNat + 72 ≤ Image.textBase ∨ Image.textBase + Image.textSize ≤ ch.toNat
  chanRodata : ch.toNat + 72 ≤ Image.rodataBase ∨ Image.rodataBase + Image.rodataSize ≤ ch.toNat

structure FlushInput (ra sp ch fd rp off : BitVec 64) (bs : List UInt8) (c : Config) : Prop
    extends LeafInput ra c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], (gprGet c.σ n).isSome
  stack : gpr c 2 = some sp
  chanReg : gpr c 10 = some ch
  short : bs.length < 2 ^ 31
  nonempty : 0 < bs.length
  layout : FlushLayout sp ch fd rp bs.length
  fdWord : bytesVal .lw (read8 c.σ.mem ch.toNat) = fd
  descriptor : ConsoleFd fd c
  curr : bytesVal .ld (read8 c.σ.mem (ch + 24#64).toNat) = ch + 72#64 + BitVec.ofNat 64 bs.length
  offset : bytesVal .ld (read8 c.σ.mem (ch + 8#64).toNat) = off
  ram : 0x80000000 ≤ (ch + 72#64).toNat ∧ (ch + 72#64).toNat + bs.length ≤ 0x100000000 ∧
    ((ch + 72#64).toNat + bs.length ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 8 ≤ (ch + 72#64).toNat)
  bytes : ∀ i x, bs[i]? = some x →
    (c.σ.mem[(ch + 72#64 + BitVec.ofNat 64 i).toNat]?).getD 0 = BitVec.ofNat 8 x.toNat
  enterHookWord : bytesVal .ld (read8 c.σ.mem enterHook.toNat) = 0x8000d2a4#64
  leaveHookWord : bytesVal .ld (read8 c.σ.mem leaveHook.toNat) = 0x8000d2a8#64
  impure : bytesVal .ld (read8 c.σ.mem impurePtr.toNat) = rp
  clear : NoPendingSignals c.σ.mem
  quiet : bytesVal .lw (read8 c.σ.mem somethingToDo.toNat) = 0#64

/-- Return from `caml_flush_partial`: 1, the buffer on the console, `curr`
reset to the buffer start, `offset` advanced; only the native stack, the two
`errno` words and the two channel words were written. -/
structure FlushPost (ra sp ch rp off : BitVec 64) (bs : List UInt8) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some ra
  raReg : gpr d 1 = some ra
  result : gpr d 10 = some 1#64
  stack : gpr d 2 = some sp
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ ++ bytesToString bs
  curr : bytesVal .ld (read8 d.σ.mem (ch + 24#64).toNat) = ch + 72#64
  offset : bytesVal .ld (read8 d.σ.mem (ch + 8#64).toNat) = off + BitVec.ofNat 64 bs.length
  frame : ∀ x, (x < sp.toNat - 272 ∨ sp.toNat ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
    (x < rp.toNat ∨ rp.toNat + 4 ≤ x) → (x < ch.toNat + 8 ∨ ch.toNat + 16 ≤ x) →
    (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0

theorem flush_partial {ra sp ch fd rp off bs c} (h : FlushInput ra sp ch fd rp off bs c)
    (entry : pcOf c = some 0x80015408#64) :
    ∃ d, Steps c d ∧ FlushPost ra sp ch rp off bs c d := by
  have L := h.layout
  have present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr c n = some ((gpr c n).getD 0) := by
    intro n hn
    have := h.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  let len : BitVec 64 := BitVec.ofNat 64 bs.length
  let buf : BitVec 64 := ch + 72#64
  have floor := L.floor
  have off80 : ∀ k, k ≤ 80 → (sp - 80#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 80 + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  have sp80 : (sp - 80#64).toNat = sp.toNat - 80 := by
    rw [BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  have chRam := L.chanRam
  have chOff : ∀ k, k ≤ 72 → (ch + BitVec.ofNat 64 k).toNat = ch.toNat + k := by
    intro k hk; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  -- prologue
  let R0 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else if n = 10 then ch else
    (gpr c n).getD 0
  have within : LogWithin (Flush.FlushPartial.proLog R0 []) (sp.toNat - 80) sp.toNat := by
    intro e he
    simp only [Flush.FlushPartial.proLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; rw [off80 _ (by decide)]; omega)
  have slot := fun k (hk : k ∈ [24, 32, 40, 48, 56, 64, 72]) => L.slots k hk
  obtain ⟨d1, run1, p1⟩ := (Flush.FlushPartial.pro_fast c R0 h.toLeafInput
    ⟨h.raReg, h.stack, present 8 (by simp), present 9 (by simp), h.chanReg, present 18 (by simp),
      present 19 (by simp), present 20 (by simp), present 21 (by simp), True.intro⟩
    (slot 64 (by simp)) (slot 48 (by simp)) (slot 40 (by simp)) (slot 32 (by simp)) (slot 24 (by simp))
    (slot 72 (by simp)) (slot 56 (by simp))
    ⟨within.outLRange (by have := L.text; omega), within.outLRange (by have := L.rodata; omega)⟩).run c ⟨entry, rfl⟩
  have mem1 : d1.σ.mem = writeLog c.σ.mem (Flush.FlushPartial.proLog R0 []) := p1.memory
  have read1 : ∀ a, (a + 8 ≤ sp.toNat - 80 ∨ sp.toNat ≤ a) → read8 d1.σ.mem a = read8 c.σ.mem a := by
    intro a ha; rw [mem1]; exact read8_outside within ha
  have outer := L.outer
  have chan := L.chan
  -- caml_check_pending_actions: nothing to do
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 18 then buf else ch
  have ra1 : gpr d1 1 = some ra := gholds_lookup _ p1.regs rfl
  obtain ⟨d2, run2, p2⟩ := (Flush.FlushPartial.head_fast d1 R1
    ⟨p1.good, p1.image, p1.minstret, ra1, h.aligned, p1.tick⟩
    ⟨ra1, gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, True.intro⟩).run
    d1 ⟨p1.pc, rfl⟩
  have J2 := call_registers_summary Flush.FlushPartial.head_call_shape Flush.FlushPartial.head_call_decode d2
    (Flush.FlushPartial.head_call_pins p2.image) p2.good p2.image p2.tick p2.minstret
    [(10, ch)] ⟨gholds_lookup _ p2.regs rfl, True.intro⟩
    (by change KeysOK [10]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  obtain ⟨d3, run3, q3⟩ := J2.run d2 ⟨p2.pc, rfl⟩
  let R3 : Nat → BitVec 64 := fun _ => Flush.FlushPartial.head_call.link
  obtain ⟨d4, run4, p4⟩ := (Flush.CheckPending.leaf_fast d3 R3
    ⟨q3.good, q3.image, q3.minstret, gholds_lookup _ q3.regs rfl, by simp only [R3]; decide, q3.tick⟩
    ⟨gholds_lookup _ q3.regs rfl, True.intro⟩).run d3 ⟨by show pcOf _ = _; rw [q3.pc]; rfl, rfl⟩
  have mem4 : d4.σ.mem = d1.σ.mem := by
    rw [p4.memory, show writeLog d3.σ.mem [] = d3.σ.mem from rfl, q3.memory, p2.memory]; rfl
  have zero4 : gpr d4 10 = some 0#64 := by
    have l : gpr d4 10 = some (bytesVal .lw (read8 d3.σ.mem somethingToDo.toNat)) := gholds_lookup _ p4.regs rfl
    rw [l, q3.memory, p2.memory, show writeLog d1.σ.mem [] = d1.σ.mem from rfl,
      read1 _ (by have := outer somethingToDo.toNat (by simp); omega), h.quiet]
  -- registers after the call, against d1
  have k4 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 10] → gpr d4 n = gpr d1 n := fun n lo hi hn => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    rw [p4.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      q3.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p2.toEffectPost.gpr_frame (by decide) n lo hi (by simp)]
  have link4 : gpr d4 1 = some Flush.FlushPartial.head_call.link := gholds_lookup _ p4.regs rfl
  let R4 : Nat → BitVec 64 := fun n => if n = 1 then Flush.FlushPartial.head_call.link else
    if n = 10 then 0#64 else if n = 18 then buf else ch
  obtain ⟨d5, run5, p5⟩ := (Flush.FlushPartial.pending_fast d4 R4
    ⟨p4.good, p4.image, p4.minstret, link4, by simp only [R4, ↓reduceIte]; decide, p4.tick⟩
    ⟨link4, (k4 8 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl), zero4,
      (k4 18 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl), True.intro⟩
    (by simp [R4, guardB])).run d4 ⟨p4.pc, rfl⟩
  -- the buffer is nonempty: towrite = n
  have curr5 : bytesVal .ld (read8 d5.σ.mem (ch + 24#64).toNat) = buf + len := by
    rw [p5.memory, show writeLog d4.σ.mem [] = d4.σ.mem from rfl, mem4,
      read1 _ (by rw [chOff 24 (by decide)]; omega), h.curr]
  have link5 : gpr d5 1 = some Flush.FlushPartial.head_call.link :=
    (p5.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by simp)).trans link4
  have k5 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 10] → gpr d5 n = gpr d1 n := fun n lo hi hn =>
    (p5.toEffectPost.gpr_frame (by decide) n lo hi (by simp)).trans (k4 n lo hi hn)
  let R5 : Nat → BitVec 64 := fun n => if n = 1 then Flush.FlushPartial.head_call.link else
    if n = 18 then buf else ch
  have regs5 : GHolds d5.σ (Flush.FlushPartial.more_input R5) :=
    ⟨link5, (k5 8 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl),
      (k5 18 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl), True.intro⟩
  have towrite : BitVec.signExtend 64 (Sail.BitVec.extractLsb
      (bytesVal .ld ((Flush.FlushPartial.more_loads d5.σ.mem R5).getD 0 [])) 31 0 -
      Sail.BitVec.extractLsb (R5 18) 31 0) = len := by
    show BitVec.signExtend 64 (Sail.BitVec.extractLsb (bytesVal .ld (read8 d5.σ.mem (ch + 24#64).toNat)) 31 0 -
      Sail.BitVec.extractLsb buf 31 0) = len
    rw [curr5]; exact subw_len buf _ h.short
  obtain ⟨d6, run6, p6⟩ := (Flush.FlushPartial.more_fast d5 R5
    ⟨p5.good, p5.image, p5.minstret, link5, by simp only [R5, ↓reduceIte]; decide, p5.tick⟩ regs5
    L.currWindow.read (by rw [towrite]; exact positive_len _ h.nonempty h.short)).run d5 ⟨p5.pc, rfl⟩
  have len6 : gpr d6 9 = some len := by
    have l : gpr d6 9 = some (BitVec.signExtend 64 (Sail.BitVec.extractLsb
      (bytesVal .ld ((Flush.FlushPartial.more_loads d5.σ.mem R5).getD 0 [])) 31 0 -
      Sail.BitVec.extractLsb (R5 18) 31 0)) := gholds_lookup _ p6.regs rfl
    rw [l, towrite]
  have len6' : gpr d6 13 = some len := by
    have l : gpr d6 13 = some (BitVec.signExtend 64 (Sail.BitVec.extractLsb
      (bytesVal .ld ((Flush.FlushPartial.more_loads d5.σ.mem R5).getD 0 [])) 31 0 -
      Sail.BitVec.extractLsb (R5 18) 31 0)) := gholds_lookup _ p6.regs rfl
    rw [l, towrite]
  -- load fd and flags, call caml_write_fd(fd, flags, buff, n)
  let R6 : Nat → BitVec 64 := fun n => if n = 1 then Flush.FlushPartial.head_call.link else
    if n = 8 then ch else if n = 9 then len else if n = 12 then buf else if n = 13 then len else buf
  have link6 : gpr d6 1 = some Flush.FlushPartial.head_call.link :=
    (p6.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by simp)).trans link5
  have ch6 : gpr d6 8 = some ch :=
    (p6.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by simp)).trans
      ((k5 8 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl))
  have buf6 : gpr d6 18 = some buf :=
    (p6.toEffectPost.gpr_frame (by decide) 18 (by decide) (by decide) (by simp)).trans
      ((k5 18 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl))
  obtain ⟨d7, run7, p7⟩ := (Flush.FlushPartial.write_fast d6 R6
    ⟨p6.good, p6.image, p6.minstret, link6, by simp only [R6, ↓reduceIte]; decide, p6.tick⟩
    ⟨link6, ch6, len6, gholds_lookup _ p6.regs rfl, len6', buf6, True.intro⟩
    L.flagsWindow L.fdWindow).run
    d6 ⟨p6.pc, rfl⟩
  have mem7 : d7.σ.mem = d1.σ.mem := by
    rw [p7.memory, show writeLog d6.σ.mem [] = d6.σ.mem from rfl, p6.memory,
      show writeLog d5.σ.mem [] = d5.σ.mem from rfl, p5.memory, show writeLog d4.σ.mem [] = d4.σ.mem from rfl, mem4]
  have fd7 : gpr d7 10 = some fd := by
    have l : gpr d7 10 = some (bytesVal .lw (read8 d6.σ.mem ch.toNat)) := gholds_lookup _ p7.regs rfl
    rw [l, show d6.σ.mem = d1.σ.mem by rw [← mem7, p7.memory]; rfl,
      read1 _ (by omega), h.fdWord]
  have J7 := call_registers_summary Flush.FlushPartial.write_call_shape Flush.FlushPartial.write_call_decode d7
    (Flush.FlushPartial.write_call_pins p7.image) p7.good p7.image p7.tick p7.minstret
    [(10, fd), (12, buf), (13, len)] ⟨fd7, gholds_lookup _ p7.regs rfl, gholds_lookup _ p7.regs rfl, True.intro⟩
    (by change KeysOK [10, 12, 13]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  obtain ⟨d8, run8, q8⟩ := J7.run d7 ⟨p7.pc, rfl⟩
  have mem8 : d8.σ.mem = d1.σ.mem := by rw [q8.memory, mem7]
  have read8' : ∀ a, (a + 8 ≤ sp.toNat - 80 ∨ sp.toNat ≤ a) → read8 d8.σ.mem a = read8 c.σ.mem a := by
    intro a ha; rw [mem8]; exact read1 a ha
  have k8 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 9, 10, 11, 12, 13, 15] → gpr d8 n = gpr d1 n := fun n lo hi hn => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    rw [q8.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p7.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p6.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega), k5 n lo hi (by simp; omega)]
  have len8 : gpr d8 9 = some len :=
    (q8.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by simp)).trans
      ((p7.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by simp)).trans len6)
  have idle8 := q8.toEffectPost.htifIdle (p7.toEffectPost.htifIdle (p6.toEffectPost.htifIdle
    (p5.toEffectPost.htifIdle (p4.toEffectPost.htifIdle (q3.toEffectPost.htifIdle (p2.toEffectPost.htifIdle
      (p1.toEffectPost.htifIdle h.idle)))))))
  have isSome : ∀ {d : Config} {n : Nat} {v : BitVec 64}, gpr d n = some v → (gprGet d.σ n).isSome := by
    intro d n v e; change (gpr d n).isSome; rw [e]; rfl
  have D := h.descriptor
  have kind8 := read8' (kindAddress fd).toNat (by have := outer (kindAddress fd).toNat (by simp); omega)
  have input : WriteFdInput Flush.FlushPartial.write_call.link (sp - 80#64) fd buf rp bs d8 :=
    { good := q8.good, image := q8.image, minstret := q8.minstret, raReg := gholds_lookup _ q8.regs rfl,
      aligned := by decide, tick := q8.tick, idle := idle8
      saved := by
        intro n hn
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact isSome ((k8 8 (by decide) (by decide) (by simp)).trans (gholds_lookup (v := ch) _ p1.regs rfl))
        · exact isSome len8
        · exact isSome ((k8 18 (by decide) (by decide) (by simp)).trans (gholds_lookup (v := buf) _ p1.regs rfl))
        · exact isSome ((k8 19 (by decide) (by decide) (by simp)).trans
            (gholds_lookup (v := 18446744073709551615#64) _ p1.regs rfl))
        · exact isSome ((k8 20 (by decide) (by decide) (by simp)).trans (gholds_lookup (v := 0x80064b58#64) _ p1.regs rfl))
        · exact isSome ((k8 21 (by decide) (by decide) (by simp)).trans (gholds_lookup (v := 0x80064b50#64) _ p1.regs rfl))
        · exact isSome ((k8 22 (by decide) (by decide) (by simp)).trans
            ((p1.toEffectPost.gpr_frame (by decide) 22 (by decide) (by decide) (by simp)).trans (present 22 (by simp))))
        · exact isSome ((k8 23 (by decide) (by decide) (by simp)).trans
            ((p1.toEffectPost.gpr_frame (by decide) 23 (by decide) (by decide) (by simp)).trans (present 23 (by simp))))
      stack := (k8 2 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl)
      fdReg := gholds_lookup _ q8.regs rfl
      bufReg := gholds_lookup _ q8.regs rfl
      lenReg := gholds_lookup _ q8.regs rfl
      short := h.short
      layout := L.inner
      descriptor := ⟨by rw [read8' _ (by have := outer fsReady.toNat (by simp); omega)]; exact D.ready, D.range,
        D.kindWindow, by rw [kind8]; exact D.console, by rw [kind8]; exact D.notFile⟩
      ram := h.ram
      bytes := by
        intro i x hx
        have hi := (List.getElem?_eq_some_iff.mp hx).1
        have addr := cursor_toNat h.ram.2.1 (Nat.le_of_lt hi)
        have b := L.buffer
        rw [mem8, mem1, writeLog_out _ _ _ (within.outL (by rw [addr, chOff 72 (by decide)]; omega))]
        exact h.bytes i x hx
      enterHookWord := by
        rw [read8' _ (by have := outer enterHook.toNat (by simp); omega)]; exact h.enterHookWord
      leaveHookWord := by
        rw [read8' _ (by have := outer leaveHook.toNat (by simp); omega)]; exact h.leaveHookWord
      impure := by rw [read8' _ (by have := outer impurePtr.toNat (by simp); omega)]; exact h.impure
      clear := by
        intro i hi
        rw [read8' _ (by rw [slot_toNat i hi]; have hp := L.pending; generalize pendingSignals.toNat = P at hp ⊢; omega)]
        exact h.clear i hi }
  obtain ⟨d9, run9, p9⟩ := write_fd input (by rw [q8.pc]; rfl)
  have errnoOut := outer errnoGlobal.toNat (by simp)
  have rpOut := outer rp.toNat (by simp)
  have chErr := L.chanErrno
  have chRp := L.chanRp
  have frame9 : ∀ x, (x < sp.toNat - 272 ∨ sp.toNat - 80 ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
      (x < rp.toNat ∨ rp.toNat + 4 ≤ x) → (d9.σ.mem[x]?).getD 0 = (d1.σ.mem[x]?).getD 0 := by
    intro x s e r
    rw [p9.frame x (by rw [sp80]; omega) e r, mem8]
  have read9 : ∀ a, (a + 8 ≤ sp.toNat - 272 ∨ sp.toNat - 80 ≤ a) → (a + 8 ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ a) →
      (a + 8 ≤ rp.toNat ∨ rp.toNat + 4 ≤ a) → read8 d9.σ.mem a = read8 d1.σ.mem a := by
    intro a s e r
    simp only [read8]
    rw [frame9 a (by omega) (by omega) (by omega), frame9 (a + 1) (by omega) (by omega) (by omega),
      frame9 (a + 2) (by omega) (by omega) (by omega), frame9 (a + 3) (by omega) (by omega) (by omega),
      frame9 (a + 4) (by omega) (by omega) (by omega), frame9 (a + 5) (by omega) (by omega) (by omega),
      frame9 (a + 6) (by omega) (by omega) (by omega), frame9 (a + 7) (by omega) (by omega) (by omega)]
  -- channel words read back from the call site
  have chanRead : ∀ k, k ≤ 64 → read8 d9.σ.mem (ch + BitVec.ofNat 64 k).toNat = read8 c.σ.mem (ch + BitVec.ofNat 64 k).toNat := by
    intro k hk
    rw [read9 _ (by rw [chOff k (by omega)]; omega) (by rw [chOff k (by omega)]; omega)
      (by rw [chOff k (by omega)]; omega), read1 _ (by rw [chOff k (by omega)]; omega)]
  have link9 := p9.raReg
  have k9 : ∀ n ∈ [8, 18, 19, 20, 21, 22, 23], gpr d9 n = gpr d8 n := fun n hn => p9.saved n (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn ⊢; omega)
  have ch9 : gpr d9 8 = some ch :=
    (k9 8 (by simp)).trans ((k8 8 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl))
  have buf9 : gpr d9 18 = some buf :=
    (k9 18 (by simp)).trans ((k8 18 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl))
  have minus9 : gpr d9 19 = some 18446744073709551615#64 :=
    (k9 19 (by simp)).trans ((k8 19 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl))
  have len9 : gpr d9 9 = some len := (p9.saved 9 (by simp)).trans len8
  let R9 : Nat → BitVec 64 := fun n => if n = 1 then Flush.FlushPartial.write_call.link else
    if n = 8 then ch else if n = 18 then buf else if n = 19 then 18446744073709551615#64 else len
  obtain ⟨d10, run10, p10⟩ := (Flush.FlushPartial.result_fast d9 R9
    ⟨p9.good, p9.image, p9.minstret, link9, by simp only [R9, ↓reduceIte]; decide, p9.tick⟩
    ⟨link9, ch9, len9, p9.result, buf9, minus9, True.intro⟩
    (not_minus_one _ h.short)).run d9 ⟨p9.pc, rfl⟩
  have keep10 := fun n (hn : n ≠ 15) (lo : 1 ≤ n) (hi : n ≤ 31) =>
    p10.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn)
  -- offset += n; the whole buffer was written
  let R10 : Nat → BitVec 64 := fun n => if n = 1 then Flush.FlushPartial.write_call.link else
    if n = 8 then ch else if n = 18 then buf else len
  have adjWithin : LogWithin (Flush.FlushPartial.adjustLog R10 (Flush.FlushPartial.adjust_loads d10.σ.mem R10))
      (ch.toNat + 8) (ch.toNat + 16) := by
    intro e he
    simp only [Flush.FlushPartial.adjustLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he; simp only [R10, ↓reduceIte, Nat.reduceEqDiff]; rw [chOff 8 (by decide)]; omega
  obtain ⟨d11, run11, p11⟩ := (Flush.FlushPartial.adjust_fast d10 R10
    ⟨p10.good, p10.image, p10.minstret, (keep10 1 (by decide) (by decide) (by decide)).trans link9,
      by simp only [R10, ↓reduceIte]; decide, p10.tick⟩
    ⟨(keep10 1 (by decide) (by decide) (by decide)).trans link9, (keep10 8 (by decide) (by decide) (by decide)).trans ch9,
      (keep10 9 (by decide) (by decide) (by decide)).trans len9,
      (keep10 10 (by decide) (by decide) (by decide)).trans p9.result,
      gholds_lookup _ p10.regs rfl, (keep10 18 (by decide) (by decide) (by decide)).trans buf9, True.intro⟩
    L.offsetWindow.read L.offsetWindow
    ⟨adjWithin.outLRange (by have := L.chanText; omega), adjWithin.outLRange (by have := L.chanRodata; omega)⟩
    (whole_len _)).run d10 ⟨p10.pc, rfl⟩
  have mem11 : d11.σ.mem = writeLog d9.σ.mem
      (Flush.FlushPartial.adjustLog R10 (Flush.FlushPartial.adjust_loads d10.σ.mem R10)) := by
    rw [p11.memory, p10.memory]; rfl
  -- curr -= n
  let R11 : Nat → BitVec 64 := R10
  have keep11 := fun n (hn : n ≠ 14) (lo : 1 ≤ n) (hi : n ≤ 31) =>
    p11.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn)
  have shWithin : LogWithin (Flush.FlushPartial.shiftLog R11 (Flush.FlushPartial.shift_loads d11.σ.mem R11))
      (ch.toNat + 24) (ch.toNat + 32) := by
    intro e he
    simp only [Flush.FlushPartial.shiftLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he; simp only [R11, R10, ↓reduceIte, Nat.reduceEqDiff]; rw [chOff 24 (by decide)]; omega
  have link11 := (keep11 1 (by decide) (by decide) (by decide)).trans ((keep10 1 (by decide) (by decide) (by decide)).trans link9)
  obtain ⟨d12, run12, p12⟩ := (Flush.FlushPartial.shift_fast d11 R11
    ⟨p11.good, p11.image, p11.minstret, link11, by simp only [R11, R10, ↓reduceIte]; decide, p11.tick⟩
    ⟨link11, (keep11 8 (by decide) (by decide) (by decide)).trans ((keep10 8 (by decide) (by decide) (by decide)).trans ch9),
      (keep11 15 (by decide) (by decide) (by decide)).trans (gholds_lookup _ p10.regs rfl),
      (keep11 18 (by decide) (by decide) (by decide)).trans ((keep10 18 (by decide) (by decide) (by decide)).trans buf9),
      True.intro⟩
    L.currWindow.read L.currWindow
    ⟨shWithin.outLRange (by have := L.chanText; omega), shWithin.outLRange (by have := L.chanRodata; omega)⟩).run
    d11 ⟨p11.pc, rfl⟩
  have curr11 : bytesVal .ld (read8 d11.σ.mem (ch + 24#64).toNat) = buf + len := by
    rw [mem11, read8_outside adjWithin (by rw [chOff 24 (by decide)]; omega),
      show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, chanRead 24 (by decide)]
    exact h.curr
  have newCurr : bytesVal .ld ((Flush.FlushPartial.shift_loads d11.σ.mem R11).getD 0 []) - R11 15 = buf := by
    show bytesVal .ld (read8 d11.σ.mem (ch + 24#64).toNat) - len = buf
    rw [curr11]; exact BitVec.add_sub_cancel _ _
  -- epilogue: reload the saves, return curr == buff
  have keep12 := fun n (hn : n ≠ 10) (lo : 1 ≤ n) (hi : n ≤ 31) =>
    p12.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn)
  let R12 : Nat → BitVec 64 := fun n => if n = 1 then Flush.FlushPartial.write_call.link else
    if n = 2 then sp - 80#64 else buf
  have link12 := (keep12 1 (by decide) (by decide) (by decide)).trans link11
  have mem12 : d12.σ.mem = writeLog (writeLog d9.σ.mem
      (Flush.FlushPartial.adjustLog R10 (Flush.FlushPartial.adjust_loads d10.σ.mem R10)))
      (Flush.FlushPartial.shiftLog R11 (Flush.FlushPartial.shift_loads d11.σ.mem R11)) := by
    rw [p12.memory, mem11]
  have read12 : ∀ a, sp.toNat - 80 ≤ a → a + 8 ≤ sp.toNat →
      read8 d12.σ.mem a = read8 (writeLog c.σ.mem (Flush.FlushPartial.proLog R0 [])) a := by
    intro a lo hi
    rw [mem12, read8_outside shWithin (by omega), read8_outside adjWithin (by omega),
      read9 a (by omega) (by omega) (by omega), mem1]
  have back := fun (i k : Nat) (hk : k ≤ 72) (v : BitVec 64)
      (sel : (Flush.FlushPartial.proLog R0 [])[i]? = some ((sp - 80#64 + BitVec.ofNat 64 k).toNat, 8, v))
      (after : OutLRange ((Flush.FlushPartial.proLog R0 []).drop (i + 1)) (sp - 80#64 + BitVec.ofNat 64 k).toNat 8) =>
    (show bytesVal .ld (read8 d12.σ.mem (sp - 80#64 + BitVec.ofNat 64 k).toNat) = v by
      rw [read12 _ (by rw [off80 k (by omega)]; omega) (by rw [off80 k (by omega)]; omega), read8_value]
      exact Gc.word_writeLog_at _ _ i _ _ sel after)
  have apart := fun (j k : Nat) (hj : j ≤ 72) (hk : k ≤ 72) (ne : j + 8 ≤ k ∨ k + 8 ≤ j) =>
    (show (sp - 80#64 + BitVec.ofNat 64 j).toNat + 8 ≤ (sp - 80#64 + BitVec.ofNat 64 k).toNat ∨
        (sp - 80#64 + BitVec.ofNat 64 k).toNat + 8 ≤ (sp - 80#64 + BitVec.ofNat 64 j).toNat by
      rw [off80 j (by omega), off80 k (by omega)]; omega)
  have later := fun (k : Nat) (hk : k ≤ 72) (ks : List Nat) (hks : ∀ j ∈ ks, j ≤ 72 ∧ (j + 8 ≤ k ∨ k + 8 ≤ j)) =>
    (show ∀ j ∈ ks, (sp - 80#64 + BitVec.ofNat 64 k).toNat + 8 ≤ (sp - 80#64 + BitVec.ofNat 64 j).toNat ∨
        (sp - 80#64 + BitVec.ofNat 64 j).toNat + 8 ≤ (sp - 80#64 + BitVec.ofNat 64 k).toNat from
      fun j hj => apart k j hk (hks j hj).1 (hks j hj).2.symm)
  have raBack := back 5 72 (by decide) ra rfl ⟨apart 72 56 (by decide) (by decide) (by decide), trivial⟩
  have s0Back := back 0 64 (by decide) (R0 8) rfl
    (by have a := later 64 (by decide) [48, 40, 32, 24, 72, 56] (by decide)
        exact ⟨a 48 (by simp), a 40 (by simp), a 32 (by simp), a 24 (by simp), a 72 (by simp), a 56 (by simp), trivial⟩)
  have s2Back := back 1 48 (by decide) (R0 18) rfl
    (by have a := later 48 (by decide) [40, 32, 24, 72, 56] (by decide)
        exact ⟨a 40 (by simp), a 32 (by simp), a 24 (by simp), a 72 (by simp), a 56 (by simp), trivial⟩)
  have s3Back := back 2 40 (by decide) (R0 19) rfl
    (by have a := later 40 (by decide) [32, 24, 72, 56] (by decide)
        exact ⟨a 32 (by simp), a 24 (by simp), a 72 (by simp), a 56 (by simp), trivial⟩)
  have s4Back := back 3 32 (by decide) (R0 20) rfl
    (by have a := later 32 (by decide) [24, 72, 56] (by decide)
        exact ⟨a 24 (by simp), a 72 (by simp), a 56 (by simp), trivial⟩)
  have s5Back := back 4 24 (by decide) (R0 21) rfl
    (by have a := later 24 (by decide) [72, 56] (by decide) ; exact ⟨a 72 (by simp), a 56 (by simp), trivial⟩)
  have s1Back := back 6 56 (by decide) (R0 9) rfl trivial
  obtain ⟨d13, run13, p13⟩ := (Flush.FlushPartial.epi_fast d12 ra R12
    ⟨p12.good, p12.image, p12.minstret, link12, by simp only [R12, ↓reduceIte]; decide, p12.tick⟩
    ⟨(keep12 2 (by decide) (by decide) (by decide)).trans ((keep11 2 (by decide) (by decide) (by decide)).trans
      ((keep10 2 (by decide) (by decide) (by decide)).trans p9.stack)),
     (gholds_lookup _ p12.regs rfl).trans (congrArg some newCurr),
     (keep12 18 (by decide) (by decide) (by decide)).trans ((keep11 18 (by decide) (by decide) (by decide)).trans
      ((keep10 18 (by decide) (by decide) (by decide)).trans buf9)), True.intro⟩
    (L.slots 72 (by simp)).read (L.slots 64 (by simp)).read (L.slots 56 (by simp)).read (L.slots 48 (by simp)).read
    (L.slots 40 (by simp)).read (L.slots 32 (by simp)).read (L.slots 24 (by simp)).read raBack h.aligned).run
    d12 ⟨p12.pc, rfl⟩
  have restore : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr c n = some (R0 n) := fun n hn => by
    have := present n hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact this
  have load := fun (n k : Nat) (v : BitVec 64)
      (l : gpr d13 n = some (bytesVal .ld (read8 d12.σ.mem (sp - 80#64 + BitVec.ofNat 64 k).toNat)))
      (b : bytesVal .ld (read8 d12.σ.mem (sp - 80#64 + BitVec.ofNat 64 k).toNat) = v) =>
    (show gpr d13 n = some v by rw [l, b])
  have out8 : Vsa.Machine.output d8.σ = Vsa.Machine.output c.σ := by
    unfold Vsa.Machine.output
    rw [q8.output, p7.output, p6.output, p5.output, p4.output, q3.output, p2.output, p1.output]
  have mem13 : d13.σ.mem = d12.σ.mem := by rw [p13.memory]; rfl
  refine ⟨d13, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
    (run9.trans (run10.trans (run11.trans (run12.trans run13))))))))))),
    p13.good, p13.image, p13.minstret, p13.tick,
    p13.toEffectPost.htifIdle (p12.toEffectPost.htifIdle (p11.toEffectPost.htifIdle (p10.toEffectPost.htifIdle p9.idle))),
    p13.pc, load 1 72 ra (gholds_lookup _ p13.regs rfl) raBack, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have l : gpr d13 10 = some (compareValue true (R12 18 - R12 10) 1#64) := gholds_lookup _ p13.regs rfl
    rw [l]; exact congrArg some (seqz_same _)
  · have l : gpr d13 2 = some (R12 2 + 80#64) := gholds_lookup _ p13.regs rfl
    rw [l]; simp only [R12, ↓reduceIte, Nat.reduceEqDiff, BitVec.sub_add_cancel]
  · intro n hn
    rw [restore n hn]
    have hn' := hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn'
    rcases hn' with rfl | rfl | rfl | rfl | rfl | rfl | hn'
    · exact load 8 64 _ (gholds_lookup _ p13.regs rfl) s0Back
    · exact load 9 56 _ (gholds_lookup _ p13.regs rfl) s1Back
    · exact load 18 48 _ (gholds_lookup _ p13.regs rfl) s2Back
    · exact load 19 40 _ (gholds_lookup _ p13.regs rfl) s3Back
    · exact load 20 32 _ (gholds_lookup _ p13.regs rfl) s4Back
    · exact load 21 24 _ (gholds_lookup _ p13.regs rfl) s5Back
    · have far : 22 ≤ n ∧ n ≤ 27 := by omega
      have mid : gpr d9 n = gpr d8 n := by
        by_cases small : n ≤ 23
        · exact p9.saved n (by simp; omega)
        · exact p9.rest n (by simp; omega)
      rw [p13.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega),
        keep12 n (by omega) (by omega) (by omega), keep11 n (by omega) (by omega) (by omega),
        keep10 n (by omega) (by omega) (by omega), mid, k8 n (by omega) (by omega) (by simp; omega),
        p1.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega)]
      exact restore n hn
  · have o9 := p9.output
    unfold Vsa.Machine.output at *
    rw [p13.output, p12.output, p11.output, p10.output, o9, out8]
  · rw [mem13, mem12, read8_value]
    have w := Gc.word_writeLog_at (writeLog d9.σ.mem
      (Flush.FlushPartial.adjustLog R10 (Flush.FlushPartial.adjust_loads d10.σ.mem R10)))
      (Flush.FlushPartial.shiftLog R11 (Flush.FlushPartial.shift_loads d11.σ.mem R11)) 0 (ch + 24#64).toNat _ rfl trivial
    exact w.trans newCurr
  · rw [mem13, mem12, read8_outside shWithin (by rw [chOff 8 (by decide)]; omega), read8_value]
    have w := Gc.word_writeLog_at d9.σ.mem
      (Flush.FlushPartial.adjustLog R10 (Flush.FlushPartial.adjust_loads d10.σ.mem R10)) 0 (ch + 8#64).toNat _ rfl trivial
    refine w.trans ?_
    show bytesVal .ld (read8 d10.σ.mem (ch + 8#64).toNat) + len = off + len
    rw [p10.memory, show writeLog d9.σ.mem [] = d9.σ.mem from rfl, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      chanRead 8 (by decide), h.offset]
  · intro x s e r o k
    rw [mem13, mem12, writeLog_out _ _ _ (shWithin.outL (by omega)), writeLog_out _ _ _ (adjWithin.outL (by omega)),
      frame9 x (by omega) e r, mem1, writeLog_out _ _ _ (within.outL (by omega))]

end OCaml.Vm.Primitives.ConsoleWrite
