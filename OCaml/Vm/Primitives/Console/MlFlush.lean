import OCaml.Vm.Primitives.Console.Flush
import OCaml.Vm.Primitives.GprsKept
import OCaml.Vm.Primitives.Flush.MlFlush

/-! `caml_ml_flush(vchannel)` on a console output channel with a nonempty
buffer: register the local root, take no channel lock (the hooks are null),
`caml_flush_partial` once (the whole buffer is written), restore the local
roots and return `Val_unit`. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable
open ExitPath (LogWithin LogWithin.outL LogWithin.outLRange)
open FdWrite (errnoGlobal impurePtr enterHook leaveHook pendingSignals)

/-- `Caml_state`, `caml_channel_mutex_lock`, `caml_channel_mutex_unlock`. -/
def camlStateGlobal : BitVec 64 := 0x80064d08#64
def channelLock : BitVec 64 := 0x80064b58#64
def channelUnlock : BitVec 64 := 0x80064b50#64

theorem outLRange_of_each {log : List WEntry} {x n : Nat}
    (h : ∀ e ∈ log, x + n ≤ e.1 ∨ e.1 + e.2.1 ≤ x) : OutLRange log x n := by
  induction log with
  | nil => trivial
  | cons e rest ih =>
    exact ⟨h e (List.mem_cons_self ..), ih fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

theorem outL_of_each {log : List WEntry} {x : Nat}
    (h : ∀ e ∈ log, x < e.1 ∨ e.1 + e.2.1 ≤ x) : OutL log x := by
  induction log with
  | nil => trivial
  | cons e rest ih =>
    exact ⟨h e (List.mem_cons_self ..), ih fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

/-- A word `a` apart from the native stack, the two errno words, the channel
header and the local-roots word. -/
structure WordApart (sp ch rp dom : BitVec 64) (a : Nat) : Prop where
  stack : a + 8 ≤ sp.toNat - 384 ∨ sp.toNat ≤ a
  errno : a + 8 ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ a
  reent : a + 8 ≤ rp.toNat ∨ rp.toNat + 4 ≤ a
  chan : a + 8 ≤ ch.toNat ∨ ch.toNat + 72 ≤ a
  roots : a + 8 ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ a

/-- `caml_ml_flush`'s 112-byte frame above `caml_flush_partial`'s stack, the
domain's `local_roots` word, the channel custom block's pointer word and the
runtime globals it reads, apart from each other and from everything the
flush writes. -/
structure MlFlushLayout (sp v ch fd rp dom : BitVec 64) (len : Nat) : Prop where
  slots : ∀ k ∈ [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104],
    WriteWindow (sp - 112#64 + BitVec.ofNat 64 k) 8
  floor : 0x80000000 + 384 ≤ sp.toNat
  top : sp.toNat ≤ 0x100000000
  text : Image.textBase + Image.textSize ≤ sp.toNat - 112 ∨ sp.toNat ≤ Image.textBase
  rodata : Image.rodataBase + Image.rodataSize ≤ sp.toNat - 112 ∨ sp.toNat ≤ Image.rodataBase
  roots : WriteWindow (dom + 288#64) 8
  rootsRam : dom.toNat + 296 ≤ 0x100000000
  rootsText : dom.toNat + 296 ≤ Image.textBase ∨ Image.textBase + Image.textSize ≤ dom.toNat + 288
  rootsRodata : dom.toNat + 296 ≤ Image.rodataBase ∨ Image.rodataBase + Image.rodataSize ≤ dom.toNat + 288
  /-- every word read or written apart from the native stack, the two errno
  words, the channel header and the local-roots word -/
  rootsApart : (dom.toNat + 296 ≤ sp.toNat - 384 ∨ sp.toNat ≤ dom.toNat + 288) ∧
    (dom.toNat + 296 ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ dom.toNat + 288) ∧
    (dom.toNat + 296 ≤ rp.toNat ∨ rp.toNat + 4 ≤ dom.toNat + 288) ∧
    (dom.toNat + 296 ≤ ch.toNat ∨ ch.toNat + 72 ≤ dom.toNat + 288)
  apart : ∀ a ∈ [camlStateGlobal.toNat, channelLock.toNat, channelUnlock.toNat, (v + 8#64).toNat],
    WordApart sp ch rp dom a
  valWindow : ReadWindow (v + 8#64) 8
  errnoFrame : errnoGlobal.toNat + 4 ≤ sp.toNat - 112 ∨ sp.toNat ≤ errnoGlobal.toNat
  rpFrame : rp.toNat + 4 ≤ sp.toNat - 112 ∨ sp.toNat ≤ rp.toNat
  reads : ∀ x, FlushReads ch fd len x → (x < sp.toNat - 112 ∨ sp.toNat ≤ x) ∧
    (x < (dom + 288#64).toNat ∨ (dom + 288#64).toNat + 8 ≤ x)

structure MlFlushInput (ra sp v ch fd rp off dom lr : BitVec 64) (bs : List UInt8) (c : Config) : Prop
    extends LeafInput ra c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], (gprGet c.σ n).isSome
  stack : gpr c 2 = some sp
  valReg : gpr c 10 = some v
  flush : FlushMem (sp - 112#64) ch fd rp off bs c
  layout : MlFlushLayout sp v ch fd rp dom bs.length
  domWord : bytesVal .ld (read8 c.σ.mem camlStateGlobal.toNat) = dom
  rootsWord : bytesVal .ld (read8 c.σ.mem (dom + 288#64).toNat) = lr
  chanPtr : bytesVal .ld (read8 c.σ.mem (v + 8#64).toNat) = ch
  lockNull : bytesVal .ld (read8 c.σ.mem channelLock.toNat) = 0#64
  unlockNull : bytesVal .ld (read8 c.σ.mem channelUnlock.toNat) = 0#64

/-- A word read after the prologue misses its frame and the local-roots word. -/
def ProMiss (sp dom a : Nat) : Prop := (a + 8 ≤ sp - 112 ∨ sp ≤ a) ∧ (a + 8 ≤ dom + 288 ∨ dom + 296 ≤ a)

/-- What `caml_ml_flush`'s prologue and epilogue touch: the 112-byte frame,
the domain's `local_roots` word, `Caml_state`, the channel custom block's
pointer word and the channel's fd word, apart from the frame and the
local-roots word. -/
structure MlFlushFrame (sp v ch dom : BitVec 64) : Prop where
  slots : ∀ k ∈ [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104],
    WriteWindow (sp - 112#64 + BitVec.ofNat 64 k) 8
  floor : 0x80000000 + 384 ≤ sp.toNat
  top : sp.toNat ≤ 0x100000000
  text : Image.textBase + Image.textSize ≤ sp.toNat - 112 ∨ sp.toNat ≤ Image.textBase
  rodata : Image.rodataBase + Image.rodataSize ≤ sp.toNat - 112 ∨ sp.toNat ≤ Image.rodataBase
  roots : WriteWindow (dom + 288#64) 8
  rootsRam : dom.toNat + 296 ≤ 0x100000000
  rootsText : dom.toNat + 296 ≤ Image.textBase ∨ Image.textBase + Image.textSize ≤ dom.toNat + 288
  rootsRodata : dom.toNat + 296 ≤ Image.rodataBase ∨ Image.rodataBase + Image.rodataSize ≤ dom.toNat + 288
  rootsStack : dom.toNat + 296 ≤ sp.toNat - 112 ∨ sp.toNat ≤ dom.toNat + 288
  stateMiss : ProMiss sp.toNat dom.toNat camlStateGlobal.toNat
  valMiss : ProMiss sp.toNat dom.toNat (v + 8#64).toNat
  valWindow : ReadWindow (v + 8#64) 8
  fdWindow : ReadWindow ch 4
  fdMiss : (ch.toNat + 4 ≤ sp.toNat - 112 ∨ sp.toNat ≤ ch.toNat) ∧
    (ch.toNat + 4 ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ ch.toNat)

/-- `caml_ml_flush`'s entry, open or closed channel. -/
structure MlFlushEntry (ra sp v ch dom lr : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], (gprGet c.σ n).isSome
  stack : gpr c 2 = some sp
  valReg : gpr c 10 = some v
  frame : MlFlushFrame sp v ch dom
  domWord : bytesVal .ld (read8 c.σ.mem camlStateGlobal.toNat) = dom
  rootsWord : bytesVal .ld (read8 c.σ.mem (dom + 288#64).toNat) = lr
  chanPtr : bytesVal .ld (read8 c.σ.mem (v + 8#64).toNat) = ch

theorem WordApart.proMiss {sp ch rp dom : BitVec 64} {a : Nat} (h : WordApart sp ch rp dom a)
    (floor : 384 ≤ sp.toNat) : ProMiss sp.toNat dom.toNat a :=
  ⟨by have := h.stack; omega, h.roots⟩

/-- The open-channel input gives the entry. -/
theorem MlFlushInput.entry {ra sp v ch fd rp off dom lr bs c} (h : MlFlushInput ra sp v ch fd rp off dom lr bs c) :
    MlFlushEntry ra sp v ch dom lr c := by
  have L := h.layout
  have floor := L.floor
  have rootsRam := L.rootsRam
  have chRam := h.flush.layout.chanRam
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have a := L.reads ch.toNat (Or.inl ⟨Nat.le_refl _, by omega⟩)
  have b := L.reads (ch.toNat + 3) (Or.inl ⟨by omega, by omega⟩)
  rw [r288] at a b
  have ra' := L.rootsApart.1
  exact { h with
    frame := { L with
      rootsStack := by omega
      stateMiss := (L.apart _ (by simp)).proMiss (by omega)
      valMiss := (L.apart _ (by simp)).proMiss (by omega)
      fdWindow := h.flush.layout.fdWindow
      fdMiss := ⟨by omega, by omega⟩ } }

theorem MlFlushInput.fdOpen {ra sp v ch fd rp off dom lr bs c} (h : MlFlushInput ra sp v ch fd rp off dom lr bs c) :
    guardB .BEQ (bytesVal .lw (read8 c.σ.mem ch.toNat)) 18446744073709551615#64 = false := by
  rw [h.flush.fdWord]
  have := h.flush.descriptor.range
  simp only [guardB, beq_eq_false_iff_ne, ne_eq]
  intro e; rw [e] at this; simp at this

/-- Return from `caml_ml_flush`: `Val_unit`, the buffer on the console, the
channel's `curr` reset and `offset` advanced, `local_roots` restored; only
the native stack, the errno words, the two channel words and the
local-roots word were written. -/
structure MlFlushPost (ra sp ch rp off dom lr : BitVec 64) (bs : List UInt8) (c d : Config) : Prop where
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
  roots : bytesVal .ld (read8 d.σ.mem (dom + 288#64).toNat) = lr
  frame : ∀ x, (x < sp.toNat - 384 ∨ sp.toNat ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
    (x < rp.toNat ∨ rp.toNat + 4 ≤ x) → (x < ch.toNat + 8 ∨ ch.toNat + 16 ≤ x) →
    (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  gprs : GprsKept c d

/-- `caml_ml_flush` after its prologue: the frame saved, the local root
registered, the channel and its fd loaded; `t` is the lock block (open
channel) or the epilogue (`fd == -1`). -/
structure MlFlushPro (ra sp v ch dom lr t : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ w, d.σ.regs.get? Register.minstret = some w
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some t
  raReg : gpr d 1 = some ra
  stack : gpr d 2 = some (sp - 112#64)
  chReg : gpr d 8 = some ch
  lrReg : gpr d 9 = some lr
  valReg : gpr d 10 = some v
  globalReg : gpr d 18 = some 0x80064d08#64
  domReg : gpr d 15 = some dom
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [2, 8, 9, 12, 13, 14, 15, 18] → gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ
  outside : ∀ x, (x < sp.toNat - 112 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  savedRa : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 104).toNat) = ra
  savedS0 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 96).toNat) = (gpr c 8).getD 0
  savedS1 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 88).toNat) = (gpr c 9).getD 0
  savedS2 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 80).toNat) = (gpr c 18).getD 0
  gprs : GprsKept c d

theorem ml_flush_pro_gen {ra sp v ch dom lr c} (h : MlFlushEntry ra sp v ch dom lr c)
    (entry : pcOf c = some 0x80016238#64) (closed : Bool)
    (fd : guardB .BEQ (bytesVal .lw (read8 c.σ.mem ch.toNat)) 18446744073709551615#64 = closed) :
    ∃ d, Steps c d ∧ MlFlushPro ra sp v ch dom lr (if closed then 0x800162c8#64 else 0x80016290#64) c d := by
  have L := h.frame
  have present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr c n = some ((gpr c n).getD 0) := by
    intro n hn
    have := h.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  have floor := L.floor
  have off112 : ∀ k, k ≤ 112 → (sp - 112#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 112 + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  have sp112 : (sp - 112#64).toNat = sp.toNat - 112 := by
    rw [BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  have rootsRam := L.rootsRam
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have dw : bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) = dom := h.domWord
  -- prologue: the frame, the local root, the channel and its fd
  let R0 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else if n = 10 then v else
    (gpr c n).getD 0
  have proIn : ∀ e ∈ Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0),
      (sp.toNat - 112 ≤ e.1 ∧ e.1 + e.2.1 ≤ sp.toNat) ∨ (e.1 = dom.toNat + 288 ∧ e.2.1 = 8) := by
    intro e he
    simp only [Flush.MlFlush.proLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (left; simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; rw [off112 _ (by decide)]; omega)
      | (right; simp only [Flush.MlFlush.pro_loads, List.getD_cons_zero]; rw [dw, r288]; simp)
  have outside0 : ∀ x, (x < sp.toNat - 112 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
      OutL (Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0)) x :=
    fun x a b => outL_of_each fun e he => by rcases proIn e he with ⟨l, u⟩ | ⟨l, u⟩ <;> omega
  have range0 : ∀ x n j, (x + n ≤ sp.toNat - 112 ∨ sp.toNat ≤ x) → (x + n ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
      OutLRange ((Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0)).take j) x n :=
    fun x n j a b => outLRange_of_each fun e he => by
      rcases proIn e (List.mem_of_mem_take he) with ⟨l, u⟩ | ⟨l, u⟩ <;> omega
  have frame4 : ∀ x n, (x + n ≤ sp.toNat - 112 ∨ sp.toNat ≤ x) →
      OutLRange ((Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0)).take 4) x n :=
    fun x n a => outLRange_of_each fun e he => by
      simp only [Flush.MlFlush.proLog, List.take, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;>
        (simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; rw [off112 _ (by decide)]; omega)
  have slot := fun k (hk : k ∈ [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104]) => L.slots k hk
  have st := L.stateMiss
  have va := L.valMiss
  have fm := L.fdMiss
  have rs := L.rootsStack
  have cs : camlStateGlobal.toNat = 2147896584 := by decide
  rw [cs] at st
  clear cs
  have ok0 : guardB .BEQ (bytesVal .lw ((Flush.MlFlush.pro_loads c.σ.mem R0).getD 3 [])) 18446744073709551615#64 = closed := by
    show guardB .BEQ (bytesVal .lw (read8 c.σ.mem (bytesVal .ld (read8 c.σ.mem (v + 8#64).toNat)).toNat))
      18446744073709551615#64 = closed
    rw [h.chanPtr]; exact fd
  have fdApart : OutLRange ((Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0)).take 10) ch.toNat 4 :=
    range0 _ _ _ fm.1 fm.2
  have a4 : OutLRange ((Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0)).take 4) (0x80064d08#64).toNat 8 := by
    rw [show (0x80064d08#64 : BitVec 64).toNat = 2147896584 by decide]
    exact frame4 _ _ st.1
  have w5 : ReadWindow (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64) 8 := by
    rw [dw]; exact L.roots.read
  have a5 : OutLRange ((Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0)).take 4)
      (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64).toNat 8 := by
    rw [dw, r288]; exact frame4 _ _ rs
  have w10 : WriteWindow (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64) 8 := by
    rw [dw]; exact L.roots
  have a12 : OutLRange ((Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0)).take 10) (v + 8#64).toNat 8 :=
    range0 _ _ _ va.1 va.2
  have w13 : ReadWindow (bytesVal .ld (read8 c.σ.mem (v + 8#64).toNat)) 4 := by
    rw [h.chanPtr]; exact L.fdWindow
  have a13 : OutLRange ((Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0)).take 10)
      (bytesVal .ld (read8 c.σ.mem (v + 8#64).toNat)).toNat 4 := by
    rw [h.chanPtr]; exact fdApart
  have image0 : ImageOutside (Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0)) :=
    ⟨outLRange_of_each fun e he => by have := L.text; have := L.rootsText; rcases proIn e he with ⟨l, u⟩ | ⟨l, u⟩ <;> omega,
     outLRange_of_each fun e he => by have := L.rodata; have := L.rootsRodata; rcases proIn e he with ⟨l, u⟩ | ⟨l, u⟩ <;> omega⟩
  have regs0 : GHolds c.σ (Flush.MlFlush.pro_input R0) :=
    ⟨h.raReg, h.stack, present 8 (by simp), present 9 (by simp), h.valReg, present 18 (by simp), True.intro⟩
  obtain ⟨d1, run1, p1⟩ : ∃ d1, Steps c d1 ∧ WriteRegistersPost [2, 8, 9, 12, 13, 14, 15, 18]
      (Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0)) c
      (if closed then 0x800162c8#64 else 0x80016290#64) (R0 10)
      (Flush.MlFlush.pro_regs R0 (Flush.MlFlush.pro_loads c.σ.mem R0)) d1 := by
    cases closed
    · exact (Flush.MlFlush.pro_fast c R0 h.toLeafInput regs0
        (slot 80 (by simp)) (slot 104 (by simp)) (slot 96 (by simp)) (slot 88 (by simp)) a4 w5 a5
        (slot 32 (by simp)) (slot 24 (by simp)) (slot 8 (by simp)) (slot 16 (by simp)) w10 (slot 40 (by simp))
        L.valWindow a12 w13 a13 image0 ok0).run c ⟨entry, rfl⟩
    · exact (Flush.MlFlush.closed_fast c R0 h.toLeafInput regs0
        (slot 80 (by simp)) (slot 104 (by simp)) (slot 96 (by simp)) (slot 88 (by simp)) a4 w5 a5
        (slot 32 (by simp)) (slot 24 (by simp)) (slot 8 (by simp)) (slot 16 (by simp)) w10 (slot 40 (by simp))
        L.valWindow a12 w13 a13 image0 ok0).run c ⟨entry, rfl⟩
  have mem1 : d1.σ.mem = writeLog c.σ.mem (Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0)) := p1.memory
  have same1 : ∀ x, (x < sp.toNat - 112 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
      (d1.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := fun x a b => by rw [mem1, writeLog_out _ _ _ (outside0 x a b)]
  have read1 : ∀ a, (a + 8 ≤ sp.toNat - 112 ∨ sp.toNat ≤ a) → (a + 8 ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ a) →
      read8 d1.σ.mem a = read8 c.σ.mem a := fun a x y => read8_same fun i hi => same1 _ (by omega) (by omega)
  have ch1 : gpr d1 8 = some ch := by
    have l : gpr d1 8 = some (bytesVal .ld (read8 c.σ.mem (v + 8#64).toNat)) := gholds_lookup _ p1.regs rfl
    rw [l, h.chanPtr]
  have lr1 : gpr d1 9 = some lr := by
    have l : gpr d1 9 = some (bytesVal .ld (read8 c.σ.mem (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) +
      288#64).toNat)) := gholds_lookup _ p1.regs rfl
    rw [l, dw, h.rootsWord]
  have ra1 : gpr d1 1 = some ra := gholds_lookup _ p1.regs rfl
  have dom1 : gpr d1 15 = some dom := by
    have l : gpr d1 15 = some (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat)) := gholds_lookup _ p1.regs rfl
    rw [l, dw]
  -- the frame reads back from the prologue's log
  have back := fun (i k : Nat) (hk : k ≤ 104) (w : BitVec 64)
      (sel : (Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0))[i]? = some ((sp - 112#64 + BitVec.ofNat 64 k).toNat, 8, w))
      (after : OutLRange ((Flush.MlFlush.proLog R0 (Flush.MlFlush.pro_loads c.σ.mem R0)).drop (i + 1))
        (sp - 112#64 + BitVec.ofNat 64 k).toNat 8) =>
    (show bytesVal .ld (read8 d1.σ.mem (sp - 112#64 + BitVec.ofNat 64 k).toNat) = w by
      rw [mem1, read8_value]
      exact Gc.word_writeLog_at _ _ i _ _ sel after)
  have apart := fun (j k : Nat) (hj : j ≤ 104) (hk : k ≤ 104) (ne : j + 8 ≤ k ∨ k + 8 ≤ j) =>
    (show (sp - 112#64 + BitVec.ofNat 64 j).toNat + 8 ≤ (sp - 112#64 + BitVec.ofNat 64 k).toNat ∨
        (sp - 112#64 + BitVec.ofNat 64 k).toNat + 8 ≤ (sp - 112#64 + BitVec.ofNat 64 j).toNat by
      rw [off112 j (by omega), off112 k (by omega)]; omega)
  have domLater := fun (k : Nat) (hk : k ≤ 104) =>
    (show (sp - 112#64 + BitVec.ofNat 64 k).toNat + 8 ≤ (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64).toNat ∨
        (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64).toNat + 8 ≤ (sp - 112#64 + BitVec.ofNat 64 k).toNat by
      rw [dw, r288, off112 k (by omega)]; omega)
  have s2Back := back 0 80 (by decide) (R0 18) rfl
    ⟨apart 80 104 (by decide) (by decide) (by decide), apart 80 96 (by decide) (by decide) (by decide),
     apart 80 88 (by decide) (by decide) (by decide), apart 80 32 (by decide) (by decide) (by decide),
     apart 80 24 (by decide) (by decide) (by decide), apart 80 8 (by decide) (by decide) (by decide),
     apart 80 16 (by decide) (by decide) (by decide), domLater 80 (by decide),
     apart 80 40 (by decide) (by decide) (by decide), trivial⟩
  have raBack := back 1 104 (by decide) ra rfl
    ⟨apart 104 96 (by decide) (by decide) (by decide), apart 104 88 (by decide) (by decide) (by decide),
     apart 104 32 (by decide) (by decide) (by decide), apart 104 24 (by decide) (by decide) (by decide),
     apart 104 8 (by decide) (by decide) (by decide), apart 104 16 (by decide) (by decide) (by decide),
     domLater 104 (by decide), apart 104 40 (by decide) (by decide) (by decide), trivial⟩
  have s0Back := back 2 96 (by decide) (R0 8) rfl
    ⟨apart 96 88 (by decide) (by decide) (by decide), apart 96 32 (by decide) (by decide) (by decide),
     apart 96 24 (by decide) (by decide) (by decide), apart 96 8 (by decide) (by decide) (by decide),
     apart 96 16 (by decide) (by decide) (by decide), domLater 96 (by decide),
     apart 96 40 (by decide) (by decide) (by decide), trivial⟩
  have s1Back := back 3 88 (by decide) (R0 9) rfl
    ⟨apart 88 32 (by decide) (by decide) (by decide), apart 88 24 (by decide) (by decide) (by decide),
     apart 88 8 (by decide) (by decide) (by decide), apart 88 16 (by decide) (by decide) (by decide),
     domLater 88 (by decide), apart 88 40 (by decide) (by decide) (by decide), trivial⟩
  refine ⟨d1, run1, p1.good, p1.image, p1.minstret, p1.tick, p1.toEffectPost.htifIdle h.idle, p1.pc, ra1,
    gholds_lookup _ p1.regs rfl, ch1, lr1, gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, dom1,
    fun n lo hi hn => p1.toEffectPost.gpr_frame (by decide) n lo hi hn,
    by unfold Vsa.Machine.output; rw [p1.output], same1, raBack, ?_, ?_, ?_, GprsKept.of_pins p1 (by decide) (by decide) (by simp [keysG, Flush.MlFlush.pro_regs])⟩
  · rw [s0Back]; exact rfl
  · rw [s1Back]; exact rfl
  · rw [s2Back]; exact rfl

theorem ml_flush_pro {ra sp v ch fd rp off dom lr bs c} (h : MlFlushInput ra sp v ch fd rp off dom lr bs c)
    (entry : pcOf c = some 0x80016238#64) :
    ∃ d, Steps c d ∧ MlFlushPro ra sp v ch dom lr 0x80016290#64 c d :=
  ml_flush_pro_gen h.entry entry false h.fdOpen

/-- The call of `caml_flush_partial` inside `caml_ml_flush`: its input, the
saved frame words, and memory unchanged outside the frame and the
local-roots word. -/
structure MlFlushCall (ra sp ch fd rp off dom lr : BitVec 64) (bs : List UInt8) (c d : Config) : Prop where
  flush : FlushInput Flush.MlFlush.call_call.link (sp - 112#64) ch fd rp off bs d
  pc : pcOf d = some 0x80015408#64
  chReg : gpr d 8 = some ch
  lrReg : gpr d 9 = some lr
  globalReg : gpr d 18 = some 0x80064d08#64
  rest : ∀ n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ
  outside : ∀ x, (x < sp.toNat - 112 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  savedRa : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 104).toNat) = ra
  savedS0 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 96).toNat) = (gpr c 8).getD 0
  savedS1 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 88).toNat) = (gpr c 9).getD 0
  savedS2 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 80).toNat) = (gpr c 18).getD 0
  gprs : GprsKept c d

theorem ml_flush_enter {ra sp v ch fd rp off dom lr bs c} (h : MlFlushInput ra sp v ch fd rp off dom lr bs c)
    (entry : pcOf c = some 0x80016238#64) :
    ∃ d, Steps c d ∧ MlFlushCall ra sp ch fd rp off dom lr bs c d := by
  obtain ⟨d1, run1, P⟩ := ml_flush_pro h entry
  have L := h.layout
  have F := h.flush
  have present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr c n = some ((gpr c n).getD 0) := by
    intro n hn
    have := h.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  have floor := L.floor
  have rootsRam := L.rootsRam
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have rd := L.reads
  have lockAp := L.apart channelLock.toNat (by simp)
  have lk1 := lockAp.stack; have lk5 := lockAp.roots
  rw [show channelLock.toNat = 2147896152 by decide] at lk1 lk5
  clear lockAp
  have read1 : ∀ a, (a + 8 ≤ sp.toNat - 112 ∨ sp.toNat ≤ a) → (a + 8 ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ a) →
      read8 d1.σ.mem a = read8 c.σ.mem a := fun a x y => read8_same fun i hi => P.outside _ (by omega) (by omega)
  -- no channel lock
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 8 then ch else if n = 9 then lr else
    if n = 10 then v else 0x80064d08#64
  obtain ⟨d2, run2, p2⟩ := (Flush.MlFlush.lock_fast d1 R1 ⟨P.good, P.image, P.minstret, P.raReg, h.aligned, P.tick⟩
    ⟨P.raReg, P.chReg, P.lrReg, P.valReg, P.globalReg, True.intro⟩ (by
      show guardB .BEQ (bytesVal .ld (read8 d1.σ.mem (0x80064b58#64).toNat)) 0#64 = true
      rw [show (0x80064b58#64 : BitVec 64).toNat = 2147896152 by decide, read1 2147896152 (by omega) (by omega)]
      have := h.lockNull; simp only [channelLock] at this
      rw [show (0x80064b58#64 : BitVec 64).toNat = 2147896152 by decide] at this
      simp [guardB, this])).run d1 ⟨P.pc, rfl⟩
  have keep2 := fun n (hn : n ≠ 15) (lo : 1 ≤ n) (hi : n ≤ 31) =>
    p2.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn)
  obtain ⟨d3, run3, p3⟩ := (Flush.MlFlush.call_fast d2 R1
    ⟨p2.good, p2.image, p2.minstret, (keep2 1 (by decide) (by decide) (by decide)).trans P.raReg, h.aligned, p2.tick⟩
    ⟨(keep2 1 (by decide) (by decide) (by decide)).trans P.raReg, (keep2 8 (by decide) (by decide) (by decide)).trans P.chReg,
      (keep2 9 (by decide) (by decide) (by decide)).trans P.lrReg,
      (keep2 18 (by decide) (by decide) (by decide)).trans P.globalReg, True.intro⟩).run d2 ⟨p2.pc, rfl⟩
  have J3 := call_registers_summary Flush.MlFlush.call_call_shape Flush.MlFlush.call_call_decode d3
    (Flush.MlFlush.call_call_pins p3.image) p3.good p3.image p3.tick p3.minstret
    [(10, ch)] ⟨gholds_lookup _ p3.regs rfl, True.intro⟩
    (by change KeysOK [10]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  obtain ⟨d4, run4, q4⟩ := J3.run d3 ⟨p3.pc, rfl⟩
  have mem4 : d4.σ.mem = d1.σ.mem := by
    rw [q4.memory, p3.memory, show writeLog d2.σ.mem [] = d2.σ.mem from rfl, p2.memory]; rfl
  have k4 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 10, 15] → gpr d4 n = gpr d1 n := fun n lo hi hn => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    rw [q4.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p3.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega), keep2 n (by omega) lo hi]
  have isSome : ∀ {d : Config} {n : Nat} {w : BitVec 64}, gpr d n = some w → (gprGet d.σ n).isSome := by
    intro d n w e; change (gpr d n).isSome; rw [e]; rfl
  have rest4 : ∀ n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], gpr d4 n = gpr c n := by
    intro n hn
    have b := hn; simp only [List.mem_cons, List.mem_nil_iff, or_false] at b
    rw [k4 n (by omega) (by omega) (by simp; omega), P.kept n (by omega) (by omega) (by simp; omega)]
  have flushIn : FlushInput Flush.MlFlush.call_call.link (sp - 112#64) ch fd rp off bs d4 :=
    { F.transfer fun x hx => by
        have r := rd x hx; rw [r288] at r
        rw [mem4]; exact P.outside x r.1 r.2 with
      good := q4.good, image := q4.image, minstret := q4.minstret, raReg := gholds_lookup _ q4.regs rfl,
      aligned := by decide, tick := q4.tick
      idle := q4.toEffectPost.htifIdle (p3.toEffectPost.htifIdle (p2.toEffectPost.htifIdle P.idle))
      saved := by
        intro n hn
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
        rcases hn with rfl | rfl | rfl | hn
        · exact isSome ((k4 8 (by decide) (by decide) (by simp)).trans P.chReg)
        · exact isSome ((k4 9 (by decide) (by decide) (by simp)).trans P.lrReg)
        · exact isSome ((k4 18 (by decide) (by decide) (by simp)).trans P.globalReg)
        · exact isSome ((rest4 n (by simp; omega)).trans (present n (by simp; omega)))
      stack := (k4 2 (by decide) (by decide) (by simp)).trans P.stack
      chanReg := gholds_lookup _ q4.regs rfl }
  refine ⟨d4, run1.trans (run2.trans (run3.trans run4)), flushIn, q4.pc,
    (k4 8 (by decide) (by decide) (by simp)).trans P.chReg, (k4 9 (by decide) (by decide) (by simp)).trans P.lrReg,
    (k4 18 (by decide) (by decide) (by simp)).trans P.globalReg, rest4, ?_, ?_,
    by rw [mem4]; exact P.savedRa, by rw [mem4]; exact P.savedS0, by rw [mem4]; exact P.savedS1,
    by rw [mem4]; exact P.savedS2,
    P.gprs.trans ((GprsKept.of_pins p2 (by decide) (by decide) (by simp [keysG, Flush.MlFlush.lock_regs])).trans ((GprsKept.of_pins p3 (by decide) (by decide) (by simp [keysG, Flush.MlFlush.call_regs])).trans (GprsKept.of_pins q4 (by decide) (by decide) (by simp [keysG]))))⟩
  · have o := P.output
    unfold Vsa.Machine.output at *
    rw [q4.output, p3.output, p2.output, o]
  · intro x a b; rw [mem4]; exact P.outside x a b

/-- A word read after `caml_flush_partial` misses what the flush wrote: the
native stack below the frame, `errno`, the reentrancy errno word and the
channel header. -/
def FlushMiss (sp ch rp a : Nat) : Prop :=
  (a + 8 ≤ sp - 384 ∨ sp - 112 ≤ a) ∧ (a + 8 ≤ 2147896648 ∨ 2147896648 + 4 ≤ a) ∧
  (a + 8 ≤ rp ∨ rp + 4 ≤ a) ∧ (a + 8 ≤ ch ∨ ch + 72 ≤ a)

/-- The separation facts `caml_ml_flush`'s reads need, from its layout. -/
structure MlFlushSep (sp ch rp dom : Nat) : Prop where
  unlockFlush : FlushMiss sp ch rp 2147896144
  unlockPro : ProMiss sp dom 2147896144
  stateFlush : FlushMiss sp ch rp 2147896584
  statePro : ProMiss sp dom 2147896584
  frame : ∀ k, k ≤ 104 → FlushMiss sp ch rp (sp - 112 + k)
  footprint : ∀ x, (x < sp - 384 ∨ sp ≤ x) → (x < sp - 384 ∨ sp - 112 ≤ x) ∧ (x < sp - 112 ∨ sp ≤ x)

theorem MlFlushLayout.sep {sp v ch fd rp dom : BitVec 64} {len : Nat} (L : MlFlushLayout sp v ch fd rp dom len)
    (chanRam : ch.toNat + 72 ≤ 0x100000000) : MlFlushSep sp.toNat ch.toNat rp.toNat dom.toNat := by
  have floor := L.floor
  have rootsRam := L.rootsRam
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have chA := L.reads ch.toNat (Or.inl ⟨Nat.le_refl _, by omega⟩)
  have chB := L.reads (ch.toNat + 71) (Or.inl ⟨by omega, by omega⟩)
  rw [r288] at chA chB
  have errF := L.errnoFrame
  have rpF := L.rpFrame
  rw [show errnoGlobal.toNat = 2147896648 by decide] at errF
  have ul := L.apart channelUnlock.toNat (by simp)
  have st := L.apart camlStateGlobal.toNat (by simp)
  obtain ⟨u1, u2, u3, u4, u5⟩ := ul
  obtain ⟨s1, s2, s3, s4, s5⟩ := st
  rw [show channelUnlock.toNat = 2147896144 by decide] at u1 u2 u3 u4 u5
  rw [show camlStateGlobal.toNat = 2147896584 by decide] at s1 s2 s3 s4 s5
  rw [show errnoGlobal.toNat = 2147896648 by decide] at u2 s2
  exact ⟨⟨by omega, u2, u3, u4⟩, ⟨by omega, u5⟩, ⟨by omega, s2, s3, s4⟩, ⟨by omega, s5⟩,
    fun k hk => ⟨by omega, by omega, by omega, by omega⟩, fun x hx => ⟨by omega, by omega⟩⟩

/-- `caml_ml_flush` back from `caml_flush_partial`: the frame words, the
channel words, `Caml_state` and the unlock hook read as needed. -/
structure MlFlushWritten (ra sp ch rp off dom lr : BitVec 64) (bs : List UInt8) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ w, d.σ.regs.get? Register.minstret = some w
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some 0x800162ac#64
  chReg : gpr d 8 = some ch
  unlock : bytesVal .ld (read8 d.σ.mem 2147896144) = 0#64
  raReg : gpr d 1 = some Flush.MlFlush.call_call.link
  stack : gpr d 2 = some (sp - 112#64)
  lrReg : gpr d 9 = some lr
  result : gpr d 10 = some 1#64
  globalReg : gpr d 18 = some 0x80064d08#64
  rest : ∀ n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ ++ bytesToString bs
  domain : bytesVal .ld (read8 d.σ.mem 2147896584) = dom
  savedRa : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 104).toNat) = ra
  savedS0 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 96).toNat) = (gpr c 8).getD 0
  savedS1 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 88).toNat) = (gpr c 9).getD 0
  savedS2 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 80).toNat) = (gpr c 18).getD 0
  curr : bytesVal .ld (read8 d.σ.mem (ch + 24#64).toNat) = ch + 72#64
  offset : bytesVal .ld (read8 d.σ.mem (ch + 8#64).toNat) = off + BitVec.ofNat 64 bs.length
  frame : ∀ x, (x < sp.toNat - 384 ∨ sp.toNat ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
    (x < rp.toNat ∨ rp.toNat + 4 ≤ x) → (x < ch.toNat + 8 ∨ ch.toNat + 16 ≤ x) →
    (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  gprs : GprsKept c d

/-- `caml_ml_flush` after the flush and the (null) unlock: the frame words,
the channel words and `Caml_state` read as before the call. -/
structure MlFlushDone (ra sp ch rp off dom lr : BitVec 64) (bs : List UInt8) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ w, d.σ.regs.get? Register.minstret = some w
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some 0x800162c4#64
  raReg : gpr d 1 = some Flush.MlFlush.call_call.link
  stack : gpr d 2 = some (sp - 112#64)
  lrReg : gpr d 9 = some lr
  result : gpr d 10 = some 1#64
  globalReg : gpr d 18 = some 0x80064d08#64
  rest : ∀ n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ ++ bytesToString bs
  domain : bytesVal .ld (read8 d.σ.mem 2147896584) = dom
  savedRa : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 104).toNat) = ra
  savedS0 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 96).toNat) = (gpr c 8).getD 0
  savedS1 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 88).toNat) = (gpr c 9).getD 0
  savedS2 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 80).toNat) = (gpr c 18).getD 0
  curr : bytesVal .ld (read8 d.σ.mem (ch + 24#64).toNat) = ch + 72#64
  offset : bytesVal .ld (read8 d.σ.mem (ch + 8#64).toNat) = off + BitVec.ofNat 64 bs.length
  frame : ∀ x, (x < sp.toNat - 384 ∨ sp.toNat ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
    (x < rp.toNat ∨ rp.toNat + 4 ≤ x) → (x < ch.toNat + 8 ∨ ch.toNat + 16 ≤ x) →
    (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  gprs : GprsKept c d

theorem ml_flush_written {ra sp v ch fd rp off dom lr bs c} (h : MlFlushInput ra sp v ch fd rp off dom lr bs c)
    (entry : pcOf c = some 0x80016238#64) :
    ∃ d, Steps c d ∧ MlFlushWritten ra sp ch rp off dom lr bs c d := by
  obtain ⟨d4, run4, M⟩ := ml_flush_enter h entry
  have S := h.layout.sep h.flush.layout.chanRam
  have floor := h.layout.floor
  have off112 : ∀ k, k ≤ 112 → (sp - 112#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 112 + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  have sp112 : (sp - 112#64).toNat = sp.toNat - 112 := by
    rw [BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  have dw : bytesVal .ld (read8 c.σ.mem 2147896584) = dom := by
    have := h.domWord; simp only [camlStateGlobal] at this
    rwa [show (0x80064d08#64 : BitVec 64).toNat = 2147896584 by decide] at this
  -- caml_flush_partial
  obtain ⟨d5, run5, f5⟩ := flush_partial M.flush M.pc
  have read5 : ∀ a, FlushMiss sp.toNat ch.toNat rp.toNat a → read8 d5.σ.mem a = read8 d4.σ.mem a :=
    fun a ok => read8_same fun i hi => by
      obtain ⟨o1, o2, o3, o4⟩ := ok
      exact f5.frame _ (by rw [sp112, Nat.sub_sub]; omega)
        (by rw [show errnoGlobal.toNat = 2147896648 by decide]; omega) (by omega) (by omega) (by omega)
  have read4 : ∀ a, ProMiss sp.toNat dom.toNat a → read8 d4.σ.mem a = read8 c.σ.mem a :=
    fun a ok => read8_same fun i hi => by obtain ⟨o1, o2⟩ := ok; exact M.outside _ (by omega) (by omega)
  have frame5 : ∀ k, k ≤ 104 → read8 d5.σ.mem (sp - 112#64 + BitVec.ofNat 64 k).toNat =
      read8 d4.σ.mem (sp - 112#64 + BitVec.ofNat 64 k).toNat := by
    intro k hk; rw [off112 k (by omega)]; exact read5 _ (S.frame k hk)
  refine ⟨d5, run4.trans run5, f5.good, f5.image, f5.minstret, f5.tick, f5.idle, f5.pc,
    (f5.saved 8 (by simp)).trans M.chReg, ?_, f5.raReg, f5.stack, (f5.saved 9 (by simp)).trans M.lrReg, f5.result,
    (f5.saved 18 (by simp)).trans M.globalReg, ?_, ?_, ?_,
    by rw [frame5 104 (by decide)]; exact M.savedRa, by rw [frame5 96 (by decide)]; exact M.savedS0,
    by rw [frame5 88 (by decide)]; exact M.savedS1, by rw [frame5 80 (by decide)]; exact M.savedS2,
    f5.curr, f5.offset, ?_, M.gprs.trans f5.gprs⟩
  · rw [read5 _ S.unlockFlush, read4 _ S.unlockPro]
    have := h.unlockNull; simp only [channelUnlock] at this
    rwa [show (0x80064b50#64 : BitVec 64).toNat = 2147896144 by decide] at this
  · intro n hn
    rw [f5.saved n (by simp at hn ⊢; omega)]; exact M.rest n hn
  · have o := f5.output; have o4 := M.output
    unfold Vsa.Machine.output at *
    rw [o, o4]
  · rw [read5 _ S.stateFlush, read4 _ S.statePro, dw]
  · intro x a b r o k z
    have fp := S.footprint x a
    rw [f5.frame x (by rw [sp112, Nat.sub_sub]; omega) b r o k, M.outside x (by omega) z]

theorem ml_flush_flushed {ra sp v ch fd rp off dom lr bs c} (h : MlFlushInput ra sp v ch fd rp off dom lr bs c)
    (entry : pcOf c = some 0x80016238#64) :
    ∃ d, Steps c d ∧ MlFlushDone ra sp ch rp off dom lr bs c d := by
  obtain ⟨d5, run5, W⟩ := ml_flush_written h entry
  let R5 : Nat → BitVec 64 := fun n => if n = 1 then Flush.MlFlush.call_call.link else if n = 8 then ch else
    if n = 9 then lr else if n = 10 then 1#64 else 0x80064d08#64
  obtain ⟨d6, run6, p6⟩ := (Flush.MlFlush.done_fast d5 R5
    ⟨W.good, W.image, W.minstret, W.raReg, by simp only [R5, ↓reduceIte]; decide, W.tick⟩
    ⟨W.raReg, W.chReg, W.lrReg, W.result, W.globalReg, True.intro⟩ (by simp [R5, guardB])).run d5 ⟨W.pc, rfl⟩
  have keep6 := fun n (lo : 1 ≤ n) (hi : n ≤ 31) => p6.toEffectPost.gpr_frame (by decide) n lo hi (by simp)
  have mem6 : d6.σ.mem = d5.σ.mem := by rw [p6.memory]; rfl
  obtain ⟨d7, run7, p7⟩ := (Flush.MlFlush.unlock_fast d6 R5
    ⟨p6.good, p6.image, p6.minstret, (keep6 1 (by decide) (by decide)).trans W.raReg,
      by simp only [R5, ↓reduceIte]; decide, p6.tick⟩
    ⟨(keep6 1 (by decide) (by decide)).trans W.raReg, (keep6 8 (by decide) (by decide)).trans W.chReg,
      (keep6 9 (by decide) (by decide)).trans W.lrReg, (keep6 10 (by decide) (by decide)).trans W.result,
      (keep6 18 (by decide) (by decide)).trans W.globalReg, True.intro⟩
    (by
      show guardB .BEQ (bytesVal .ld (read8 d6.σ.mem (0x80064b50#64).toNat)) 0#64 = true
      rw [mem6, show (0x80064b50#64 : BitVec 64).toNat = 2147896144 by decide, W.unlock]
      simp [guardB])).run d6 ⟨p6.pc, rfl⟩
  have keep7 := fun n (hn : n ≠ 15) (lo : 1 ≤ n) (hi : n ≤ 31) =>
    p7.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn)
  have mem7 : d7.σ.mem = d5.σ.mem := by rw [p7.memory, mem6]; rfl
  refine ⟨d7, run5.trans (run6.trans run7), p7.good, p7.image, p7.minstret, p7.tick,
    p7.toEffectPost.htifIdle (p6.toEffectPost.htifIdle W.idle), p7.pc,
    (keep7 1 (by decide) (by decide) (by decide)).trans ((keep6 1 (by decide) (by decide)).trans W.raReg),
    (keep7 2 (by decide) (by decide) (by decide)).trans ((keep6 2 (by decide) (by decide)).trans W.stack),
    (keep7 9 (by decide) (by decide) (by decide)).trans ((keep6 9 (by decide) (by decide)).trans W.lrReg),
    (keep7 10 (by decide) (by decide) (by decide)).trans ((keep6 10 (by decide) (by decide)).trans W.result),
    (keep7 18 (by decide) (by decide) (by decide)).trans ((keep6 18 (by decide) (by decide)).trans W.globalReg),
    ?_, ?_, by rw [mem7]; exact W.domain, by rw [mem7]; exact W.savedRa, by rw [mem7]; exact W.savedS0,
    by rw [mem7]; exact W.savedS1, by rw [mem7]; exact W.savedS2, by rw [mem7]; exact W.curr,
    by rw [mem7]; exact W.offset, fun x a b r o k z => by rw [mem7]; exact W.frame x a b r o k z,
    W.gprs.trans ((GprsKept.of_pins p6 (by decide) (by decide) (by simp [keysG, Flush.MlFlush.done_regs])).trans (GprsKept.of_pins p7 (by decide) (by decide) (by simp [keysG, Flush.MlFlush.unlock_regs])))⟩
  · intro n hn
    have b := hn; simp only [List.mem_cons, List.mem_nil_iff, or_false] at b
    rw [keep7 n (by omega) (by omega) (by omega), keep6 n (by omega) (by omega)]
    exact W.rest n hn
  · have o := W.output
    unfold Vsa.Machine.output at *
    rw [p7.output, p6.output, o]

/-- `caml_ml_flush` at its epilogue (`0x800162c8`): `Caml_state` in `a5`, the
saved `local_roots` in `s1`, the frame words as the prologue saved them. -/
structure MlFlushTail (ra sp dom lr lk : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ w, d.σ.regs.get? Register.minstret = some w
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some 0x800162c8#64
  link : gpr d 1 = some lk
  linkAligned : lk.toNat % 4 = 0
  stack : gpr d 2 = some (sp - 112#64)
  lrReg : gpr d 9 = some lr
  domReg : gpr d 15 = some dom
  rest : ∀ n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], gpr d n = gpr c n
  savedRa : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 104).toNat) = ra
  savedS0 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 96).toNat) = (gpr c 8).getD 0
  savedS1 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 88).toNat) = (gpr c 9).getD 0
  savedS2 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 80).toNat) = (gpr c 18).getD 0
  gprs : GprsKept c d

/-- Return through `caml_ml_flush`'s epilogue: `Val_unit`, the saves restored,
`local_roots` restored, nothing else written. -/
structure MlFlushRet (ra sp dom lr : BitVec 64) (c d e : Config) : Prop where
  good : GoodState e.σ
  image : ExecutableImage e
  minstret : ∃ w, e.σ.regs.get? Register.minstret = some w
  tick : e.tick < 2
  idle : e.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf e = some ra
  raReg : gpr e 1 = some ra
  result : gpr e 10 = some 1#64
  stack : gpr e 2 = some sp
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr e n = gpr c n
  output : Vsa.Machine.output e.σ = Vsa.Machine.output d.σ
  roots : bytesVal .ld (read8 e.σ.mem (dom + 288#64).toNat) = lr
  frame : ∀ x, (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) → (e.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0
  gprs : GprsKept d e

theorem ml_flush_tail {ra sp v ch dom lr lk c d} (h : MlFlushEntry ra sp v ch dom lr c)
    (t : MlFlushTail ra sp dom lr lk c d) : ∃ e, Steps d e ∧ MlFlushRet ra sp dom lr c d e := by
  have L := h.frame
  have floor := L.floor
  have off112 : ∀ k, k ≤ 112 → (sp - 112#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 112 + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  have rootsRam := L.rootsRam
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have rs := L.rootsStack
  have present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr c n = some ((gpr c n).getD 0) := by
    intro n hn
    have := h.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  -- restore local_roots and the saves
  let R8 : Nat → BitVec 64 := fun n => if n = 1 then lk else
    if n = 2 then sp - 112#64 else if n = 9 then lr else dom
  have tlWithin : LogWithin (Flush.MlFlush.tailLog R8 []) (dom.toNat + 288) (dom.toNat + 296) := by
    intro e he
    simp only [Flush.MlFlush.tailLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he; simp only [R8, ↓reduceIte, Nat.reduceEqDiff]; rw [r288]; omega
  have readFrame : ∀ k, k ≤ 104 →
      read8 (writeLog d.σ.mem (Flush.MlFlush.tailLog R8 [])) (sp - 112#64 + BitVec.ofNat 64 k).toNat =
        read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 k).toNat := by
    intro k hk
    rw [read8_outside tlWithin (by rw [off112 k (by omega)]; omega)]
  have raBack : bytesVal .ld (read8 (writeLog d.σ.mem (Flush.MlFlush.tailLog R8 [])) (R8 2 + 104#64).toNat) = ra := by
    show bytesVal .ld (read8 (writeLog d.σ.mem (Flush.MlFlush.tailLog R8 [])) (sp - 112#64 + BitVec.ofNat 64 104).toNat) = ra
    rw [readFrame 104 (by decide)]; exact t.savedRa
  obtain ⟨e, run9, p9⟩ := (Flush.MlFlush.tail_fast d ra R8
    ⟨t.good, t.image, t.minstret, t.link, t.linkAligned, t.tick⟩ ⟨t.stack, t.lrReg, t.domReg, True.intro⟩
    L.roots (L.slots 104 (by simp)).read (L.slots 96 (by simp)).read (L.slots 88 (by simp)).read
    (L.slots 80 (by simp)).read
    ⟨tlWithin.outLRange (by have := L.rootsText; omega), tlWithin.outLRange (by have := L.rootsRodata; omega)⟩
    raBack h.aligned).run d ⟨t.pc, rfl⟩
  have mem9 : e.σ.mem = writeLog d.σ.mem (Flush.MlFlush.tailLog R8 []) := p9.memory
  have load := fun (n k : Nat) (hk : k ≤ 104) (w : BitVec 64)
      (l : gpr e n = some (bytesVal .ld (read8 (writeLog d.σ.mem (Flush.MlFlush.tailLog R8 []))
        (sp - 112#64 + BitVec.ofNat 64 k).toNat)))
      (b : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 k).toNat) = w) =>
    (show gpr e n = some w by rw [l, readFrame k hk, b])
  refine ⟨e, run9, p9.good, p9.image, p9.minstret, p9.tick, p9.toEffectPost.htifIdle t.idle, p9.pc,
    load 1 104 (by decide) ra (gholds_lookup _ p9.regs rfl) t.savedRa, gholds_lookup _ p9.regs rfl, ?_, ?_, ?_,
    ?_, ?_, GprsKept.of_pins p9 (by decide) (by decide) (by simp [keysG, Flush.MlFlush.tail_regs])⟩
  · have l : gpr e 2 = some (R8 2 + 112#64) := gholds_lookup _ p9.regs rfl
    rw [l]; simp only [R8, ↓reduceIte, Nat.reduceEqDiff, BitVec.sub_add_cancel]
  · intro n hn
    rw [present n hn]
    have hn' := hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn'
    rcases hn' with rfl | rfl | rfl | hn'
    · exact load 8 96 (by decide) _ (gholds_lookup _ p9.regs rfl) t.savedS0
    · exact load 9 88 (by decide) _ (gholds_lookup _ p9.regs rfl) t.savedS1
    · exact load 18 80 (by decide) _ (gholds_lookup _ p9.regs rfl) t.savedS2
    · rw [p9.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega), t.rest n (by simp; omega)]
      exact present n hn
  · unfold Vsa.Machine.output
    rw [p9.output]
  · rw [mem9, read8_value]
    exact Gc.word_writeLog_at d.σ.mem (Flush.MlFlush.tailLog R8 []) 0 (dom + 288#64).toNat lr rfl trivial
  · intro x hx
    rw [mem9, writeLog_out _ _ _ (tlWithin.outL (by omega))]

theorem ml_flush {ra sp v ch fd rp off dom lr bs c} (h : MlFlushInput ra sp v ch fd rp off dom lr bs c)
    (entry : pcOf c = some 0x80016238#64) :
    ∃ d, Steps c d ∧ MlFlushPost ra sp ch rp off dom lr bs c d := by
  obtain ⟨d7, run7, p7'⟩ := ml_flush_flushed h entry
  have L := h.layout
  have floor := L.floor
  have rootsRam := L.rootsRam
  have ra' := L.rootsApart
  -- reload Caml_state
  let R7 : Nat → BitVec 64 := fun n => if n = 1 then Flush.MlFlush.call_call.link else
    if n = 2 then sp - 112#64 else if n = 9 then lr else if n = 10 then 1#64 else 0x80064d08#64
  have sp7 := p7'.stack
  have link7 := p7'.raReg
  obtain ⟨d8, run8, p8⟩ := (Flush.MlFlush.ret_fast d7 R7
    ⟨p7'.good, p7'.image, p7'.minstret, link7, by simp only [R7, ↓reduceIte]; decide, p7'.tick⟩
    ⟨sp7, p7'.lrReg, p7'.result, p7'.globalReg, True.intro⟩
    (show ReadWindow (0x80064d08#64) 8 from ⟨by decide, by decide, Or.inr (by decide)⟩)).run d7 ⟨p7'.pc, rfl⟩
  have dom8 : gpr d8 15 = some dom := by
    have l : gpr d8 15 = some (bytesVal .ld (read8 d7.σ.mem (0x80064d08#64).toNat)) := gholds_lookup _ p8.regs rfl
    rw [l, show (0x80064d08#64 : BitVec 64).toNat = 2147896584 by decide]; exact congrArg some p7'.domain
  have keep8 := fun n (hn : n ≠ 15) (lo : 1 ≤ n) (hi : n ≤ 31) =>
    p8.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn)
  have mem8 : d8.σ.mem = d7.σ.mem := by rw [p8.memory]; rfl
  obtain ⟨e, run9, r⟩ := ml_flush_tail h.entry
    { good := p8.good, image := p8.image, minstret := p8.minstret, tick := p8.tick
      idle := p8.toEffectPost.htifIdle p7'.idle, pc := p8.pc
      link := (keep8 1 (by decide) (by decide) (by decide)).trans link7, linkAligned := by decide
      stack := (keep8 2 (by decide) (by decide) (by decide)).trans sp7
      lrReg := (keep8 9 (by decide) (by decide) (by decide)).trans p7'.lrReg
      domReg := dom8
      rest := fun n hn => by
        have b := hn; simp only [List.mem_cons, List.mem_nil_iff, or_false] at b
        rw [keep8 n (by omega) (by omega) (by omega)]; exact p7'.rest n hn
      savedRa := by rw [mem8]; exact p7'.savedRa
      savedS0 := by rw [mem8]; exact p7'.savedS0
      savedS1 := by rw [mem8]; exact p7'.savedS1
      savedS2 := by rw [mem8]; exact p7'.savedS2
      gprs := p7'.gprs.trans (GprsKept.of_pins p8 (by decide) (by decide) (by simp [keysG, Flush.MlFlush.ret_regs])) }
  have chApart := ra'.2.2.2
  have chRam := h.flush.layout.chanRam
  have chOff : ∀ k, k ≤ 72 → (ch + BitVec.ofNat 64 k).toNat = ch.toNat + k := by
    intro k hk; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨e, run7.trans (run8.trans run9), r.good, r.image, r.minstret, r.tick, r.idle, r.pc, r.raReg, r.result,
    r.stack, r.saved, ?_, ?_, ?_, r.roots, ?_,
    (p7'.gprs.trans (GprsKept.of_pins p8 (by decide) (by decide) (by simp [keysG, Flush.MlFlush.ret_regs]))).trans r.gprs⟩
  · have o := p7'.output
    have ro := r.output
    unfold Vsa.Machine.output at *
    rw [ro, p8.output, o]
  · rw [read8_same fun i hi => r.frame _ (by
      rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, chOff 24 (by decide)]; omega), mem8]
    exact p7'.curr
  · rw [read8_same fun i hi => r.frame _ (by
      rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, chOff 8 (by decide)]; omega), mem8]
    exact p7'.offset
  · intro x a b rr o k z
    rw [r.frame x z, mem8]
    exact p7'.frame x a b rr o k z

/-- Return from `caml_ml_flush` on a closed channel (`fd == -1`): `Val_unit`,
nothing written outside its frame but the restored local-roots word. -/
structure MlFlushClosedPost (ra sp dom lr : BitVec 64) (c e : Config) : Prop where
  good : GoodState e.σ
  image : ExecutableImage e
  minstret : ∃ w, e.σ.regs.get? Register.minstret = some w
  tick : e.tick < 2
  idle : e.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf e = some ra
  raReg : gpr e 1 = some ra
  result : gpr e 10 = some 1#64
  stack : gpr e 2 = some sp
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr e n = gpr c n
  output : Vsa.Machine.output e.σ = Vsa.Machine.output c.σ
  roots : bytesVal .ld (read8 e.σ.mem (dom + 288#64).toNat) = lr
  frame : ∀ x, (x < sp.toNat - 112 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
    (e.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  gprs : GprsKept c e

theorem ml_flush_closed {ra sp v ch dom lr c} (h : MlFlushEntry ra sp v ch dom lr c)
    (entry : pcOf c = some 0x80016238#64)
    (closed : guardB .BEQ (bytesVal .lw (read8 c.σ.mem ch.toNat)) 18446744073709551615#64 = true) :
    ∃ e, Steps c e ∧ MlFlushClosedPost ra sp dom lr c e := by
  obtain ⟨d, run1, P⟩ := ml_flush_pro_gen h entry true closed
  obtain ⟨e, run2, r⟩ := ml_flush_tail h
    { good := P.good, image := P.image, minstret := P.minstret, tick := P.tick, idle := P.idle, pc := P.pc
      link := P.raReg, linkAligned := h.aligned, stack := P.stack, lrReg := P.lrReg, domReg := P.domReg
      rest := fun n hn => by
        have b := hn; simp only [List.mem_cons, List.mem_nil_iff, or_false] at b
        exact P.kept n (by omega) (by omega) (by simp; omega)
      savedRa := P.savedRa, savedS0 := P.savedS0, savedS1 := P.savedS1, savedS2 := P.savedS2
      gprs := P.gprs }
  refine ⟨e, run1.trans run2, r.good, r.image, r.minstret, r.tick, r.idle, r.pc, r.raReg, r.result, r.stack,
    r.saved, ?_, r.roots, ?_, P.gprs.trans r.gprs⟩
  · have o := r.output
    have po := P.output
    unfold Vsa.Machine.output at *
    rw [o, po]
  · intro x a b
    rw [r.frame x b]
    exact P.outside x a b

end OCaml.Vm.Primitives.ConsoleWrite
