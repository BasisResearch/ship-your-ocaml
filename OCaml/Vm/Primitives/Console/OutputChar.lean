import OCaml.Vm.Primitives.Console.MlFlush
import OCaml.Vm.Primitives.Flush.MlOutputChar

/-! `caml_ml_output_char(vchannel, ch)` on a buffered console output channel
with null channel-mutex hooks: register the local root, store the byte at
`curr` (flushing first when the buffer is full), and return `Val_unit`. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable
open ExitPath (LogWithin LogWithin.outL LogWithin.outLRange)
open FdWrite (errnoGlobal impurePtr enterHook leaveHook pendingSignals)

/-- `caml_ml_output_char`'s native layout: `caml_ml_flush`'s frame and
separation (the same 112-byte frame shape) plus the argument slot at the
frame base and the channel words it reads and writes. -/
structure OcLayout (sp v ch fd rp dom : BitVec 64) (len : Nat) : Prop where
  base : MlFlushLayout sp v ch fd rp dom len
  slot0 : WriteWindow (sp - 112#64) 8
  chanEnd : ReadWindow (ch + 16#64) 8
  chanCurr : WriteWindow (ch + 24#64) 8
  chanFlags : ReadWindow (ch + 68#64) 4
  /-- the buffer lies in RAM, apart from the image, the native stack, the
  errno words and the local-roots word -/
  bufRam : 0x80000000 ≤ ch.toNat ∧ ch.toNat + 72 + 65536 ≤ 0x100000000 ∧ Layout.sym_tohost + 16 ≤ ch.toNat
  bufText : ch.toNat + 72 + 65536 ≤ Image.textBase ∨ Image.textBase + Image.textSize ≤ ch.toNat
  bufRodata : ch.toNat + 72 + 65536 ≤ Image.rodataBase ∨ Image.rodataBase + Image.rodataSize ≤ ch.toNat
  bufStack : ch.toNat + 72 + 65536 ≤ sp.toNat - 384 ∨ sp.toNat ≤ ch.toNat
  bufErrno : ch.toNat + 72 + 65536 ≤ errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ ch.toNat
  bufRp : ch.toNat + 72 + 65536 ≤ rp.toNat ∨ rp.toNat + 4 ≤ ch.toNat
  bufRoots : ch.toNat + 72 + 65536 ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ ch.toNat
  /-- the channel record is malloc'd above `.bss` (`StackGeometry.channelLow`) -/
  chanLow : Layout.sym_bss_end ≤ ch.toNat

structure OcInput (ra sp v cv ch fd rp dom lr : BitVec 64) (len : Nat) (c : Config) : Prop
    extends LeafInput ra c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], (gprGet c.σ n).isSome
  stack : gpr c 2 = some sp
  valReg : gpr c 10 = some v
  charReg : gpr c 11 = some cv
  layout : OcLayout sp v ch fd rp dom len
  domWord : bytesVal .ld (read8 c.σ.mem camlStateGlobal.toNat) = dom
  rootsWord : bytesVal .ld (read8 c.σ.mem (dom + 288#64).toNat) = lr
  chanPtr : bytesVal .ld (read8 c.σ.mem (v + 8#64).toNat) = ch
  lockNull : bytesVal .ld (read8 c.σ.mem channelLock.toNat) = 0#64
  unlockNull : bytesVal .ld (read8 c.σ.mem channelUnlock.toNat) = 0#64

/-- `caml_ml_output_char` after its prologue and the (null) lock: the frame
saved, the local root registered, the channel loaded. -/
structure OcPro (ra sp v cv ch dom lr : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ w, d.σ.regs.get? Register.minstret = some w
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some 0x800163bc#64
  raReg : gpr d 1 = some ra
  stack : gpr d 2 = some (sp - 112#64)
  chReg : gpr d 8 = some ch
  lrReg : gpr d 9 = some lr
  valReg : gpr d 10 = some v
  globalReg : gpr d 18 = some 0x80064d08#64
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [2, 8, 9, 11, 12, 14, 15, 16, 17, 18] → gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ
  outside : ∀ x, (x < sp.toNat - 112 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  charWord : bytesVal .ld (read8 d.σ.mem (sp - 112#64).toNat) = cv
  savedRa : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 104).toNat) = ra
  savedS0 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 96).toNat) = (gpr c 8).getD 0
  savedS1 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 88).toNat) = (gpr c 9).getD 0
  savedS2 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 80).toNat) = (gpr c 18).getD 0
  gprs : GprsKept c d

theorem oc_pro {ra sp v cv ch fd rp dom lr len c} (h : OcInput ra sp v cv ch fd rp dom lr len c)
    (entry : pcOf c = some 0x80016350#64) :
    ∃ d, Steps c d ∧ OcPro ra sp v cv ch dom lr c d := by
  have L := h.layout.base
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
  let R0 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else if n = 10 then v else
    if n = 11 then cv else (gpr c n).getD 0
  have proIn : ∀ e ∈ Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0),
      (sp.toNat - 112 ≤ e.1 ∧ e.1 + e.2.1 ≤ sp.toNat) ∨ (e.1 = dom.toNat + 288 ∧ e.2.1 = 8) := by
    intro e he
    simp only [Flush.MlOutputChar.proLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (left; simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; rw [off112 _ (by decide)]; omega)
      | (left; simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; rw [sp112]; omega)
      | (right; simp only [Flush.MlOutputChar.pro_loads, List.getD_cons_zero]; rw [dw, r288]; simp)
  have outside0 : ∀ x, (x < sp.toNat - 112 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
      OutL (Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0)) x :=
    fun x a b => outL_of_each fun e he => by rcases proIn e he with ⟨l, u⟩ | ⟨l, u⟩ <;> omega
  have range0 : ∀ x n j, (x + n ≤ sp.toNat - 112 ∨ sp.toNat ≤ x) → (x + n ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
      OutLRange ((Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0)).take j) x n :=
    fun x n j a b => outLRange_of_each fun e he => by
      rcases proIn e (List.mem_of_mem_take he) with ⟨l, u⟩ | ⟨l, u⟩ <;> omega
  have frame5 : ∀ x n j, j ≤ 5 → (x + n ≤ sp.toNat - 112 ∨ sp.toNat ≤ x) →
      OutLRange ((Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0)).take j) x n :=
    fun x n j hj a => outLRange_of_each fun e he => by
      have he' : e ∈ (Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0)).take 5 :=
        List.take_subset_take_left _ hj he
      simp only [Flush.MlOutputChar.proLog, List.take, List.mem_cons, List.mem_nil_iff, or_false] at he'
      rcases he' with rfl | rfl | rfl | rfl | rfl <;>
        first
          | (simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; rw [off112 _ (by decide)]; omega)
          | (simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; rw [sp112]; omega)
  have slot := fun k (hk : k ∈ [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104]) => L.slots k hk
  have g := fun a (ha : a ∈ [camlStateGlobal.toNat, channelLock.toNat, channelUnlock.toNat, (v + 8#64).toNat]) =>
    L.apart a ha
  have stateAp := g camlStateGlobal.toNat (by simp)
  have lockAp := g channelLock.toNat (by simp)
  have valAp := g (v + 8#64).toNat (by simp)
  have st := stateAp.stack; have st2 := stateAp.roots
  have lk := lockAp.stack; have lk2 := lockAp.roots
  have va := valAp.stack; have va2 := valAp.roots
  rw [show camlStateGlobal.toNat = 2147896584 by decide] at st st2
  rw [show channelLock.toNat = 2147896152 by decide] at lk lk2
  clear stateAp lockAp valAp g
  have a4 : OutLRange ((Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0)).take 4)
      (0x80064d08#64).toNat 8 := by
    rw [show (0x80064d08#64 : BitVec 64).toNat = 2147896584 by decide]; exact frame5 _ _ _ (by decide) (by omega)
  have a5 : OutLRange ((Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0)).take 4)
      (0x80064b58#64).toNat 8 := by
    rw [show (0x80064b58#64 : BitVec 64).toNat = 2147896152 by decide]; exact frame5 _ _ _ (by decide) (by omega)
  have w7 : ReadWindow (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64) 8 := by
    rw [dw]; exact L.roots.read
  have a7 : OutLRange ((Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0)).take 5)
      (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64).toNat 8 := by
    rw [dw, r288]; exact frame5 _ _ _ (by decide) (by have := L.rootsApart.1; omega)
  have w10 : WriteWindow (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64) 8 := by
    rw [dw]; exact L.roots
  have a15 : OutLRange ((Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0)).take 12)
      (v + 8#64).toNat 8 :=
    range0 _ _ _ (by omega) (by omega)
  have image0 : ImageOutside (Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0)) :=
    ⟨outLRange_of_each fun e he => by have := L.text; have := L.rootsText; rcases proIn e he with ⟨l, u⟩ | ⟨l, u⟩ <;> omega,
     outLRange_of_each fun e he => by have := L.rodata; have := L.rootsRodata; rcases proIn e he with ⟨l, u⟩ | ⟨l, u⟩ <;> omega⟩
  have regs0 : GHolds c.σ (Flush.MlOutputChar.pro_input R0) :=
    ⟨h.raReg, h.stack, present 8 (by simp), present 9 (by simp), h.valReg, h.charReg, present 18 (by simp), True.intro⟩
  have ok0 : guardB .BEQ (bytesVal .ld ((Flush.MlOutputChar.pro_loads c.σ.mem R0).getD 1 [])) 0#64 = true := by
    show guardB .BEQ (bytesVal .ld (read8 c.σ.mem (0x80064b58#64).toNat)) 0#64 = true
    have := h.lockNull; simp only [channelLock] at this; rw [this]; rfl
  have P0 := Flush.MlOutputChar.pro_fast c R0 h.toLeafInput regs0
    (slot 80 (by simp)) (slot 104 (by simp)) (slot 96 (by simp)) (slot 88 (by simp)) a4 a5
    h.layout.slot0 w7 a7 (slot 8 (by simp)) (slot 16 (by simp)) w10 (slot 32 (by simp)) (slot 24 (by simp))
    (slot 40 (by simp)) (slot 48 (by simp)) L.valWindow a15 image0 ok0
  obtain ⟨d1, run1, p1⟩ := P0.run c ⟨entry, rfl⟩
  have mem1 : d1.σ.mem = writeLog c.σ.mem (Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0)) :=
    p1.memory
  have same1 : ∀ x, (x < sp.toNat - 112 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
      (d1.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := fun x a b => by rw [mem1, writeLog_out _ _ _ (outside0 x a b)]
  have ch1 : gpr d1 8 = some ch := by
    have l : gpr d1 8 = some (bytesVal .ld (read8 c.σ.mem (v + 8#64).toNat)) := gholds_lookup _ p1.regs rfl
    rw [l, h.chanPtr]
  have lr1 : gpr d1 9 = some lr := by
    have l : gpr d1 9 = some (bytesVal .ld (read8 c.σ.mem (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) +
      288#64).toNat)) := gholds_lookup _ p1.regs rfl
    rw [l, dw, h.rootsWord]
  -- the frame reads back from the prologue's log
  have back := fun (i a : Nat) (w : BitVec 64)
      (sel : (Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0))[i]? = some (a, 8, w))
      (after : OutLRange ((Flush.MlOutputChar.proLog R0 (Flush.MlOutputChar.pro_loads c.σ.mem R0)).drop (i + 1)) a 8) =>
    (show bytesVal .ld (read8 d1.σ.mem a) = w by
      rw [mem1, read8_value]
      exact Gc.word_writeLog_at _ _ i _ _ sel after)
  have apart := fun (j k : Nat) (hj : j ≤ 104) (hk : k ≤ 104) (ne : j + 8 ≤ k ∨ k + 8 ≤ j) =>
    (show (sp - 112#64 + BitVec.ofNat 64 j).toNat + 8 ≤ (sp - 112#64 + BitVec.ofNat 64 k).toNat ∨
        (sp - 112#64 + BitVec.ofNat 64 k).toNat + 8 ≤ (sp - 112#64 + BitVec.ofNat 64 j).toNat by
      rw [off112 j (by omega), off112 k (by omega)]; omega)
  have apart0 := fun (j : Nat) (hj : j ≤ 104) (ne : 8 ≤ j) =>
    (show (sp - 112#64 + BitVec.ofNat 64 j).toNat + 8 ≤ (sp - 112#64).toNat ∨
        (sp - 112#64).toNat + 8 ≤ (sp - 112#64 + BitVec.ofNat 64 j).toNat by
      rw [off112 j (by omega), sp112]; omega)
  have zeroApart := fun (k : Nat) (hk : k ≤ 104) (ne : 8 ≤ k) =>
    (show (sp - 112#64).toNat + 8 ≤ (sp - 112#64 + BitVec.ofNat 64 k).toNat ∨
        (sp - 112#64 + BitVec.ofNat 64 k).toNat + 8 ≤ (sp - 112#64).toNat by
      rw [off112 k (by omega), sp112]; omega)
  have ro := L.rootsApart.1
  have domLater := fun (a : Nat) (lo : sp.toNat - 112 ≤ a) (hi : a + 8 ≤ sp.toNat) =>
    (show a + 8 ≤ (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64).toNat ∨
        (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64).toNat + 8 ≤ a by
      rw [dw, r288]; omega)
  have dl := fun (k : Nat) (hk : k ≤ 104) => domLater (sp - 112#64 + BitVec.ofNat 64 k).toNat (by rw [off112 k (by omega)]; omega) (by rw [off112 k (by omega)]; omega)
  have s2Back := back 0 _ (R0 18) rfl
    ⟨apart 80 104 (by decide) (by decide) (by decide), apart 80 96 (by decide) (by decide) (by decide),
     apart 80 88 (by decide) (by decide) (by decide), apart0 80 (by decide) (by decide),
     apart 80 8 (by decide) (by decide) (by decide), apart 80 16 (by decide) (by decide) (by decide),
     dl 80 (by decide), apart 80 32 (by decide) (by decide) (by decide),
     apart 80 24 (by decide) (by decide) (by decide), apart 80 40 (by decide) (by decide) (by decide),
     apart 80 48 (by decide) (by decide) (by decide), trivial⟩
  have raBack := back 1 _ ra rfl
    ⟨apart 104 96 (by decide) (by decide) (by decide), apart 104 88 (by decide) (by decide) (by decide),
     apart0 104 (by decide) (by decide), apart 104 8 (by decide) (by decide) (by decide),
     apart 104 16 (by decide) (by decide) (by decide), dl 104 (by decide),
     apart 104 32 (by decide) (by decide) (by decide), apart 104 24 (by decide) (by decide) (by decide),
     apart 104 40 (by decide) (by decide) (by decide), apart 104 48 (by decide) (by decide) (by decide), trivial⟩
  have s0Back := back 2 _ (R0 8) rfl
    ⟨apart 96 88 (by decide) (by decide) (by decide), apart0 96 (by decide) (by decide),
     apart 96 8 (by decide) (by decide) (by decide), apart 96 16 (by decide) (by decide) (by decide),
     dl 96 (by decide), apart 96 32 (by decide) (by decide) (by decide),
     apart 96 24 (by decide) (by decide) (by decide), apart 96 40 (by decide) (by decide) (by decide),
     apart 96 48 (by decide) (by decide) (by decide), trivial⟩
  have s1Back := back 3 _ (R0 9) rfl
    ⟨apart0 88 (by decide) (by decide), apart 88 8 (by decide) (by decide) (by decide),
     apart 88 16 (by decide) (by decide) (by decide), dl 88 (by decide),
     apart 88 32 (by decide) (by decide) (by decide), apart 88 24 (by decide) (by decide) (by decide),
     apart 88 40 (by decide) (by decide) (by decide), apart 88 48 (by decide) (by decide) (by decide), trivial⟩
  have cBack := back 4 _ cv rfl
    ⟨zeroApart 8 (by decide) (by decide), zeroApart 16 (by decide) (by decide),
     domLater (sp - 112#64).toNat (by rw [sp112]; exact Nat.le_refl _) (by rw [sp112]; omega),
     zeroApart 32 (by decide) (by decide), zeroApart 24 (by decide) (by decide),
     zeroApart 40 (by decide) (by decide), zeroApart 48 (by decide) (by decide), trivial⟩
  refine ⟨d1, run1, p1.good, p1.image, p1.minstret, p1.tick, p1.toEffectPost.htifIdle h.idle, p1.pc,
    gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, ch1, lr1, gholds_lookup _ p1.regs rfl,
    gholds_lookup _ p1.regs rfl, fun n lo hi hn => p1.toEffectPost.gpr_frame (by decide) n lo hi hn,
    by unfold Vsa.Machine.output; rw [p1.output], same1, cBack, raBack, ?_, ?_, ?_, GprsKept.of_pins p1 (by decide) (by decide) (by simp [keysG, Flush.MlOutputChar.pro_regs])⟩
  · exact s0Back
  · exact s1Back
  · exact s2Back


/-- The state at the byte store (`0x800163c8`), reached with room in the
buffer (directly or after a flush): `curr` is `buff + k`, `k < IO_BUFFER_SIZE`. -/
structure OcTailInput (ra sp v cv ch fd rp dom lr : BitVec 64) (len k : Nat) (c0 d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ w, d.σ.regs.get? Register.minstret = some w
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some 0x800163c8#64
  layout : OcLayout sp v ch fd rp dom len
  room : k < 65536
  /-- x1 holds some aligned return address (the caller's, or a call's link);
  the epilogue reloads `ra` from the frame -/
  link : ∃ r, gpr d 1 = some r ∧ r.toNat % 4 = 0
  aligned : ra.toNat % 4 = 0
  stack : gpr d 2 = some (sp - 112#64)
  chReg : gpr d 8 = some ch
  lrReg : gpr d 9 = some lr
  a0 : ∃ w, gpr d 10 = some w
  currReg : gpr d 15 = some (ch + 72#64 + BitVec.ofNat 64 k)
  globalReg : gpr d 18 = some 0x80064d08#64
  charWord : bytesVal .ld (read8 d.σ.mem (sp - 112#64).toNat) = cv
  flags : bytesVal .lw (read8 d.σ.mem (ch + 68#64).toNat) &&& 16#64 = 0#64
  unlockNull : bytesVal .ld (read8 d.σ.mem 2147896144) = 0#64
  domain : bytesVal .ld (read8 d.σ.mem 2147896584) = dom
  savedRa : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 104).toNat) = ra
  savedS0 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 96).toNat) = (gpr c0 8).getD 0
  savedS1 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 88).toNat) = (gpr c0 9).getD 0
  savedS2 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 80).toNat) = (gpr c0 18).getD 0

/-- Return from `caml_ml_output_char`: `Val_unit`, the byte at `curr`,
`curr + 1`, `local_roots` restored; nothing else written since the store. -/
structure OcTailPost (ra sp cv ch dom lr : BitVec 64) (k : Nat) (c0 d e : Config) : Prop where
  good : GoodState e.σ
  image : ExecutableImage e
  minstret : ∃ w, e.σ.regs.get? Register.minstret = some w
  tick : e.tick < 2
  idle : e.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf e = some ra
  raReg : gpr e 1 = some ra
  result : gpr e 10 = some 1#64
  stack : gpr e 2 = some sp
  saved : ∀ n ∈ [8, 9, 18], gpr e n = some ((gpr c0 n).getD 0)
  rest : ∀ n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], gpr e n = gpr d n
  output : Vsa.Machine.output e.σ = Vsa.Machine.output d.σ
  byte : (e.σ.mem[(ch + 72#64 + BitVec.ofNat 64 k).toNat]?).getD 0 =
    Vsa.Sim.sbData (Functions.shift_bits_right_arith cv 1#6)
  curr : bytesVal .ld (read8 e.σ.mem (ch + 24#64).toNat) = ch + 72#64 + BitVec.ofNat 64 k + 1#64
  roots : bytesVal .ld (read8 e.σ.mem (dom + 288#64).toNat) = lr
  frame : ∀ x, x ≠ (ch + 72#64 + BitVec.ofNat 64 k).toNat → (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) →
    (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) → (e.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0
  gprs : GprsKept d e

theorem oc_tail {ra sp v cv ch fd rp dom lr len k c0 d} (h : OcTailInput ra sp v cv ch fd rp dom lr len k c0 d) :
    ∃ e, Steps d e ∧ OcTailPost ra sp cv ch dom lr k c0 d e := by
  obtain ⟨r, hr, ral⟩ := h.link
  obtain ⟨w0, hw0⟩ := h.a0
  have OL := h.layout
  have L := OL.base
  have floor := L.floor
  have bufRam := OL.bufRam
  have chanLow := OL.chanLow
  have glb : 2147896584 + 8 ≤ Layout.sym_bss_end ∧ 2147896144 + 8 ≤ Layout.sym_bss_end ∧
      Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have room := h.room
  have off112 : ∀ j, j ≤ 112 → (sp - 112#64 + BitVec.ofNat 64 j).toNat = sp.toNat - 112 + j := by
    intro j hj
    rw [BitVec.toNat_add, BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  have sp112 : (sp - 112#64).toNat = sp.toNat - 112 := by
    rw [BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  have chOff : ∀ j, j ≤ 72 → (ch + BitVec.ofNat 64 j).toNat = ch.toNat + j := by
    intro j hj; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  let curr : BitVec 64 := ch + 72#64 + BitVec.ofNat 64 k
  have currNat : curr.toNat = ch.toNat + 72 + k := by
    simp only [curr]; rw [BitVec.toNat_add, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have currNat' : (ch + 72#64 + BitVec.ofNat 64 k).toNat = ch.toNat + 72 + k := currNat
  have rootsRam := L.rootsRam
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have ro := L.rootsApart
  have bufStack := OL.bufStack
  have bufRoots := OL.bufRoots
  -- store the byte, curr + 1, buffered
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then r else if n = 2 then sp - 112#64 else if n = 8 then ch else
    if n = 9 then lr else if n = 10 then w0 else if n = 15 then curr else 0x80064d08#64
  have w2 : WriteWindow curr 1 := ⟨by omega, by omega, by have := bufRam.2.2; omega, by omega⟩
  have a3 : OutLRange ((Flush.MlOutputChar.putLog R1 (Flush.MlOutputChar.put_loads d.σ.mem R1)).take 2)
      (ch + 68#64).toNat 4 := by
    simp only [Flush.MlOutputChar.putLog, List.take, OutLRange, R1, ↓reduceIte, Nat.reduceEqDiff]
    have e68 : (ch + 68#64).toNat = ch.toNat + 68 := chOff 68 (by decide)
    have e24 : (ch + 24#64).toNat = ch.toNat + 24 := chOff 24 (by decide)
    rw [e68, e24, currNat]
    exact ⟨Or.inr (Nat.le_of_lt (Nat.add_lt_add_left (by decide) _)), Or.inl (by simp only [Nat.add_assoc]; exact Nat.add_le_add_left (by simp) _), trivial⟩
  have putIn : ∀ e ∈ Flush.MlOutputChar.putLog R1 (Flush.MlOutputChar.put_loads d.σ.mem R1),
      ch.toNat + 24 ≤ e.1 ∧ e.1 + e.2.1 ≤ ch.toNat + 72 + 65536 := by
    intro e he
    simp only [Flush.MlOutputChar.putLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl <;> simp only [R1, ↓reduceIte, Nat.reduceEqDiff]
    · rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, chOff 24 (by decide)]; omega
    · rw [currNat]; omega
  have putWithin : LogWithin (Flush.MlOutputChar.putLog R1 (Flush.MlOutputChar.put_loads d.σ.mem R1))
      (ch.toNat + 24) (ch.toNat + 72 + 65536) := putIn
  obtain ⟨d1, run1, p1⟩ := (Flush.MlOutputChar.put_fast d R1
    ⟨h.good, h.image, h.minstret, hr, ral, h.tick⟩
    ⟨hr, h.stack, h.chReg, h.lrReg, hw0, h.currReg, h.globalReg, True.intro⟩
    OL.slot0.read OL.chanCurr w2 OL.chanFlags a3
    ⟨putWithin.outLRange (by have := OL.bufText; omega), putWithin.outLRange (by have := OL.bufRodata; omega)⟩
    (by
      show guardB .BNE (bytesVal .lw (read8 d.σ.mem (ch + 68#64).toNat) &&& 16#64) 0#64 = false
      rw [h.flags]; rfl)).run d ⟨h.pc, rfl⟩
  have mem1 : d1.σ.mem = writeLog d.σ.mem (Flush.MlOutputChar.putLog R1 (Flush.MlOutputChar.put_loads d.σ.mem R1)) :=
    p1.memory
  have read1 : ∀ a, (a + 8 ≤ ch.toNat + 24 ∨ ch.toNat + 72 + 65536 ≤ a) → read8 d1.σ.mem a = read8 d.σ.mem a :=
    fun a ha => by rw [mem1]; exact read8_outside putWithin ha
  have keep1 := fun n (hn : n ∉ [13, 14, 15]) (lo : 1 ≤ n) (hi : n ≤ 31) => p1.toEffectPost.gpr_frame (by decide) n lo hi hn
  -- no channel unlock
  obtain ⟨d2, run2, p2⟩ := (Flush.MlOutputChar.unlock_fast d1 R1
    ⟨p1.good, p1.image, p1.minstret, (keep1 1 (by simp) (by decide) (by decide)).trans hr, ral, p1.tick⟩
    ⟨(keep1 1 (by simp) (by decide) (by decide)).trans hr, (keep1 2 (by simp) (by decide) (by decide)).trans h.stack,
      (keep1 8 (by simp) (by decide) (by decide)).trans h.chReg, (keep1 9 (by simp) (by decide) (by decide)).trans h.lrReg,
      (keep1 10 (by simp) (by decide) (by decide)).trans hw0,
      (keep1 18 (by simp) (by decide) (by decide)).trans h.globalReg, True.intro⟩
    (by
      show guardB .BEQ (bytesVal .ld (read8 d1.σ.mem (0x80064b50#64).toNat)) 0#64 = true
      rw [show (0x80064b50#64 : BitVec 64).toNat = 2147896144 by decide, read1 2147896144 (by omega), h.unlockNull]
      rfl)).run d1 ⟨p1.pc, rfl⟩
  have keep2 := fun n (hn : n ≠ 15) (lo : 1 ≤ n) (hi : n ≤ 31) =>
    p2.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn)
  have mem2 : d2.σ.mem = d1.σ.mem := by rw [p2.memory]; rfl
  -- restore local_roots and the saves
  let R2 : Nat → BitVec 64 := fun n => if n = 1 then r else if n = 2 then sp - 112#64 else if n = 9 then lr else
    0x80064d08#64
  have dom2 : bytesVal .ld (read8 d2.σ.mem (R2 18).toNat) = dom := by
    show bytesVal .ld (read8 d2.σ.mem (0x80064d08#64).toNat) = dom
    rw [mem2, show (0x80064d08#64 : BitVec 64).toNat = 2147896584 by decide, read1 2147896584 (by omega), h.domain]
  have frame2 : ∀ j, j ≤ 104 → read8 d2.σ.mem (sp - 112#64 + BitVec.ofNat 64 j).toNat =
      read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 j).toNat := by
    intro j hj; rw [mem2, read1 _ (by rw [off112 j (by omega)]; omega)]
  have retAp : ∀ j, j ≤ 104 → OutLRange ((Flush.MlOutputChar.retLog R2 (Flush.MlOutputChar.ret_loads d2.σ.mem R2)).take 1)
      (R2 2 + BitVec.ofNat 64 j).toNat 8 := by
    intro j hj
    simp only [Flush.MlOutputChar.retLog, Flush.MlOutputChar.ret_loads, List.take, OutLRange, List.getD_cons_zero]
    rw [dom2, r288]
    simp only [R2, ↓reduceIte, Nat.reduceEqDiff]
    rw [off112 j (by omega)]
    have := ro.1
    exact ⟨by omega, trivial⟩
  have retWithin : LogWithin (Flush.MlOutputChar.retLog R2 (Flush.MlOutputChar.ret_loads d2.σ.mem R2))
      (dom.toNat + 288) (dom.toNat + 296) := by
    intro e he
    simp only [Flush.MlOutputChar.retLog, Flush.MlOutputChar.ret_loads, List.mem_cons, List.mem_nil_iff, or_false,
      List.getD_cons_zero] at he
    subst he; dsimp only; rw [dom2, r288]; omega
  obtain ⟨d3, run3, p3⟩ := (Flush.MlOutputChar.ret_fast d2 ra R2
    ⟨p2.good, p2.image, p2.minstret, (keep2 1 (by decide) (by decide) (by decide)).trans
      ((keep1 1 (by simp) (by decide) (by decide)).trans hr), ral, p2.tick⟩
    ⟨(keep2 2 (by decide) (by decide) (by decide)).trans ((keep1 2 (by simp) (by decide) (by decide)).trans h.stack),
      (keep2 9 (by decide) (by decide) (by decide)).trans ((keep1 9 (by simp) (by decide) (by decide)).trans h.lrReg),
      (keep2 18 (by decide) (by decide) (by decide)).trans ((keep1 18 (by simp) (by decide) (by decide)).trans h.globalReg),
      True.intro⟩
    (show ReadWindow (0x80064d08#64) 8 from ⟨by decide, by decide, Or.inr (by decide)⟩) (by rw [dom2]; exact L.roots)
    (L.slots 104 (by simp)).read (retAp 104 (by decide)) (L.slots 96 (by simp)).read (retAp 96 (by decide))
    (L.slots 88 (by simp)).read (retAp 88 (by decide)) (L.slots 80 (by simp)).read (retAp 80 (by decide))
    ⟨retWithin.outLRange (by have := L.rootsText; omega), retWithin.outLRange (by have := L.rootsRodata; omega)⟩
    (by
      show bytesVal .ld (read8 d2.σ.mem (sp - 112#64 + BitVec.ofNat 64 104).toNat) = ra
      rw [frame2 104 (by decide)]; exact h.savedRa) h.aligned).run d2 ⟨p2.pc, rfl⟩
  have mem3 : d3.σ.mem = writeLog d2.σ.mem (Flush.MlOutputChar.retLog R2 (Flush.MlOutputChar.ret_loads d2.σ.mem R2)) :=
    p3.memory
  have load := fun (n j : Nat) (hj : j ≤ 104) (w : BitVec 64)
      (l : gpr d3 n = some (bytesVal .ld (read8 d2.σ.mem (sp - 112#64 + BitVec.ofNat 64 j).toNat)))
      (b : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 j).toNat) = w) =>
    (show gpr d3 n = some w by rw [l, frame2 j hj, b])
  have keep3 := fun n (hn : n ∉ [1, 2, 8, 9, 10, 15, 18]) (lo : 1 ≤ n) (hi : n ≤ 31) =>
    p3.toEffectPost.gpr_frame (by decide) n lo hi hn
  refine ⟨d3, run1.trans (run2.trans run3), p3.good, p3.image, p3.minstret, p3.tick,
    p3.toEffectPost.htifIdle (p2.toEffectPost.htifIdle (p1.toEffectPost.htifIdle h.idle)), p3.pc,
    load 1 104 (by decide) ra (gholds_lookup _ p3.regs rfl) h.savedRa, gholds_lookup _ p3.regs rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, (GprsKept.of_pins p1 (by decide) (by decide) (by simp [keysG, Flush.MlOutputChar.put_regs])).trans ((GprsKept.of_pins p2 (by decide) (by decide) (by simp [keysG, Flush.MlOutputChar.unlock_regs])).trans (GprsKept.of_pins p3 (by decide) (by decide) (by simp [keysG, Flush.MlOutputChar.ret_regs])))⟩
  · have l : gpr d3 2 = some (R2 2 + 112#64) := gholds_lookup _ p3.regs rfl
    rw [l]; simp only [R2, ↓reduceIte, Nat.reduceEqDiff, BitVec.sub_add_cancel]
  · intro n hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact load 8 96 (by decide) _ (gholds_lookup _ p3.regs rfl) h.savedS0
    · exact load 9 88 (by decide) _ (gholds_lookup _ p3.regs rfl) h.savedS1
    · exact load 18 80 (by decide) _ (gholds_lookup _ p3.regs rfl) h.savedS2
  · intro n hn
    have b := hn; simp only [List.mem_cons, List.mem_nil_iff, or_false] at b
    rw [keep3 n (by simp; omega) (by omega) (by omega), keep2 n (by omega) (by omega) (by omega),
      keep1 n (by simp; omega) (by omega) (by omega)]
  · have o2 := p2.output
    unfold Vsa.Machine.output at *
    rw [p3.output, o2, p1.output]
  · -- the byte: the put log's last entry, missed by the roots store
    rw [mem3, writeLog_out _ _ _ (retWithin.outL (by rw [currNat']; omega)), mem2, mem1]
    show ((writeLog d.σ.mem [((ch + 24#64).toNat, 8, curr + 1#64),
      (curr.toNat, 1, Functions.shift_bits_right_arith (bytesVal .ld (read8 d.σ.mem (sp - 112#64).toNat)) 1#6)])[curr.toNat]?).getD 0 = _
    rw [h.charWord]
    simp [writeLog, applyW]
  · rw [mem3, read8_outside retWithin (by
      have e24 : (ch + 24#64).toNat = ch.toNat + 24 := chOff 24 (by decide)
      have := ro.2.2.2; rw [e24]; omega), mem2, mem1, read8_value]
    exact Gc.word_writeLog_at d.σ.mem _ 0 (ch + 24#64).toNat _ rfl
      ⟨by have e24 : (ch + 24#64).toNat = ch.toNat + 24 := chOff 24 (by decide)
          simp only [R1, ↓reduceIte, Nat.reduceEqDiff]; rw [e24, currNat]; omega, trivial⟩
  · rw [mem3, read8_value]
    have w := Gc.word_writeLog_at d2.σ.mem (Flush.MlOutputChar.retLog R2 (Flush.MlOutputChar.ret_loads d2.σ.mem R2))
      0 (bytesVal .ld (read8 d2.σ.mem (R2 18).toNat) + 288#64).toNat (R2 9) rfl trivial
    rw [dom2] at w
    exact w
  · intro x xc xw xr
    rw [mem3, writeLog_out _ _ _ (retWithin.outL xr), mem2, mem1, writeLog_out _ _ _ ?_]
    simp only [Flush.MlOutputChar.putLog, OutL, R1, ↓reduceIte, Nat.reduceEqDiff]
    have e24 : (ch + 24#64).toNat = ch.toNat + 24 := chOff 24 (by decide)
    rw [e24]
    refine ⟨by omega, ?_, trivial⟩
    rw [currNat]
    rw [currNat'] at xc
    omega


/-- Return from `caml_ml_output_char` on a channel with room: `Val_unit`, the
byte stored at `curr`, `curr + 1`, s0–s11 and sp restored, the console
unchanged; only the native frame, `curr`, the byte and `local_roots` written. -/
structure OcPost (ra sp cv ch dom lr : BitVec 64) (k : Nat) (c e : Config) : Prop where
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
  byte : (e.σ.mem[(ch + 72#64 + BitVec.ofNat 64 k).toNat]?).getD 0 =
    Vsa.Sim.sbData (Functions.shift_bits_right_arith cv 1#6)
  curr : bytesVal .ld (read8 e.σ.mem (ch + 24#64).toNat) = ch + 72#64 + BitVec.ofNat 64 k + 1#64
  roots : bytesVal .ld (read8 e.σ.mem (dom + 288#64).toNat) = lr
  frame : ∀ x, (x < sp.toNat - 112 ∨ sp.toNat ≤ x) → x ≠ (ch + 72#64 + BitVec.ofNat 64 k).toNat →
    (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
    (e.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  gprs : GprsKept c e

theorem oc_room {ra sp v cv ch fd rp dom lr len c} (h : OcInput ra sp v cv ch fd rp dom lr len c)
    (entry : pcOf c = some 0x80016350#64) (room : len < 65536)
    (currWord : bytesVal .ld (read8 c.σ.mem (ch + 24#64).toNat) = ch + 72#64 + BitVec.ofNat 64 len)
    (endWord : bytesVal .ld (read8 c.σ.mem (ch + 16#64).toNat) = ch + 72#64 + 65536#64)
    (flags : bytesVal .lw (read8 c.σ.mem (ch + 68#64).toNat) &&& 16#64 = 0#64) :
    ∃ e, Steps c e ∧ OcPost ra sp cv ch dom lr len c e ∧ Vsa.Machine.output e.σ = Vsa.Machine.output c.σ := by
  obtain ⟨d1, run1, P⟩ := oc_pro h entry
  have OL := h.layout
  have L := OL.base
  have floor := L.floor
  have rootsRam := L.rootsRam
  have bufRam := OL.bufRam
  have chOff : ∀ j, j ≤ 72 → (ch + BitVec.ofNat 64 j).toNat = ch.toNat + j := by
    intro j hj; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hd := OL.bufStack
  have hr := OL.bufRoots
  have read1 : ∀ j, j ≤ 72 → read8 d1.σ.mem (ch + BitVec.ofNat 64 j).toNat = read8 c.σ.mem (ch + BitVec.ofNat 64 j).toNat :=
    fun j hj => read8_same fun i hi => P.outside _ (by rw [chOff j (by omega)]; omega) (by rw [chOff j (by omega)]; omega)
  have unlockAp := L.apart channelUnlock.toNat (by simp)
  have stateAp := L.apart camlStateGlobal.toNat (by simp)
  have u1 := unlockAp.stack; have u5 := unlockAp.roots
  have s1 := stateAp.stack; have s5 := stateAp.roots
  rw [show channelUnlock.toNat = 2147896144 by decide] at u1 u5
  rw [show camlStateGlobal.toNat = 2147896584 by decide] at s1 s5
  clear unlockAp stateAp
  have glob : ∀ a, (a + 8 ≤ sp.toNat - 384 ∨ sp.toNat ≤ a) → (a + 8 ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ a) →
      read8 d1.σ.mem a = read8 c.σ.mem a :=
    fun a x y => read8_same fun i hi => P.outside _ (by omega) (by omega)
  -- curr < end: room in the buffer
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp - 112#64 else if n = 8 then ch else
    if n = 9 then lr else if n = 10 then v else 0x80064d08#64
  have curr1 : bytesVal .ld (read8 d1.σ.mem (ch + 24#64).toNat) = ch + 72#64 + BitVec.ofNat 64 len := by
    rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, read1 24 (by decide)]; exact currWord
  have end1 : bytesVal .ld (read8 d1.σ.mem (ch + 16#64).toNat) = ch + 72#64 + 65536#64 := by
    rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, read1 16 (by decide)]; exact endWord
  have below : guardB .BGEU (ch + 72#64 + BitVec.ofNat 64 len) (ch + 72#64 + 65536#64) = false := by
    have e1 : (ch + 72#64 + BitVec.ofNat 64 len).toNat = ch.toNat + 72 + len := by
      rw [BitVec.toNat_add, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    have e2 : (ch + 72#64 + 65536#64).toNat = ch.toNat + 72 + 65536 := by
      rw [BitVec.toNat_add, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    simp only [guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt, e1, e2]
    simp only [decide_eq_false_iff_not, Int.ofNat_eq_coe]
    omega
  obtain ⟨d2, run2, p2⟩ := (Flush.MlOutputChar.room_fast d1 R1
    ⟨P.good, P.image, P.minstret, P.raReg, h.aligned, P.tick⟩
    ⟨P.raReg, P.stack, P.chReg, P.lrReg, P.valReg, P.globalReg, True.intro⟩
    OL.chanCurr.read OL.chanEnd
    (by
      show guardB .BGEU (bytesVal .ld (read8 d1.σ.mem (ch + 24#64).toNat))
        (bytesVal .ld (read8 d1.σ.mem (ch + 16#64).toNat)) = false
      rw [curr1, end1]; exact below)).run d1 ⟨P.pc, rfl⟩
  have keep2 := fun n (hn : n ∉ [14, 15]) (lo : 1 ≤ n) (hi : n ≤ 31) => p2.toEffectPost.gpr_frame (by decide) n lo hi hn
  have mem2 : d2.σ.mem = d1.σ.mem := by rw [p2.memory]; rfl
  have tail : OcTailInput ra sp v cv ch fd rp dom lr len len c d2 :=
    { good := p2.good, image := p2.image, minstret := p2.minstret, tick := p2.tick
      idle := p2.toEffectPost.htifIdle P.idle, pc := p2.pc, layout := OL, room := room
      link := ⟨ra, (keep2 1 (by simp) (by decide) (by decide)).trans P.raReg, h.aligned⟩, aligned := h.aligned
      stack := (keep2 2 (by simp) (by decide) (by decide)).trans P.stack
      chReg := (keep2 8 (by simp) (by decide) (by decide)).trans P.chReg
      lrReg := (keep2 9 (by simp) (by decide) (by decide)).trans P.lrReg
      a0 := ⟨v, (keep2 10 (by simp) (by decide) (by decide)).trans P.valReg⟩
      currReg := by
        have l : gpr d2 15 = some (bytesVal .ld (read8 d1.σ.mem (R1 8 + 24#64).toNat)) := gholds_lookup _ p2.regs rfl
        rw [l]; exact congrArg some curr1
      globalReg := (keep2 18 (by simp) (by decide) (by decide)).trans P.globalReg
      charWord := by rw [mem2]; exact P.charWord
      flags := by rw [mem2, show (68#64 : BitVec 64) = BitVec.ofNat 64 68 from rfl, read1 68 (by decide)]; exact flags
      unlockNull := by
        rw [mem2, glob 2147896144 (by omega) (by omega)]
        have := h.unlockNull; simp only [channelUnlock] at this
        rwa [show (0x80064b50#64 : BitVec 64).toNat = 2147896144 by decide] at this
      domain := by
        rw [mem2, glob 2147896584 (by omega) (by omega)]
        have := h.domWord; simp only [camlStateGlobal] at this
        rwa [show (0x80064d08#64 : BitVec 64).toNat = 2147896584 by decide] at this
      savedRa := by rw [mem2]; exact P.savedRa
      savedS0 := by rw [mem2]; exact P.savedS0
      savedS1 := by rw [mem2]; exact P.savedS1
      savedS2 := by rw [mem2]; exact P.savedS2 }
  obtain ⟨e, run3, T⟩ := oc_tail tail
  have present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr c n = some ((gpr c n).getD 0) := by
    intro n hn
    have := h.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  refine ⟨e, run1.trans (run2.trans run3), ⟨T.good, T.image, T.minstret, T.tick, T.idle, T.pc, T.raReg, T.result,
    T.stack, ?_, T.byte, T.curr, T.roots, fun x a b w r => by rw [T.frame x b w r, mem2]; exact P.outside x a r,
    P.gprs.trans ((GprsKept.of_pins p2 (by decide) (by decide) (by simp [keysG, Flush.MlOutputChar.room_regs])).trans T.gprs)⟩, ?_⟩
  · intro n hn
    rw [present n hn]
    have hn' := hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn'
    rcases hn' with rfl | rfl | rfl | hn'
    · exact T.saved 8 (by simp)
    · exact T.saved 9 (by simp)
    · exact T.saved 18 (by simp)
    · rw [T.rest n (by simp; omega), keep2 n (by simp; omega) (by omega) (by omega),
        P.kept n (by omega) (by omega) (by simp; omega)]
      exact present n hn
  · have o := T.output; have o1 := P.output
    unfold Vsa.Machine.output at *
    rw [o, p2.output, o1]


/-- The call of `caml_flush_partial` from `caml_ml_output_char` on a full
buffer: its input, the frame words and the memory unchanged outside the
frame and the local-roots word. -/
structure OcCall (ra sp cv ch fd rp off dom lr : BitVec 64) (bs : List UInt8) (c d : Config) : Prop where
  flush : FlushInput Flush.MlOutputChar.flush_call.link (sp - 112#64) ch fd rp off bs d
  pc : pcOf d = some 0x80015408#64
  chReg : gpr d 8 = some ch
  lrReg : gpr d 9 = some lr
  globalReg : gpr d 18 = some 0x80064d08#64
  rest : ∀ n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ
  outside : ∀ x, (x < sp.toNat - 112 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  charWord : bytesVal .ld (read8 d.σ.mem (sp - 112#64).toNat) = cv
  savedRa : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 104).toNat) = ra
  savedS0 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 96).toNat) = (gpr c 8).getD 0
  savedS1 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 88).toNat) = (gpr c 9).getD 0
  savedS2 : bytesVal .ld (read8 d.σ.mem (sp - 112#64 + BitVec.ofNat 64 80).toNat) = (gpr c 18).getD 0
  gprs : GprsKept c d

theorem oc_full_enter {ra sp v cv ch fd rp off dom lr bs c} (h : OcInput ra sp v cv ch fd rp dom lr bs.length c)
    (entry : pcOf c = some 0x80016350#64) (F : FlushMem (sp - 112#64) ch fd rp off bs c) (full : bs.length = 65536)
    (endWord : bytesVal .ld (read8 c.σ.mem (ch + 16#64).toNat) = ch + 72#64 + 65536#64) :
    ∃ d, Steps c d ∧ OcCall ra sp cv ch fd rp off dom lr bs c d := by
  obtain ⟨d1, run1, P⟩ := oc_pro h entry
  have OL := h.layout
  have L := OL.base
  have floor := L.floor
  have rootsRam := L.rootsRam
  have bufRam := OL.bufRam
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have chOff : ∀ j, j ≤ 72 → (ch + BitVec.ofNat 64 j).toNat = ch.toNat + j := by
    intro j hj; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hd := OL.bufStack
  have hr := OL.bufRoots
  have present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr c n = some ((gpr c n).getD 0) := by
    intro n hn
    have := h.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  have read1 : ∀ j, j ≤ 72 → read8 d1.σ.mem (ch + BitVec.ofNat 64 j).toNat = read8 c.σ.mem (ch + BitVec.ofNat 64 j).toNat :=
    fun j hj => read8_same fun i hi => P.outside _ (by rw [chOff j (by omega)]; omega) (by rw [chOff j (by omega)]; omega)
  -- curr ≥ end: the buffer is full
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp - 112#64 else if n = 8 then ch else
    if n = 9 then lr else if n = 10 then v else 0x80064d08#64
  have curr1 : bytesVal .ld (read8 d1.σ.mem (ch + 24#64).toNat) = ch + 72#64 + BitVec.ofNat 64 bs.length := by
    rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, read1 24 (by decide)]; exact F.curr
  have end1 : bytesVal .ld (read8 d1.σ.mem (ch + 16#64).toNat) = ch + 72#64 + 65536#64 := by
    rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, read1 16 (by decide)]; exact endWord
  obtain ⟨d2, run2, p2⟩ := (Flush.MlOutputChar.full_fast d1 R1
    ⟨P.good, P.image, P.minstret, P.raReg, h.aligned, P.tick⟩
    ⟨P.raReg, P.stack, P.chReg, P.lrReg, P.valReg, P.globalReg, True.intro⟩
    OL.chanCurr.read OL.chanEnd
    (by
      show guardB .BGEU (bytesVal .ld (read8 d1.σ.mem (ch + 24#64).toNat))
        (bytesVal .ld (read8 d1.σ.mem (ch + 16#64).toNat)) = true
      rw [curr1, end1, full]
      simp [guardB, Functions.zopz0zKzJ_u])).run d1 ⟨P.pc, rfl⟩
  have keep2 := fun n (hn : n ∉ [14, 15]) (lo : 1 ≤ n) (hi : n ≤ 31) => p2.toEffectPost.gpr_frame (by decide) n lo hi hn
  have R2ok : GHolds d2.σ (Flush.MlOutputChar.flush_input R1) :=
    ⟨(keep2 1 (by simp) (by decide) (by decide)).trans P.raReg, (keep2 2 (by simp) (by decide) (by decide)).trans P.stack,
      (keep2 8 (by simp) (by decide) (by decide)).trans P.chReg, (keep2 9 (by simp) (by decide) (by decide)).trans P.lrReg,
      (keep2 10 (by simp) (by decide) (by decide)).trans P.valReg,
      (keep2 18 (by simp) (by decide) (by decide)).trans P.globalReg, True.intro⟩
  obtain ⟨d3, run3, p3⟩ := (Flush.MlOutputChar.flush_fast d2 R1
    ⟨p2.good, p2.image, p2.minstret, (keep2 1 (by simp) (by decide) (by decide)).trans P.raReg, h.aligned, p2.tick⟩
    R2ok).run d2 ⟨p2.pc, rfl⟩
  have J3 := call_registers_summary Flush.MlOutputChar.flush_call_shape Flush.MlOutputChar.flush_call_decode d3
    (Flush.MlOutputChar.flush_call_pins p3.image) p3.good p3.image p3.tick p3.minstret
    [(10, ch)] ⟨gholds_lookup _ p3.regs rfl, True.intro⟩
    (by change KeysOK [10]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  obtain ⟨d4, run4, q4⟩ := J3.run d3 ⟨p3.pc, rfl⟩
  have mem4 : d4.σ.mem = d1.σ.mem := by
    rw [q4.memory, p3.memory, show writeLog d2.σ.mem [] = d2.σ.mem from rfl, p2.memory]; rfl
  have k4 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 10, 14, 15] → gpr d4 n = gpr d1 n := fun n lo hi hn => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    rw [q4.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega),
      p3.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega), keep2 n (by simp; omega) lo hi]
  have isSome : ∀ {d : Config} {n : Nat} {w : BitVec 64}, gpr d n = some w → (gprGet d.σ n).isSome := by
    intro d n w e; change (gpr d n).isSome; rw [e]; rfl
  have rest4 : ∀ n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], gpr d4 n = gpr c n := by
    intro n hn
    have b := hn; simp only [List.mem_cons, List.mem_nil_iff, or_false] at b
    rw [k4 n (by omega) (by omega) (by simp; omega), P.kept n (by omega) (by omega) (by simp; omega)]
  have rd := L.reads
  refine ⟨d4, run1.trans (run2.trans (run3.trans run4)),
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
      chanReg := gholds_lookup _ q4.regs rfl },
    q4.pc, (k4 8 (by decide) (by decide) (by simp)).trans P.chReg, (k4 9 (by decide) (by decide) (by simp)).trans P.lrReg,
    (k4 18 (by decide) (by decide) (by simp)).trans P.globalReg, rest4, ?_, fun x a b => by rw [mem4]; exact P.outside x a b,
    by rw [mem4]; exact P.charWord, by rw [mem4]; exact P.savedRa, by rw [mem4]; exact P.savedS0,
    by rw [mem4]; exact P.savedS1, by rw [mem4]; exact P.savedS2,
    P.gprs.trans ((GprsKept.of_pins p2 (by decide) (by decide) (by simp [keysG, Flush.MlOutputChar.full_regs])).trans ((GprsKept.of_pins p3 (by decide) (by decide) (by simp [keysG, Flush.MlOutputChar.flush_regs])).trans (GprsKept.of_pins q4 (by decide) (by decide) (by simp [keysG]))))⟩
  have o := P.output
  unfold Vsa.Machine.output at *
  rw [q4.output, p3.output, p2.output, o]


/-- `caml_ml_output_char` back at the byte store after flushing a full
buffer: the tail input with `curr = buff`, and the flush's effects. -/
structure OcFlushed (ra sp v cv ch fd rp off dom lr : BitVec 64) (bs : List UInt8) (c d : Config) : Prop where
  tail : OcTailInput ra sp v cv ch fd rp dom lr bs.length 0 c d
  rest : ∀ n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ ++ bytesToString bs
  offset : bytesVal .ld (read8 d.σ.mem (ch + 8#64).toNat) = off + BitVec.ofNat 64 bs.length
  frame : ∀ x, (x < sp.toNat - 384 ∨ sp.toNat ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
    (x < rp.toNat ∨ rp.toNat + 4 ≤ x) → (x < ch.toNat + 8 ∨ ch.toNat + 16 ≤ x) →
    (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  gprs : GprsKept c d

theorem oc_full_flushed {ra sp v cv ch fd rp off dom lr bs c} (h : OcInput ra sp v cv ch fd rp dom lr bs.length c)
    (entry : pcOf c = some 0x80016350#64) (F : FlushMem (sp - 112#64) ch fd rp off bs c) (full : bs.length = 65536)
    (endWord : bytesVal .ld (read8 c.σ.mem (ch + 16#64).toNat) = ch + 72#64 + 65536#64)
    (flags : bytesVal .lw (read8 c.σ.mem (ch + 68#64).toNat) &&& 16#64 = 0#64) :
    ∃ d, Steps c d ∧ OcFlushed ra sp v cv ch fd rp off dom lr bs c d := by
  obtain ⟨d4, run4, M⟩ := oc_full_enter h entry F full endWord
  have OL := h.layout
  have L := OL.base
  have floor := L.floor
  have bufRam := OL.bufRam
  have off112 : ∀ j, j ≤ 112 → (sp - 112#64 + BitVec.ofNat 64 j).toNat = sp.toNat - 112 + j := by
    intro j hj
    rw [BitVec.toNat_add, BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  have sp112 : (sp - 112#64).toNat = sp.toNat - 112 := by
    rw [BitVec.toNat_sub]; have := sp.isLt; simp only [BitVec.toNat_ofNat]; omega
  have chOff : ∀ j, j ≤ 72 → (ch + BitVec.ofNat 64 j).toNat = ch.toNat + j := by
    intro j hj; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have rootsRam := L.rootsRam
  have hd := OL.bufStack
  have hr := OL.bufRoots
  have he := OL.bufErrno
  have hp := OL.bufRp
  have errF := L.errnoFrame
  have rpF := L.rpFrame
  have ro := L.rootsApart
  -- caml_flush_partial writes the whole buffer
  obtain ⟨d5, run5, f5⟩ := flush_partial M.flush M.pc
  have S := L.sep (chanRam := by have := bufRam.2.1; omega)
  have frame5 : ∀ x, (x < sp.toNat - 384 ∨ sp.toNat - 112 ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
      (x < rp.toNat ∨ rp.toNat + 4 ≤ x) → (x < ch.toNat + 8 ∨ ch.toNat + 16 ≤ x) →
      (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → (d5.σ.mem[x]?).getD 0 = (d4.σ.mem[x]?).getD 0 :=
    fun x a b r o k => f5.frame x (by rw [sp112, Nat.sub_sub]; omega) b r o k
  have read5 : ∀ a, FlushMiss sp.toNat ch.toNat rp.toNat a → read8 d5.σ.mem a = read8 d4.σ.mem a :=
    fun a ok => read8_same fun i hi => by
      obtain ⟨o1, o2, o3, o4⟩ := ok
      exact frame5 _ (by omega) (by rw [show errnoGlobal.toNat = 2147896648 by decide]; omega) (by omega)
        (by omega) (by omega)
  have read4 : ∀ a, ProMiss sp.toNat dom.toNat a → read8 d4.σ.mem a = read8 c.σ.mem a :=
    fun a ok => read8_same fun i hi => by obtain ⟨o1, o2⟩ := ok; exact M.outside _ (by omega) (by omega)
  have frameW : ∀ j, j ≤ 104 → read8 d5.σ.mem (sp - 112#64 + BitVec.ofNat 64 j).toNat =
      read8 d4.σ.mem (sp - 112#64 + BitVec.ofNat 64 j).toNat := by
    intro j hj; rw [off112 j (by omega)]; exact read5 _ (S.frame j hj)
  have char5 : read8 d5.σ.mem (sp - 112#64).toNat = read8 d4.σ.mem (sp - 112#64).toNat := by
    rw [sp112]; have := S.frame 0 (by decide); simpa using read5 _ this
  have flags6 : read8 d5.σ.mem (ch + 68#64).toNat = read8 c.σ.mem (ch + 68#64).toNat := by
    rw [show (68#64 : BitVec 64) = BitVec.ofNat 64 68 from rfl, chOff 68 (by decide)]
    exact (read8_same fun i hi => frame5 _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (read8_same fun i hi => M.outside _ (by omega) (by omega))
  -- reload curr (now the buffer start)
  let R5 : Nat → BitVec 64 := fun n => if n = 1 then Flush.MlOutputChar.flush_call.link else
    if n = 2 then sp - 112#64 else if n = 8 then ch else if n = 9 then lr else if n = 10 then 1#64 else 0x80064d08#64
  have ch5 : gpr d5 8 = some ch := (f5.saved 8 (by simp)).trans M.chReg
  have lr5 : gpr d5 9 = some lr := (f5.saved 9 (by simp)).trans M.lrReg
  have g5 : gpr d5 18 = some 0x80064d08#64 := (f5.saved 18 (by simp)).trans M.globalReg
  obtain ⟨d6, run6, p6⟩ := (Flush.MlOutputChar.reload_fast d5 R5
    ⟨f5.good, f5.image, f5.minstret, f5.raReg, by simp only [R5, ↓reduceIte]; decide, f5.tick⟩
    ⟨f5.raReg, f5.stack, ch5, lr5, f5.result, g5, True.intro⟩ OL.chanCurr.read).run d5 ⟨f5.pc, rfl⟩
  have keep6 := fun n (hn : n ≠ 15) (lo : 1 ≤ n) (hi : n ≤ 31) =>
    p6.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn)
  have mem6 : d6.σ.mem = d5.σ.mem := by rw [p6.memory]; rfl
  refine ⟨d6, run4.trans (run5.trans run6), ⟨p6.good, p6.image, p6.minstret, p6.tick, p6.toEffectPost.htifIdle f5.idle, p6.pc, OL, by decide,
    ⟨_, (keep6 1 (by decide) (by decide) (by decide)).trans f5.raReg, by decide⟩, h.aligned,
    (keep6 2 (by decide) (by decide) (by decide)).trans f5.stack,
    (keep6 8 (by decide) (by decide) (by decide)).trans ch5, (keep6 9 (by decide) (by decide) (by decide)).trans lr5,
    ⟨_, (keep6 10 (by decide) (by decide) (by decide)).trans f5.result⟩, ?_,
    (keep6 18 (by decide) (by decide) (by decide)).trans g5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    M.gprs.trans (f5.gprs.trans (GprsKept.of_pins p6 (by decide) (by decide) (by simp [keysG, Flush.MlOutputChar.reload_regs])))⟩
  · have l : gpr d6 15 = some (bytesVal .ld (read8 d5.σ.mem (R5 8 + 24#64).toNat)) := gholds_lookup _ p6.regs rfl
    rw [l]; show some (bytesVal .ld (read8 d5.σ.mem (ch + 24#64).toNat)) = _
    rw [f5.curr]; simp
  · rw [mem6, char5]; exact M.charWord
  · rw [mem6, flags6]; exact flags
  · rw [mem6, read5 _ S.unlockFlush, read4 _ S.unlockPro]
    have := h.unlockNull; simp only [channelUnlock] at this
    rwa [show (0x80064b50#64 : BitVec 64).toNat = 2147896144 by decide] at this
  · rw [mem6, read5 _ S.stateFlush, read4 _ S.statePro]
    have := h.domWord; simp only [camlStateGlobal] at this
    rwa [show (0x80064d08#64 : BitVec 64).toNat = 2147896584 by decide] at this
  · rw [mem6, frameW 104 (by decide)]; exact M.savedRa
  · rw [mem6, frameW 96 (by decide)]; exact M.savedS0
  · rw [mem6, frameW 88 (by decide)]; exact M.savedS1
  · rw [mem6, frameW 80 (by decide)]; exact M.savedS2
  · intro n hn
    rw [keep6 n (by simp at hn; omega) (by simp at hn; omega) (by simp at hn; omega), f5.saved n (by simp at hn ⊢; omega)]
    exact M.rest n hn
  · have o := f5.output; have o4 := M.output
    unfold Vsa.Machine.output at *
    rw [p6.output, o, o4]
  · rw [mem6]; exact f5.offset
  · intro x a b r o k z
    have fp := S.footprint x a
    rw [mem6, frame5 x fp.1 b r o k, M.outside x fp.2 z]


/-- Return from `caml_ml_output_char` on a full buffer: the buffer written to
the console and the byte stored at the buffer's start. -/
structure OcFullPost (ra sp cv ch rp off dom lr : BitVec 64) (bs : List UInt8) (c e : Config) : Prop where
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
  output : Vsa.Machine.output e.σ = Vsa.Machine.output c.σ ++ bytesToString bs
  byte : (e.σ.mem[(ch + 72#64 + BitVec.ofNat 64 0).toNat]?).getD 0 =
    Vsa.Sim.sbData (Functions.shift_bits_right_arith cv 1#6)
  curr : bytesVal .ld (read8 e.σ.mem (ch + 24#64).toNat) = ch + 72#64 + BitVec.ofNat 64 0 + 1#64
  offset : bytesVal .ld (read8 e.σ.mem (ch + 8#64).toNat) = off + BitVec.ofNat 64 bs.length
  roots : bytesVal .ld (read8 e.σ.mem (dom + 288#64).toNat) = lr
  frame : ∀ x, (x < sp.toNat - 384 ∨ sp.toNat ≤ x) → (x < errnoGlobal.toNat ∨ errnoGlobal.toNat + 4 ≤ x) →
    (x < rp.toNat ∨ rp.toNat + 4 ≤ x) → (x < ch.toNat + 8 ∨ ch.toNat + 16 ≤ x) →
    (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → x ≠ (ch + 72#64 + BitVec.ofNat 64 0).toNat →
    (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) → (e.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  gprs : GprsKept c e

theorem oc_full {ra sp v cv ch fd rp off dom lr bs c} (h : OcInput ra sp v cv ch fd rp dom lr bs.length c)
    (entry : pcOf c = some 0x80016350#64) (F : FlushMem (sp - 112#64) ch fd rp off bs c) (full : bs.length = 65536)
    (endWord : bytesVal .ld (read8 c.σ.mem (ch + 16#64).toNat) = ch + 72#64 + 65536#64)
    (flags : bytesVal .lw (read8 c.σ.mem (ch + 68#64).toNat) &&& 16#64 = 0#64) :
    ∃ e, Steps c e ∧ OcFullPost ra sp cv ch rp off dom lr bs c e := by
  obtain ⟨d, run1, D⟩ := oc_full_flushed h entry F full endWord flags
  obtain ⟨e, run2, T⟩ := oc_tail D.tail
  have present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr c n = some ((gpr c n).getD 0) := by
    intro n hn
    have := h.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  have OL := h.layout
  have bufRam := OL.bufRam
  have hr := OL.bufRoots
  have chOff : ∀ j, j ≤ 72 → (ch + BitVec.ofNat 64 j).toNat = ch.toNat + j := by
    intro j hj; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have byteAt : (ch + 72#64 + BitVec.ofNat 64 0).toNat = ch.toNat + 72 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨e, run1.trans run2, T.good, T.image, T.minstret, T.tick, T.idle, T.pc, T.raReg, T.result, T.stack, ?_,
    ?_, T.byte, T.curr, ?_, T.roots, ?_, D.gprs.trans T.gprs⟩
  · intro n hn
    rw [present n hn]
    have hn' := hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn'
    rcases hn' with rfl | rfl | rfl | hn'
    · exact T.saved 8 (by simp)
    · exact T.saved 9 (by simp)
    · exact T.saved 18 (by simp)
    · rw [T.rest n (by simp; omega), D.rest n (by simp; omega)]; exact present n hn
  · have o := T.output; have o1 := D.output
    unfold Vsa.Machine.output at *
    rw [o, o1]
  · have e8 : (ch + 8#64).toNat = ch.toNat + 8 := chOff 8 (by decide)
    rw [read8_same (m := d.σ.mem) fun i hi => T.frame _ (by rw [e8, byteAt]; omega) (by rw [e8]; omega)
      (by rw [e8]; omega)]
    exact D.offset
  · intro x a b r o k y z
    rw [T.frame x y k z]
    exact D.frame x a b r o k z

end OCaml.Vm.Primitives.ConsoleWrite