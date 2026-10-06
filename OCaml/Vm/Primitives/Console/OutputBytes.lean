import OCaml.Vm.Primitives.Console.Geometry
import OCaml.Vm.Primitives.Flush.MlOutputBytes
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Gc.F1Runtime
import OCaml.Vm.Primitives.Memmove
import OCaml.Vm.Primitives.GprsKept

/-! `caml_ml_output_bytes(vchannel, buff, start, length)` on a buffered console
output channel with null channel-mutex hooks: its prologue (frame, local root,
channel), the copy loop (memmove into the buffer, `caml_flush_partial` of each
full buffer) and its epilogue. The phases are separate theorems to stay within
the elaboration budget. Frame readbacks: `word_writeLog_at` with the frame
offsets normalised by one `simp (disch := decide)` and `omega` per apartness. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable
open FdWrite (errnoGlobal impurePtr enterHook leaveHook pendingSignals)

/-- `caml_ml_output_bytes`' entry: the four arguments, the console statics it
reads, and the numeric geometry of its frame and the channel's whole record. -/
structure ObInput (ra sp v str ofs len ch dom lr : BitVec 64) (c : Config) : Prop
    extends LeafInput ra c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], (gprGet c.σ n).isSome
  stack : gpr c 2 = some sp
  valReg : gpr c 10 = some v
  strReg : gpr c 11 = some str
  ofsReg : gpr c 12 = some ofs
  lenReg : gpr c 13 = some len
  geo : ConsoleGeometry sp.toNat ch.toNat dom.toNat v.toNat 65536
  domWord : bytesVal .ld (read8 c.σ.mem camlStateGlobal.toNat) = dom
  rootsWord : bytesVal .ld (read8 c.σ.mem (dom + 288#64).toNat) = lr
  chanPtr : bytesVal .ld (read8 c.σ.mem (v + 8#64).toNat) = ch
  lockNull : bytesVal .ld (read8 c.σ.mem channelLock.toNat) = 0#64
  unlockNull : bytesVal .ld (read8 c.σ.mem channelUnlock.toNat) = 0#64
  flagsClear : bytesVal .lw (read8 c.σ.mem (ch + 68#64).toNat) &&& 16#64 = 0#64

/-- `caml_ml_output_bytes` after its prologue and the (null) lock: the
176-byte frame saved, the local root registered, the channel and the untagged
length loaded. -/
structure ObPro (ra sp v str ofs len ch dom lr : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ w, d.σ.regs.get? Register.minstret = some w
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some 0x800165c0#64
  raReg : gpr d 1 = some ra
  stack : gpr d 2 = some (sp - 176#64)
  lenReg : gpr d 9 = some (Functions.shift_bits_right_arith len 1#6)
  valReg : gpr d 10 = some v
  strReg : gpr d 11 = some str
  chReg : gpr d 18 = some ch
  lrReg : gpr d 20 = some lr
  stateReg : gpr d 21 = some 0x80064d08#64
  ofsReg : gpr d 23 = some ofs
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [2, 6, 9, 14, 15, 16, 17, 18, 20, 21, 23, 28, 29, 30] → gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ
  outside : ∀ x, (x < sp.toNat - 176 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  savedRa : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 168#64).toNat) = ra
  savedS1 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 152#64).toNat) = (gpr c 9).getD 0
  savedS2 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 144#64).toNat) = (gpr c 18).getD 0
  savedS4 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 128#64).toNat) = (gpr c 20).getD 0
  savedS5 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 120#64).toNat) = (gpr c 21).getD 0
  savedS7 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 104#64).toNat) = (gpr c 23).getD 0
  savedStr : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 16#64).toNat) = str
  roots : bytesVal .ld (read8 d.σ.mem (dom + 288#64).toNat) = sp - 176#64 + 32#64
  gprs : GprsKept c d

theorem ob_pro {ra sp v str ofs len ch dom lr c} (h : ObInput ra sp v str ofs len ch dom lr c)
    (entry : pcOf c = some 0x8001652c#64) :
    ∃ d, Steps c d ∧ ObPro ra sp v str ofs len ch dom lr c d := by
  have G := h.geo.lits
  have C := consoleLits
  have present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr c n = some ((gpr c n).getD 0) := by
    intro n hn
    have := h.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned; have l7 := G.domLow; have l8 := G.domHigh
  have l9 := G.domAligned; have l11 := G.valLow; have l12 := G.valHigh; have l14 := G.valDom
  have T := C.textEnd; have Rd := C.rodataEnd
  have tb : 0x80000000 ≤ Image.textBase := by decide
  have rb : 0x80000000 ≤ Image.rodataBase := by decide
  obtain ⟨F, hF⟩ : ∃ F, sp.toNat = F + 176 := ⟨sp.toNat - 176, by omega⟩
  have off : ∀ k, k ≤ 176 → (sp - 176#64 + BitVec.ofNat 64 k).toNat = F + k := by
    intro k hk; rw [BitVec.toNat_add, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have offz : (sp - 176#64).toNat = F := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have v8 : (v + 8#64).toNat = v.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have dw : bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) = dom := by
    rw [show (0x80064d08#64 : BitVec 64).toNat = camlStateGlobal.toNat by decide]; exact h.domWord
  have st : (0x80064d08#64 : BitVec 64).toNat = 2147896584 := by decide
  have lk : (0x80064b58#64 : BitVec 64).toNat = 2147896152 := by decide
  let R0 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else if n = 10 then v else
    if n = 11 then str else if n = 12 then ofs else if n = 13 then len else (gpr c n).getD 0
  have hR : R0 2 = sp := rfl
  -- every stack-relative address of the prologue's log, and the local-roots word
  have norm : ∀ k ∈ [152, 120, 104, 168, 144, 128, 16, 24, 8, 32, 48, 40, 56, 64, 72, 80],
      WriteWindow (R0 2 - 176#64 + BitVec.ofNat 64 k) 8 := by
    intro k hk
    have hk' : k + 8 ≤ 176 ∧ k % 8 = 0 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; omega
    exact frame_window (b := sp.toNat) rfl (by omega) (by omega) hk'.1 (by omega)
  have w0 : WriteWindow (R0 2 - 176#64) 8 := frame_window0 (b := sp.toNat) rfl (by omega) (by omega) (by decide) (by omega)
  have roots : WriteWindow (dom + 288#64) 8 := arena_write (ch := dom.toNat) (k := 288) rfl (by omega) (by omega) (by omega)
  have domR : ReadWindow (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64) 8 := by
    rw [dw]; exact roots.read
  have domW : WriteWindow (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64) 8 := by
    rw [dw]; exact roots
  have valR : ReadWindow (R0 10 + 8#64) 8 := arena_read (ch := v.toNat) (k := 8) rfl (by omega) (by omega)
  have logDom : (bytesVal .ld ((Flush.MlOutputBytes.pro_loads c.σ.mem R0).getD 0 []) + 288#64).toNat =
      dom.toNat + 288 := by
    show (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64).toNat = _
    rw [dw, r288]
  -- apartness of a word from (a prefix of) the prologue's log
  have apart := fun (j a : Nat) (ha : a + 8 ≤ F ∨ F + 176 ≤ a)
      (hd : a + 8 ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ a) =>
    (show OutLRange ((Flush.MlOutputBytes.proLog R0 (Flush.MlOutputBytes.pro_loads c.σ.mem R0)).take j) a 8 by
      apply outLRange_of_each
      intro e he
      have := List.mem_of_mem_take he
      simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.mem_cons, List.mem_nil_iff, or_false,
        hR, off, offz, logDom] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> dsimp only <;> omega)
  have apart6 := fun (a : Nat) (ha : a + 8 ≤ F ∨ F + 176 ≤ a) =>
    (show OutLRange ((Flush.MlOutputBytes.proLog R0 (Flush.MlOutputBytes.pro_loads c.σ.mem R0)).take 6) a 8 by
      simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.take_succ_cons, List.take_zero, OutLRange,
        hR, off]
      and_intros <;> first | exact True.intro | omega)
  have P0 := Flush.MlOutputBytes.pro_fast c R0
    ⟨h.good, h.image, h.minstret, h.raReg, h.aligned, h.tick⟩
    ⟨h.raReg, h.stack, present 9 (by simp), h.valReg, h.strReg, h.ofsReg, h.lenReg, present 18 (by simp),
      present 20 (by simp), present 21 (by simp), present 23 (by simp), True.intro⟩
    (norm 152 (by simp)) (norm 120 (by simp)) (norm 104 (by simp)) (norm 168 (by simp)) (norm 144 (by simp))
    (norm 128 (by simp))
    (apart6 _ (by rw [st]; omega)) (apart6 _ (by rw [lk]; omega))
    domR (by rw [dw, r288]; exact apart6 _ (by omega))
    (norm 16 (by simp)) (norm 24 (by simp)) (norm 8 (by simp)) w0 (norm 32 (by simp)) domW
    (norm 48 (by simp)) (norm 40 (by simp)) (norm 56 (by simp)) (norm 64 (by simp)) (norm 72 (by simp))
    (norm 80 (by simp)) valR (by show OutLRange _ (v + 8#64).toNat 8; rw [v8]; exact apart 18 _ (by omega) (by omega))
    ⟨outLRange_of_each fun e he => by
        simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.mem_cons, List.mem_nil_iff, or_false,
          hR, off, offz, logDom] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> dsimp only <;> omega,
     outLRange_of_each fun e he => by
        simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.mem_cons, List.mem_nil_iff, or_false,
          hR, off, offz, logDom] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> dsimp only <;> omega⟩
    (by
      show guardB .BEQ (bytesVal .ld (read8 c.σ.mem (0x80064b58#64).toNat)) 0#64 = true
      have := h.lockNull
      rw [show channelLock.toNat = 2147896152 by decide] at this
      rw [lk, this]; decide)
  obtain ⟨d1, run1, p1⟩ := P0.run c ⟨entry, rfl⟩
  have mem1 : d1.σ.mem = writeLog c.σ.mem
      (Flush.MlOutputBytes.proLog R0 (Flush.MlOutputBytes.pro_loads c.σ.mem R0)) := p1.memory
  have back := fun (i k : Nat) (hk : k ≤ 176) (w : BitVec 64)
      (sel : (Flush.MlOutputBytes.proLog R0 (Flush.MlOutputBytes.pro_loads c.σ.mem R0))[i]? =
        some ((sp - 176#64 + BitVec.ofNat 64 k).toNat, 8, w))
      (after : OutLRange ((Flush.MlOutputBytes.proLog R0 (Flush.MlOutputBytes.pro_loads c.σ.mem R0)).drop (i + 1))
        (sp - 176#64 + BitVec.ofNat 64 k).toNat 8) =>
    (show bytesVal .ld (read8 d1.σ.mem (sp - 176#64 + BitVec.ofNat 64 k).toNat) = w by
      rw [mem1, read8_value]
      exact OCaml.Vm.Gc.word_writeLog_at _ _ i _ _ sel after)
  refine ⟨d1, run1, p1.good, p1.image, p1.minstret, p1.tick, p1.toEffectPost.htifIdle h.idle, p1.pc,
    gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl,
    gholds_lookup _ p1.regs rfl, gholds_lookup _ p1.regs rfl, ?_, ?_, gholds_lookup _ p1.regs rfl,
    gholds_lookup _ p1.regs rfl, fun n lo hi hn => p1.toEffectPost.gpr_frame (by decide) n lo hi hn,
    by unfold Vsa.Machine.output; rw [p1.output], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, GprsKept.of_pins p1 (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.pro_regs])⟩
  · have l : gpr d1 18 = some (bytesVal .ld (read8 c.σ.mem (R0 10 + 8#64).toNat)) := gholds_lookup _ p1.regs rfl
    rw [l]; exact congrArg some h.chanPtr
  · have l : gpr d1 20 = some (bytesVal .ld (read8 c.σ.mem
        (bytesVal .ld (read8 c.σ.mem (0x80064d08#64).toNat) + 288#64).toNat)) := gholds_lookup _ p1.regs rfl
    rw [l, dw, h.rootsWord]
  · intro x a b
    rw [mem1, writeLog_out _ _ _ (outL_of_each fun e he => by
      simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.mem_cons, List.mem_nil_iff, or_false,
        hR, off, offz, logDom] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> dsimp only <;> omega)]
  · exact back 3 168 (by decide) _ rfl (by simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.drop, OutLRange, hR, off, offz, logDom]; and_intros <;> first | exact True.intro | omega)
  · exact back 0 152 (by decide) _ rfl (by simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.drop, OutLRange, hR, off, offz, logDom]; and_intros <;> first | exact True.intro | omega)
  · exact back 4 144 (by decide) _ rfl (by simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.drop, OutLRange, hR, off, offz, logDom]; and_intros <;> first | exact True.intro | omega)
  · exact back 5 128 (by decide) _ rfl (by simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.drop, OutLRange, hR, off, offz, logDom]; and_intros <;> first | exact True.intro | omega)
  · exact back 1 120 (by decide) _ rfl (by simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.drop, OutLRange, hR, off, offz, logDom]; and_intros <;> first | exact True.intro | omega)
  · exact back 2 104 (by decide) _ rfl (by simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.drop, OutLRange, hR, off, offz, logDom]; and_intros <;> first | exact True.intro | omega)
  · exact back 6 16 (by decide) _ rfl (by simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.drop, OutLRange, hR, off, offz, logDom]; and_intros <;> first | exact True.intro | omega)
  · rw [mem1, read8_value, show (dom + 288#64).toNat =
      (bytesVal .ld ((Flush.MlOutputBytes.pro_loads c.σ.mem R0).getD 0 []) + 288#64).toNat by rw [logDom, r288]]
    apply OCaml.Vm.Gc.word_writeLog_at _ _ 11 _ _ rfl
    simp (disch := decide) only [Flush.MlOutputBytes.proLog, List.drop, OutLRange, hR, off, offz, logDom]
    and_intros <;> first | exact True.intro | omega

/-- `caml_ml_output_bytes` at its unbuffered-flag test (`0x80016664`): the
frame base in `sp`, the channel in `s2`, the old local root in `s4`,
`Caml_state`'s address in `s5`, the saved registers in the frame. -/
structure ObExit (ra sp ch dom lr lk s1v s2v s4v s5v s7v : BitVec 64) (d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ w, d.σ.regs.get? Register.minstret = some w
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some 0x80016664#64
  link : gpr d 1 = some lk
  linkAligned : lk.toNat % 4 = 0
  stack : gpr d 2 = some (sp - 176#64)
  a0 : ∃ w, gpr d 10 = some w
  chReg : gpr d 18 = some ch
  lrReg : gpr d 20 = some lr
  stateReg : gpr d 21 = some 0x80064d08#64
  flags : bytesVal .lw (read8 d.σ.mem (ch + 68#64).toNat) &&& 16#64 = 0#64
  unlockNull : bytesVal .ld (read8 d.σ.mem (0x80064b50#64).toNat) = 0#64
  domain : bytesVal .ld (read8 d.σ.mem (0x80064d08#64).toNat) = dom
  savedRa : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 168#64).toNat) = ra
  savedS1 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 152#64).toNat) = s1v
  savedS2 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 144#64).toNat) = s2v
  savedS4 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 128#64).toNat) = s4v
  savedS5 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 120#64).toNat) = s5v
  savedS7 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 104#64).toNat) = s7v

/-- Return from `caml_ml_output_bytes`: `Val_unit`, `local_roots` restored,
the saved registers reloaded, nothing else written since the flag test. -/
structure ObRet (ra sp dom lr s1v s2v s4v s5v s7v : BitVec 64) (d e : Config) : Prop where
  good : GoodState e.σ
  image : ExecutableImage e
  minstret : ∃ w, e.σ.regs.get? Register.minstret = some w
  tick : e.tick < 2
  idle : e.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf e = some ra
  raReg : gpr e 1 = some ra
  result : gpr e 10 = some 1#64
  stack : gpr e 2 = some sp
  s1 : gpr e 9 = some s1v
  s2 : gpr e 18 = some s2v
  s4 : gpr e 20 = some s4v
  s5 : gpr e 21 = some s5v
  s7 : gpr e 23 = some s7v
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 9, 10, 15, 18, 20, 21, 23] → gpr e n = gpr d n
  output : Vsa.Machine.output e.σ = Vsa.Machine.output d.σ
  roots : bytesVal .ld (read8 e.σ.mem (dom + 288#64).toNat) = lr
  frame : ∀ x, (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) → (e.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0
  gprs : GprsKept d e

theorem ob_exit {ra sp ch dom lr lk s1v s2v s4v s5v s7v : BitVec 64} {v : Nat} {d : Config}
    (geo : ConsoleGeometry sp.toNat ch.toNat dom.toNat v 65536) (aligned : ra.toNat % 4 = 0)
    (E : ObExit ra sp ch dom lr lk s1v s2v s4v s5v s7v d) :
    ∃ e, Steps d e ∧ ObRet ra sp dom lr s1v s2v s4v s5v s7v d e := by
  have G := geo.lits
  have C := consoleLits
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned; have l4 := G.chanHigh; have l5 := G.chanLow
  have l7 := G.domLow; have l8 := G.domHigh; have l9 := G.domAligned
  have T := C.textEnd; have Rd := C.rodataEnd
  have tb : 0x80000000 ≤ Image.textBase := by decide
  have rb : 0x80000000 ≤ Image.rodataBase := by decide
  obtain ⟨F, hF⟩ : ∃ F, sp.toNat = F + 176 := ⟨sp.toNat - 176, by omega⟩
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  obtain ⟨w0, hw0⟩ := E.a0
  -- the unbuffered flag is clear
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then lk else if n = 10 then w0 else ch
  obtain ⟨d1, run1, p1⟩ := (Flush.MlOutputBytes.buffered_fast d R1
    ⟨E.good, E.image, E.minstret, E.link, E.linkAligned, E.tick⟩ ⟨E.link, hw0, E.chReg, True.intro⟩
    (arena_read (ch := ch.toNat) (k := 68) rfl (by omega) (by omega))
    (by show guardB .BNE (bytesVal .lw (read8 d.σ.mem (ch + 68#64).toNat) &&& 16#64) 0#64 = false
        rw [E.flags]; decide)).run d ⟨E.pc, rfl⟩
  have keep1 := fun n (hn : n ≠ 15) (lo : 1 ≤ n) (hi : n ≤ 31) =>
    p1.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn)
  have mem1 : d1.σ.mem = d.σ.mem := by rw [p1.memory]; rfl
  -- no unlock hook
  obtain ⟨d2, run2, p2⟩ := (Flush.MlOutputBytes.unlock_fast d1 R1
    ⟨p1.good, p1.image, p1.minstret, (keep1 1 (by decide) (by decide) (by decide)).trans E.link,
      E.linkAligned, p1.tick⟩
    ⟨(keep1 1 (by decide) (by decide) (by decide)).trans E.link, (keep1 10 (by decide) (by decide) (by decide)).trans hw0,
      True.intro⟩
    (by show guardB .BEQ (bytesVal .ld (read8 d1.σ.mem (0x80064b50#64).toNat)) 0#64 = true
        rw [mem1, E.unlockNull]; decide)).run d1 ⟨p1.pc, rfl⟩
  have keep2 := fun n (hn : n ≠ 15) (lo : 1 ≤ n) (hi : n ≤ 31) =>
    (p2.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn)).trans (keep1 n hn lo hi)
  have mem2 : d2.σ.mem = d.σ.mem := by rw [p2.memory, mem1]; rfl
  -- restore local_roots, reload the saves, return
  let R2 : Nat → BitVec 64 := fun n => if n = 1 then lk else if n = 2 then sp - 176#64 else
    if n = 20 then lr else 0x80064d08#64
  have off : ∀ k, k ≤ 176 → (R2 2 + BitVec.ofNat 64 k).toNat = F + k := by
    intro k hk; show (sp - 176#64 + BitVec.ofNat 64 k).toNat = F + k
    rw [BitVec.toNat_add, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have dw : bytesVal .ld (read8 d2.σ.mem (R2 21).toNat) = dom := by rw [mem2]; exact E.domain
  have logDom : (bytesVal .ld ((Flush.MlOutputBytes.ret_loads d2.σ.mem R2).getD 0 []) + 288#64).toNat =
      dom.toNat + 288 := by
    show (bytesVal .ld (read8 d2.σ.mem (R2 21).toNat) + 288#64).toNat = _
    rw [dw, r288]
  have apart := fun (k : Nat) (hk : k + 8 ≤ 176) =>
    (show OutLRange ((Flush.MlOutputBytes.retLog R2 (Flush.MlOutputBytes.ret_loads d2.σ.mem R2)).take 1)
        (R2 2 + BitVec.ofNat 64 k).toNat 8 by
      simp only [Flush.MlOutputBytes.retLog, List.take_succ_cons, List.take_zero, OutLRange, logDom, off k (by omega)]
      and_intros <;> first | exact True.intro | omega)
  have slot := fun (k : Nat) (hk : k + 8 ≤ 176) (w : BitVec 64)
      (hw : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + BitVec.ofNat 64 k).toNat) = w) =>
    (show bytesVal .ld (read8 d2.σ.mem (R2 2 + BitVec.ofNat 64 k).toNat) = w by rw [mem2]; exact hw)
  have rd := fun (k : Nat) (hk : k + 8 ≤ 176) (hk8 : k % 8 = 0) =>
    (show ReadWindow (R2 2 + BitVec.ofNat 64 k) 8 from
      (frame_window (b := sp.toNat) (s := sp) rfl (by omega) (by omega) (k := k) (off := 176) (by omega)
        (by omega)).read)
  obtain ⟨e, run3, p3⟩ := (Flush.MlOutputBytes.ret_fast d2 ra R2
    ⟨p2.good, p2.image, p2.minstret, (keep2 1 (by decide) (by decide) (by decide)).trans E.link,
      E.linkAligned, p2.tick⟩
    ⟨(keep2 2 (by decide) (by decide) (by decide)).trans E.stack, (keep2 20 (by decide) (by decide) (by decide)).trans E.lrReg,
      (keep2 21 (by decide) (by decide) (by decide)).trans E.stateReg, True.intro⟩
    (show ReadWindow (0x80064d08#64) 8 from ⟨by decide, by decide, Or.inr (by decide)⟩)
    (by rw [dw]; exact arena_write (ch := dom.toNat) (k := 288) rfl (by omega) (by omega) (by omega))
    (rd 168 (by decide) (by decide)) (apart 168 (by decide)) (rd 152 (by decide) (by decide)) (apart 152 (by decide))
    (rd 144 (by decide) (by decide)) (apart 144 (by decide)) (rd 128 (by decide) (by decide)) (apart 128 (by decide))
    (rd 120 (by decide) (by decide)) (apart 120 (by decide)) (rd 104 (by decide) (by decide)) (apart 104 (by decide))
    ⟨by simp only [Flush.MlOutputBytes.retLog, OutLRange, logDom]; and_intros <;> first | exact True.intro | omega,
     by simp only [Flush.MlOutputBytes.retLog, OutLRange, logDom]; and_intros <;> first | exact True.intro | omega⟩
    (slot 168 (by decide) ra E.savedRa) aligned).run d2 ⟨p2.pc, rfl⟩
  have mem3 : e.σ.mem = writeLog d2.σ.mem
      (Flush.MlOutputBytes.retLog R2 (Flush.MlOutputBytes.ret_loads d2.σ.mem R2)) := p3.memory
  have load := fun (n k : Nat) (hk : k + 8 ≤ 176) (w : BitVec 64)
      (l : gpr e n = some (bytesVal .ld (read8 d2.σ.mem (R2 2 + BitVec.ofNat 64 k).toNat)))
      (hw : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + BitVec.ofNat 64 k).toNat) = w) =>
    (show gpr e n = some w by rw [l, slot k hk w hw])
  refine ⟨e, run1.trans (run2.trans run3), p3.good, p3.image, p3.minstret, p3.tick,
    p3.toEffectPost.htifIdle (p2.toEffectPost.htifIdle (p1.toEffectPost.htifIdle E.idle)), p3.pc,
    load 1 168 (by decide) ra (gholds_lookup _ p3.regs rfl) E.savedRa, gholds_lookup _ p3.regs rfl, ?_,
    load 9 152 (by decide) _ (gholds_lookup _ p3.regs rfl) E.savedS1,
    load 18 144 (by decide) _ (gholds_lookup _ p3.regs rfl) E.savedS2,
    load 20 128 (by decide) _ (gholds_lookup _ p3.regs rfl) E.savedS4,
    load 21 120 (by decide) _ (gholds_lookup _ p3.regs rfl) E.savedS5,
    load 23 104 (by decide) _ (gholds_lookup _ p3.regs rfl) E.savedS7, ?_, ?_, ?_, ?_,
    (GprsKept.of_pins p1 (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.buffered_regs])).trans ((GprsKept.of_pins p2 (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.unlock_regs])).trans (GprsKept.of_pins p3 (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.ret_regs])))⟩
  · have l : gpr e 2 = some (R2 2 + 176#64) := gholds_lookup _ p3.regs rfl
    rw [l]; simp only [R2, ↓reduceIte, Nat.reduceEqDiff, BitVec.sub_add_cancel]
  · intro n lo hi hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    rw [p3.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega), keep2 n (by omega) lo hi]
  · have o2 := p2.output; have o1 := p1.output
    unfold Vsa.Machine.output at *
    rw [p3.output, o2, o1]
  · rw [mem3, read8_value, show (dom + 288#64).toNat =
      (bytesVal .ld ((Flush.MlOutputBytes.ret_loads d2.σ.mem R2).getD 0 []) + 288#64).toNat by rw [logDom, r288]]
    exact OCaml.Vm.Gc.word_writeLog_at _ _ 0 _ _ rfl trivial
  · intro x hx
    rw [mem3, writeLog_out _ _ _ (by simp only [Flush.MlOutputBytes.retLog, OutL, logDom]; exact ⟨by omega, trivial⟩), mem2]

/-- The untagged int argument: `srai 1` of `tag64 n` is `n` sign-extended. -/
theorem untag_shift (n : BitVec 63) : Functions.shift_bits_right_arith (tag64 n) 1#6 = n.signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : Sail.BitVec.toNatInt (1#6) = 1 := by decide
  simp [h1, Functions.shift_bits_right_arith, tag64, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend]
  by_cases small : i < 63
  · simp [small, show 1 + i < 64 by omega, show i < 64 by omega]
  · have i63 : i = 63 := by omega
    subst i63
    simp only [BitVec.msb_eq_getLsbD_last, BitVec.getMsbD_eq_getLsbD]
    simp [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_signExtend]

/-- `caml_ml_output_bytes` at its loop head (`t = 0x80016600`) or its exit
(`t = 0x80016658`): `rem` bytes left
at buffer offset `pos`, the frame and the saved registers as the prologue and
`prep` left them, memory outside the console footprint and the frame unchanged
since the entry `c0`. -/
structure ObHead (t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos : BitVec 64)
    (c0 d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ w, d.σ.regs.get? Register.minstret = some w
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some t
  link : ∃ lk, gpr d 1 = some lk ∧ lk.toNat % 4 = 0
  stack : gpr d 2 = some (sp - 176#64)
  a0 : ∃ w, gpr d 10 = some w
  remReg : gpr d 9 = some rem
  posReg : gpr d 23 = some pos
  chReg : gpr d 18 = some ch
  lrReg : gpr d 20 = some lr
  stateReg : gpr d 21 = some 0x80064d08#64
  maxReg : gpr d 22 = some 2147483647#64
  kept : ∀ n ∈ [24, 25, 26, 27], gpr d n = gpr c0 n
  savedRa : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 168#64).toNat) = ra
  savedS1 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 152#64).toNat) = s1v
  savedS2 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 144#64).toNat) = s2v
  savedS4 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 128#64).toNat) = s4v
  savedS5 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 120#64).toNat) = s5v
  savedS7 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 104#64).toNat) = s7v
  savedStr : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 16#64).toNat) = str
  savedS0 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 160#64).toNat) = s0v
  savedS3 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 136#64).toNat) = s3v
  savedS6 : bytesVal .ld (read8 d.σ.mem (sp - 176#64 + 112#64).toNat) = s6v
  roots : bytesVal .ld (read8 d.σ.mem (dom + 288#64).toNat) = sp - 176#64 + 32#64
  frame : ∀ x, (x < sp.toNat - 512 ∨ sp.toNat ≤ x) → (x < 0x80064d48 ∨ 0x80064d48 + 4 ≤ x) →
    (x < 0x80064668 ∨ 0x80064668 + 4 ≤ x) → (x < ch.toNat + 8 ∨ ch.toNat + 16 ≤ x) →
    (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → (x < ch.toNat + 72 ∨ ch.toNat + 72 + 65536 ≤ x) →
    (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) → (d.σ.mem[x]?).getD 0 = (c0.σ.mem[x]?).getD 0

/-- A word apart from the frame and the local-roots word reads as at entry. -/
theorem ObPro.read {ra sp v str ofs len ch dom lr c d} (P : ObPro ra sp v str ofs len ch dom lr c d) {a : Nat}
    (st : a + 8 ≤ sp.toNat - 176 ∨ sp.toNat ≤ a) (ro : a + 8 ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ a) :
    read8 d.σ.mem a = read8 c.σ.mem a :=
  read8_same fun i hi => P.outside _ (by omega) (by omega)

/-- A register-free block: memory, console and every register unchanged. -/
structure ObQuiet (d e : Config) : Prop where
  memory : e.σ.mem = d.σ.mem
  output : Vsa.Machine.output e.σ = Vsa.Machine.output d.σ
  regs : ∀ n, 1 ≤ n → n ≤ 31 → gpr e n = gpr d n
  gprs : GprsKept d e

/-- A non-positive length: straight to the flag test. -/
theorem ob_none {ra sp v str ofs len ch dom lr c d} (h : ObInput ra sp v str ofs len ch dom lr c)
    (P : ObPro ra sp v str ofs len ch dom lr c d)
    (neg : guardB .BGE 0#64 (Functions.shift_bits_right_arith len 1#6) = true) :
    ∃ e, Steps d e ∧ ObExit ra sp ch dom lr ra ((gpr c 9).getD 0) ((gpr c 18).getD 0) ((gpr c 20).getD 0)
      ((gpr c 21).getD 0) ((gpr c 23).getD 0) e ∧ ObQuiet d e := by
  have G := h.geo.lits
  have l1 := G.low; have l2 := G.high; have l5 := G.chanLow; have l4 := G.chanHigh; have cd := G.chanDom
  have l7 := G.domLow; have l8 := G.domHigh
  let R : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 9 then
    Functions.shift_bits_right_arith len 1#6 else v
  obtain ⟨e, run, p⟩ := (Flush.MlOutputBytes.none_fast d R ⟨P.good, P.image, P.minstret, P.raReg, h.aligned, P.tick⟩
    ⟨P.raReg, P.lenReg, P.valReg, True.intro⟩ neg).run d ⟨P.pc, rfl⟩
  have keep := fun n (lo : 1 ≤ n) (hi : n ≤ 31) => p.toEffectPost.gpr_frame (by decide) n lo hi (by simp)
  have mem : e.σ.mem = d.σ.mem := by rw [p.memory]; rfl
  have c68 : (ch + 68#64).toNat = ch.toNat + 68 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨e, run, ⟨p.good, p.image, p.minstret, p.tick, p.toEffectPost.htifIdle P.idle, p.pc,
    (keep 1 (by decide) (by decide)).trans P.raReg, h.aligned, (keep 2 (by decide) (by decide)).trans P.stack,
    ⟨v, (keep 10 (by decide) (by decide)).trans P.valReg⟩, (keep 18 (by decide) (by decide)).trans P.chReg,
    (keep 20 (by decide) (by decide)).trans P.lrReg, (keep 21 (by decide) (by decide)).trans P.stateReg,
    ?_, ?_, ?_, by rw [mem]; exact P.savedRa, by rw [mem]; exact P.savedS1, by rw [mem]; exact P.savedS2,
    by rw [mem]; exact P.savedS4, by rw [mem]; exact P.savedS5, by rw [mem]; exact P.savedS7⟩,
    ⟨mem, by unfold Vsa.Machine.output; rw [p.output], keep,
      ⟨fun n lo hi q => (show (gpr e n).isSome by rw [keep n lo hi]; exact q),
        keep 3 (by decide) (by decide)⟩⟩⟩
  · rw [mem, P.read (by rw [c68]; omega) (by rw [c68]; omega)]; exact h.flagsClear
  · rw [mem, show (0x80064b50#64 : BitVec 64).toNat = channelUnlock.toNat by decide,
      P.read (by rw [consoleLits.unlock]; omega) (by rw [consoleLits.unlock]; omega)]
    exact h.unlockNull
  · rw [mem, show (0x80064d08#64 : BitVec 64).toNat = camlStateGlobal.toNat by decide,
      P.read (by rw [consoleLits.state]; omega) (by rw [consoleLits.state]; omega)]
    exact h.domWord

/-- What entering the copy loop kept: register presence, the console, and
memory outside the frame and the local-roots word. -/
structure ObEntered (sp dom : BitVec 64) (c d e : Config) : Prop where
  gprs : GprsKept d e
  output : Vsa.Machine.output e.σ = Vsa.Machine.output d.σ
  outside : ∀ x, (x < sp.toNat - 176 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
    (e.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0

/-- A positive length: save `s0`, `s3`, `s6`, untag the offset, and enter the
copy loop. -/
theorem ob_go {ra sp v str ofs len ch dom lr c d} (h : ObInput ra sp v str ofs len ch dom lr c)
    (P : ObPro ra sp v str ofs len ch dom lr c d)
    (pos : guardB .BGE 0#64 (Functions.shift_bits_right_arith len 1#6) = false) :
    ∃ e, Steps d e ∧ ObHead 0x80016600#64 ra sp ch dom lr str ((gpr c 9).getD 0) ((gpr c 18).getD 0) ((gpr c 20).getD 0)
      ((gpr c 21).getD 0) ((gpr c 23).getD 0) ((gpr c 8).getD 0) ((gpr c 19).getD 0) ((gpr c 22).getD 0)
      (Functions.shift_bits_right_arith len 1#6) (Functions.shift_bits_right_arith ofs 1#6) c e ∧
      ObEntered sp dom c d e := by
  have G := h.geo.lits
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned; have l5 := G.chanLow; have l4 := G.chanHigh
  have cd := G.chanDom; have l7 := G.domLow; have l8 := G.domHigh
  have C := consoleLits
  have T := C.textEnd; have Rd := C.rodataEnd
  have tb : 0x80000000 ≤ Image.textBase := by decide
  have rb : 0x80000000 ≤ Image.rodataBase := by decide
  obtain ⟨F, hF⟩ : ∃ F, sp.toNat = F + 176 := ⟨sp.toNat - 176, by omega⟩
  have present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr c n = some ((gpr c n).getD 0) := by
    intro n hn
    have := h.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 9 then
    Functions.shift_bits_right_arith len 1#6 else v
  obtain ⟨d1, run1, p1⟩ := (Flush.MlOutputBytes.go_fast d R1 ⟨P.good, P.image, P.minstret, P.raReg, h.aligned, P.tick⟩
    ⟨P.raReg, P.lenReg, P.valReg, True.intro⟩ pos).run d ⟨P.pc, rfl⟩
  have keep1 := fun n (lo : 1 ≤ n) (hi : n ≤ 31) => p1.toEffectPost.gpr_frame (by decide) n lo hi (by simp)
  have mem1 : d1.σ.mem = d.σ.mem := by rw [p1.memory]; rfl
  have at1 := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [2, 6, 9, 14, 15, 16, 17, 18, 20, 21, 23, 28, 29, 30]) =>
    (keep1 n lo hi).trans (P.kept n lo hi hn)
  let R2 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp - 176#64 else if n = 10 then v else
    if n = 23 then ofs else (gpr c n).getD 0
  have off : ∀ k, k ≤ 176 → (R2 2 + BitVec.ofNat 64 k).toNat = F + k := by
    intro k hk; show (sp - 176#64 + BitVec.ofNat 64 k).toNat = F + k
    rw [BitVec.toNat_add, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have wr := fun (k : Nat) (hk : k + 8 ≤ 176) (hk8 : k % 8 = 0) =>
    (show WriteWindow (R2 2 + BitVec.ofNat 64 k) 8 from
      frame_window (b := sp.toNat) (s := sp) rfl (by omega) (by omega) (k := k) (off := 176) (by omega) (by omega))
  obtain ⟨e, run2, p2⟩ := (Flush.MlOutputBytes.prep_fast d1 R2
    ⟨p1.good, p1.image, p1.minstret, (keep1 1 (by decide) (by decide)).trans P.raReg, h.aligned, p1.tick⟩
    ⟨(keep1 1 (by decide) (by decide)).trans P.raReg, (keep1 2 (by decide) (by decide)).trans P.stack,
      (at1 8 (by decide) (by decide) (by simp)).trans (present 8 (by simp)), (keep1 10 (by decide) (by decide)).trans P.valReg,
      (at1 19 (by decide) (by decide) (by simp)).trans (present 19 (by simp)),
      (at1 22 (by decide) (by decide) (by simp)).trans (present 22 (by simp)),
      (keep1 23 (by decide) (by decide)).trans P.ofsReg, True.intro⟩
    (wr 112 (by decide) (by decide)) (wr 160 (by decide) (by decide)) (wr 136 (by decide) (by decide))
    ⟨by simp only [Flush.MlOutputBytes.prepLog, OutLRange, off 112 (by decide), off 160 (by decide),
          off 136 (by decide)]; and_intros <;> first | exact True.intro | omega,
     by simp only [Flush.MlOutputBytes.prepLog, OutLRange, off 112 (by decide), off 160 (by decide),
          off 136 (by decide)]; and_intros <;> first | exact True.intro | omega⟩).run d1 ⟨p1.pc, rfl⟩
  have mem2 : e.σ.mem = writeLog d.σ.mem (Flush.MlOutputBytes.prepLog R2 (Flush.MlOutputBytes.prep_loads d1.σ.mem R2)) := by
    rw [p2.memory, mem1]
  have keep2 := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [22, 23]) => p2.toEffectPost.gpr_frame (by decide) n lo hi hn
  have outPrep : ∀ y, (y < F + 112 ∨ F + 120 ≤ y) → (y < F + 160 ∨ F + 168 ≤ y) → (y < F + 136 ∨ F + 144 ≤ y) →
      OutL (Flush.MlOutputBytes.prepLog R2 (Flush.MlOutputBytes.prep_loads d1.σ.mem R2)) y := by
    intro y a b z
    simp only [Flush.MlOutputBytes.prepLog, OutL, off 112 (by decide), off 160 (by decide), off 136 (by decide)]
    refine ⟨?_, ?_, ?_, trivial⟩ <;> omega
  have miss : ∀ a, (a + 8 ≤ F + 112 ∨ F + 120 ≤ a) → (a + 8 ≤ F + 160 ∨ F + 168 ≤ a) →
      (a + 8 ≤ F + 136 ∨ F + 144 ≤ a) → read8 e.σ.mem a = read8 d.σ.mem a := fun a x y z => by
    rw [mem2]
    exact read8_same fun i hi => by rw [writeLog_out _ _ _ (outPrep (a + i) (by omega) (by omega) (by omega))]
  have slot := fun (k : Nat) (hk : k + 8 ≤ 176) => (show (sp - 176#64 + BitVec.ofNat 64 k).toNat = F + k from off k (by omega))
  have prepRead := fun (i k : Nat) (hk : k + 8 ≤ 176) (w : BitVec 64)
      (sel : (Flush.MlOutputBytes.prepLog R2 (Flush.MlOutputBytes.prep_loads d1.σ.mem R2))[i]? =
        some ((sp - 176#64 + BitVec.ofNat 64 k).toNat, 8, w))
      (after : OutLRange ((Flush.MlOutputBytes.prepLog R2 (Flush.MlOutputBytes.prep_loads d1.σ.mem R2)).drop (i + 1))
        (sp - 176#64 + BitVec.ofNat 64 k).toNat 8) =>
    (show bytesVal .ld (read8 e.σ.mem (sp - 176#64 + BitVec.ofNat 64 k).toNat) = w by
      rw [mem2, read8_value]; exact OCaml.Vm.Gc.word_writeLog_at _ _ i _ _ sel after)
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨e, run1.trans run2, ⟨p2.good, p2.image, p2.minstret, p2.tick,
    p2.toEffectPost.htifIdle (p1.toEffectPost.htifIdle P.idle), p2.pc,
    ⟨ra, (keep2 1 (by decide) (by decide) (by simp)).trans ((keep1 1 (by decide) (by decide)).trans P.raReg), h.aligned⟩,
    (keep2 2 (by decide) (by decide) (by simp)).trans ((keep1 2 (by decide) (by decide)).trans P.stack),
    ⟨v, (keep2 10 (by decide) (by decide) (by simp)).trans ((keep1 10 (by decide) (by decide)).trans P.valReg)⟩,
    (keep2 9 (by decide) (by decide) (by simp)).trans ((keep1 9 (by decide) (by decide)).trans P.lenReg),
    gholds_lookup _ p2.regs rfl,
    (keep2 18 (by decide) (by decide) (by simp)).trans ((keep1 18 (by decide) (by decide)).trans P.chReg),
    (keep2 20 (by decide) (by decide) (by simp)).trans ((keep1 20 (by decide) (by decide)).trans P.lrReg),
    (keep2 21 (by decide) (by decide) (by simp)).trans ((keep1 21 (by decide) (by decide)).trans P.stateReg),
    gholds_lookup _ p2.regs rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨(GprsKept.of_pins p1 (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.go_regs])).trans (GprsKept.of_pins p2 (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.prep_regs])),
    by unfold Vsa.Machine.output; rw [p2.output, p1.output], fun x st ro => by
      rw [mem2, writeLog_out _ _ _ (outPrep x (by omega) (by omega) (by omega))]
      exact P.outside x st ro⟩⟩
  · intro n hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rw [keep2 n (by omega) (by omega) (by simp; omega), at1 n (by omega) (by omega) (by simp; omega)]
  · rw [miss _ (by rw [slot 168 (by decide)]; omega) (by rw [slot 168 (by decide)]; omega)
      (by rw [slot 168 (by decide)]; omega)]; exact P.savedRa
  · rw [miss _ (by rw [slot 152 (by decide)]; omega) (by rw [slot 152 (by decide)]; omega)
      (by rw [slot 152 (by decide)]; omega)]; exact P.savedS1
  · rw [miss _ (by rw [slot 144 (by decide)]; omega) (by rw [slot 144 (by decide)]; omega)
      (by rw [slot 144 (by decide)]; omega)]; exact P.savedS2
  · rw [miss _ (by rw [slot 128 (by decide)]; omega) (by rw [slot 128 (by decide)]; omega)
      (by rw [slot 128 (by decide)]; omega)]; exact P.savedS4
  · rw [miss _ (by rw [slot 120 (by decide)]; omega) (by rw [slot 120 (by decide)]; omega)
      (by rw [slot 120 (by decide)]; omega)]; exact P.savedS5
  · rw [miss _ (by rw [slot 104 (by decide)]; omega) (by rw [slot 104 (by decide)]; omega)
      (by rw [slot 104 (by decide)]; omega)]; exact P.savedS7
  · rw [miss _ (by rw [slot 16 (by decide)]; omega) (by rw [slot 16 (by decide)]; omega)
      (by rw [slot 16 (by decide)]; omega)]; exact P.savedStr
  · exact prepRead 1 160 (by decide) _ rfl (by
      simp only [Flush.MlOutputBytes.prepLog, List.drop, OutLRange, off 160 (by decide), off 136 (by decide),
        slot 160 (by decide)]
      and_intros <;> first | exact True.intro | omega)
  · exact prepRead 2 136 (by decide) _ rfl trivial
  · exact prepRead 0 112 (by decide) _ rfl (by
      simp only [Flush.MlOutputBytes.prepLog, List.drop, OutLRange, off 160 (by decide), off 136 (by decide),
        off 112 (by decide), slot 112 (by decide)]
      and_intros <;> first | exact True.intro | omega)
  · rw [miss _ (by rw [r288]; omega) (by rw [r288]; omega) (by rw [r288]; omega)]; exact P.roots
  · intro x st er rp o k b ro
    rw [mem2, writeLog_out _ _ _ (outPrep x (by omega) (by omega) (by omega))]
    exact P.outside x (by omega) ro

/-- What the loop's exit adds to `ObExit`: `s0`, `s3`, `s6` reloaded, the rest
of the callee-saved registers kept, memory as at the exit. -/
structure ObRestored (s0v s3v s6v : BitVec 64) (c0 d e : Config) : Prop where
  s0 : gpr e 8 = some s0v
  s3 : gpr e 19 = some s3v
  s6 : gpr e 22 = some s6v
  kept : ∀ n ∈ [24, 25, 26, 27], gpr e n = gpr c0 n
  memory : e.σ.mem = d.σ.mem
  output : Vsa.Machine.output e.σ = Vsa.Machine.output d.σ
  gprs : GprsKept d e

/-- Leave the loop: reload `s0`, `s3`, `s6` from the frame. -/
theorem ob_restore {ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos : BitVec 64} {v : Nat}
    {c0 d : Config} (geo : ConsoleGeometry sp.toNat ch.toNat dom.toNat v 65536)
    (H : ObHead 0x80016658#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos c0 d)
    (domain : bytesVal .ld (read8 d.σ.mem (0x80064d08#64).toNat) = dom)
    (unlock : bytesVal .ld (read8 d.σ.mem (0x80064b50#64).toNat) = 0#64)
    (flags : bytesVal .lw (read8 d.σ.mem (ch + 68#64).toNat) &&& 16#64 = 0#64) :
    ∃ e, Steps d e ∧ ObExit ra sp ch dom lr ((gpr e 1).getD 0) s1v s2v s4v s5v s7v e ∧
      ObRestored s0v s3v s6v c0 d e := by
  have G := geo.lits
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned
  obtain ⟨F, hF⟩ : ∃ F, sp.toNat = F + 176 := ⟨sp.toNat - 176, by omega⟩
  obtain ⟨lk, hlk, alk⟩ := H.link
  obtain ⟨w0, hw0⟩ := H.a0
  let R : Nat → BitVec 64 := fun n => if n = 1 then lk else if n = 2 then sp - 176#64 else w0
  have rd := fun (k : Nat) (hk : k + 8 ≤ 176) (hk8 : k % 8 = 0) =>
    (show ReadWindow (R 2 + BitVec.ofNat 64 k) 8 from
      (frame_window (b := sp.toNat) (s := sp) rfl (by omega) (by omega) (k := k) (off := 176) (by omega)
        (by omega)).read)
  obtain ⟨e, run, p⟩ := (Flush.MlOutputBytes.restore_fast d R ⟨H.good, H.image, H.minstret, hlk, alk, H.tick⟩
    ⟨hlk, H.stack, hw0, True.intro⟩ (rd 160 (by decide) (by decide)) (rd 136 (by decide) (by decide))
    (rd 112 (by decide) (by decide))).run d ⟨H.pc, rfl⟩
  have keep := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [8, 19, 22]) => p.toEffectPost.gpr_frame (by decide) n lo hi hn
  have mem : e.σ.mem = d.σ.mem := by rw [p.memory]; rfl
  have l1' : gpr e 1 = some lk := (keep 1 (by decide) (by decide) (by simp)).trans hlk
  refine ⟨e, run, ⟨p.good, p.image, p.minstret, p.tick, p.toEffectPost.htifIdle H.idle, p.pc, ?_, ?_,
    (keep 2 (by decide) (by decide) (by simp)).trans H.stack, ⟨w0, (keep 10 (by decide) (by decide) (by simp)).trans hw0⟩,
    (keep 18 (by decide) (by decide) (by simp)).trans H.chReg, (keep 20 (by decide) (by decide) (by simp)).trans H.lrReg,
    (keep 21 (by decide) (by decide) (by simp)).trans H.stateReg, by rw [mem]; exact flags,
    by rw [mem]; exact unlock, by rw [mem]; exact domain, by rw [mem]; exact H.savedRa, by rw [mem]; exact H.savedS1,
    by rw [mem]; exact H.savedS2, by rw [mem]; exact H.savedS4, by rw [mem]; exact H.savedS5,
    by rw [mem]; exact H.savedS7⟩, ?_, ?_, ?_, ?_, mem, ?_, GprsKept.of_pins p (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.restore_regs])⟩
  · rw [l1']; rfl
  · rw [l1']; exact alk
  · have l : gpr e 8 = some (bytesVal .ld (read8 d.σ.mem (R 2 + 160#64).toNat)) := gholds_lookup _ p.regs rfl
    rw [l]; exact congrArg some H.savedS0
  · have l : gpr e 19 = some (bytesVal .ld (read8 d.σ.mem (R 2 + 136#64).toNat)) := gholds_lookup _ p.regs rfl
    rw [l]; exact congrArg some H.savedS3
  · have l : gpr e 22 = some (bytesVal .ld (read8 d.σ.mem (R 2 + 112#64).toNat)) := gholds_lookup _ p.regs rfl
    rw [l]; exact congrArg some H.savedS6
  · intro n hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rw [keep n (by omega) (by omega) (by simp; omega)]; exact H.kept n (by simp; omega)
  · unfold Vsa.Machine.output; rw [p.output]

/-- **Transport the loop state** to a later configuration that keeps the
frame, the local-roots word and the loop's fixed registers. -/
theorem ObHead.step {t t' ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos rem' pos' : BitVec 64}
    {c0 d e : Config} (H : ObHead t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos c0 d)
    (big : 176 ≤ sp.toNat) (high : sp.toNat < 2 ^ 63) (domHigh : dom.toNat + 296 < 2 ^ 63)
    (good : GoodState e.σ) (image : ExecutableImage e) (minstret : ∃ w, e.σ.regs.get? Register.minstret = some w)
    (tick : e.tick < 2) (idle : e.σ.regs.get? Register.htif_payload_writes = some (0#4))
    (pc : pcOf e = some t') (link : ∃ lk, gpr e 1 = some lk ∧ lk.toNat % 4 = 0) (a0 : ∃ w, gpr e 10 = some w)
    (regs : ∀ n ∈ [2, 18, 20, 21, 22, 24, 25, 26, 27], gpr e n = gpr d n)
    (remReg : gpr e 9 = some rem') (posReg : gpr e 23 = some pos')
    (keepFrame : ∀ x, sp.toNat - 176 ≤ x → x < sp.toNat → (e.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0)
    (keepRoots : ∀ x, dom.toNat + 288 ≤ x → x < dom.toNat + 296 → (e.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0)
    (frame : ∀ x, (x < sp.toNat - 512 ∨ sp.toNat ≤ x) → (x < 0x80064d48 ∨ 0x80064d48 + 4 ≤ x) →
      (x < 0x80064668 ∨ 0x80064668 + 4 ≤ x) → (x < ch.toNat + 8 ∨ ch.toNat + 16 ≤ x) →
      (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → (x < ch.toNat + 72 ∨ ch.toNat + 72 + 65536 ≤ x) →
      (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) → (e.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0) :
    ObHead t' ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem' pos' c0 e := by
  have off : ∀ k, k + 8 ≤ 176 → (sp - 176#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 176 + k := by
    intro k hk; rw [BitVec.toNat_add, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have slot := fun (k : Nat) (hk : k + 8 ≤ 176) =>
    (show read8 e.σ.mem (sp - 176#64 + BitVec.ofNat 64 k).toNat = read8 d.σ.mem (sp - 176#64 + BitVec.ofNat 64 k).toNat from
      read8_same fun i hi => keepFrame _ (by rw [off k hk]; omega) (by rw [off k hk]; omega))
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have rt : read8 e.σ.mem (dom + 288#64).toNat = read8 d.σ.mem (dom + 288#64).toNat :=
    read8_same fun i hi => keepRoots _ (by rw [r288]; omega) (by rw [r288]; omega)
  exact ⟨good, image, minstret, tick, idle, pc, link, (regs 2 (by simp)).trans H.stack, a0, remReg, posReg,
    (regs 18 (by simp)).trans H.chReg, (regs 20 (by simp)).trans H.lrReg, (regs 21 (by simp)).trans H.stateReg,
    (regs 22 (by simp)).trans H.maxReg, fun n hn => (regs n (by simp at hn ⊢; omega)).trans (H.kept n hn),
    by rw [slot 168 (by decide)]; exact H.savedRa, by rw [slot 152 (by decide)]; exact H.savedS1,
    by rw [slot 144 (by decide)]; exact H.savedS2, by rw [slot 128 (by decide)]; exact H.savedS4,
    by rw [slot 120 (by decide)]; exact H.savedS5, by rw [slot 104 (by decide)]; exact H.savedS7,
    by rw [slot 16 (by decide)]; exact H.savedStr, by rw [slot 160 (by decide)]; exact H.savedS0,
    by rw [slot 136 (by decide)]; exact H.savedS3, by rw [slot 112 (by decide)]; exact H.savedS6,
    by rw [rt]; exact H.roots,
    fun x a b c' o k bu ro => (frame x a b c' o k bu ro).trans (H.frame x a b c' o k bu ro)⟩

/-- After a full buffer: what `caml_flush_partial` left in the channel record
and on the console. -/
structure ObWritten (ch off : BitVec 64) (bs : List UInt8) (d e : Config) : Prop where
  curr : bytesVal .ld (read8 e.σ.mem (ch + 24#64).toNat) = ch + 72#64
  offset : bytesVal .ld (read8 e.σ.mem (ch + 8#64).toNat) = off + BitVec.ofNat 64 bs.length
  output : Vsa.Machine.output e.σ = Vsa.Machine.output d.σ ++ bytesToString bs
  gprs : GprsKept d e

/-- **A full buffer written out**: `curr := end`, then `caml_flush_partial`
writes the whole buffer to the console. -/
theorem ob_flushed {ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos free off fd : BitVec 64}
    {v : Nat} {bs : List UInt8} {c0 d : Config}
    (geo : ConsoleGeometry sp.toNat ch.toNat dom.toNat v 65536)
    (H : ObHead 0x80016638#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos c0 d)
    (freeReg : gpr d 19 = some free)
    (rt : ConsoleRuntime d) (hfd : fd = 1#64 ∨ fd = 2#64)
    (fdWord : bytesVal .lw (read8 d.σ.mem ch.toNat) = fd)
    (endWord : bytesVal .ld (read8 d.σ.mem (ch + 16#64).toNat) = ch + 72#64 + 65536#64)
    (offWord : bytesVal .ld (read8 d.σ.mem (ch + 8#64).toNat) = off)
    (len : bs.length = 65536)
    (bytes : ∀ i x, bs[i]? = some x → (d.σ.mem[(ch + 72#64 + BitVec.ofNat 64 i).toNat]?).getD 0 = BitVec.ofNat 8 x.toNat)
    (saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], (gprGet d.σ n).isSome) :
    ∃ e, Steps d e ∧ ObHead 0x80016650#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v (rem - free) pos c0 e ∧
      gpr e 8 = some free ∧ ObWritten ch off bs d e := by
  have G := geo.lits
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned; have l4 := G.chanHigh; have l5 := G.chanLow
  have l6 := G.chanAligned; have l7 := G.domLow; have l8 := G.domHigh; have cd := G.chanDom
  have C := consoleLits
  have T := C.textEnd; have Rd := C.rodataEnd
  have tb : 0x80000000 ≤ Image.textBase := by decide
  have rb : 0x80000000 ≤ Image.rodataBase := by decide
  obtain ⟨lk, hlk, alk⟩ := H.link
  obtain ⟨w0, hw0⟩ := H.a0
  have hc16 : (ch + 16#64).toNat = ch.toNat + 16 := by rw [bv_add_toNat (by omega)]
  have hc24 : (ch + 24#64).toNat = ch.toNat + 24 := by rw [bv_add_toNat (by omega)]
  -- curr := end
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then lk else if n = 9 then rem else if n = 10 then w0 else
    if n = 18 then ch else free
  have within : ∀ e ∈ Flush.MlOutputBytes.filledLog R1 (Flush.MlOutputBytes.filled_loads d.σ.mem R1),
      e.1 = ch.toNat + 24 ∧ e.2.1 = 8 := by
    intro e he
    simp only [Flush.MlOutputBytes.filledLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he; exact ⟨hc24, rfl⟩
  obtain ⟨d1, run1, p1⟩ := (Flush.MlOutputBytes.filled_fast d R1 ⟨H.good, H.image, H.minstret, hlk, alk, H.tick⟩
    ⟨hlk, H.remReg, hw0, H.chReg, freeReg, True.intro⟩
    (arena_read (ch := ch.toNat) (k := 16) rfl (by omega) (by omega))
    (arena_write (ch := ch.toNat) (k := 24) rfl (by omega) (by omega) (by omega))
    ⟨outLRange_of_each fun e he => by obtain ⟨a, b⟩ := within e he; omega,
     outLRange_of_each fun e he => by obtain ⟨a, b⟩ := within e he; omega⟩).run d ⟨H.pc, rfl⟩
  have mem1 : d1.σ.mem = writeLog d.σ.mem (Flush.MlOutputBytes.filledLog R1 (Flush.MlOutputBytes.filled_loads d.σ.mem R1)) :=
    p1.memory
  have out1 : ∀ x, (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) →
      OutL (Flush.MlOutputBytes.filledLog R1 (Flush.MlOutputBytes.filled_loads d.σ.mem R1)) x :=
    fun x hx => outL_of_each fun e he => by obtain ⟨a, b⟩ := within e he; omega
  have keep1 := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [8, 9, 10, 15]) =>
    p1.toEffectPost.gpr_frame (by decide) n lo hi hn
  -- the call
  have J := call_registers_summary Flush.MlOutputBytes.filled_call_shape Flush.MlOutputBytes.filled_call_decode d1
    (Flush.MlOutputBytes.filled_call_pins p1.image) p1.good p1.image p1.tick p1.minstret
    [(10, ch)] ⟨gholds_lookup _ p1.regs rfl, True.intro⟩
    (by change KeysOK [10]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  obtain ⟨d2, run2, q2⟩ := J.run d1 ⟨p1.pc, rfl⟩
  have mem2 : d2.σ.mem = d1.σ.mem := q2.memory
  have keep2 := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [1, 8, 9, 10, 15]) => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    exact (q2.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans (keep1 n lo hi (by simp; omega))
  have same2 : ∀ x, (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → (d2.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0 :=
    fun x hx => by rw [mem2, mem1, writeLog_out _ _ _ (out1 x hx)]
  have read2 : ∀ a, (a + 8 ≤ ch.toNat + 24 ∨ ch.toNat + 32 ≤ a) → read8 d2.σ.mem a = read8 d.σ.mem a :=
    fun a ha => read8_same fun i hi => same2 _ (by omega)
  have rt2 : ConsoleRuntime d2 := OCaml.Vm.Gc.ConsoleRuntime.transfer (fun x hx _ => by
    rw [← read8_value, ← read8_value, read2 x (by simp only [Layout.sym_bss_end] at hx; omega)]) rt
  have isSome : ∀ {d : Config} {n : Nat} {w : BitVec 64}, gpr d n = some w → (gprGet d.σ n).isSome := by
    intro d n w e; change (gpr d n).isSome; rw [e]; rfl
  have hs176 : (sp - 176#64).toNat + 176 = sp.toNat := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have b72 : (ch + 72#64).toNat = ch.toNat + 72 := by rw [bv_add_toNat (by omega)]
  have input : FlushInput Flush.MlOutputBytes.filled_call.link (sp - 176#64) ch fd impureData off bs d2 :=
    { good := q2.good, image := q2.image, minstret := q2.minstret, raReg := gholds_lookup _ q2.regs rfl,
      aligned := by decide, tick := q2.tick
      idle := q2.toEffectPost.htifIdle (p1.toEffectPost.htifIdle H.idle)
      saved := by
        intro n hn
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
        rcases hn with rfl | rfl | rfl | hn
        · exact isSome ((q2.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by simp)).trans
            (gholds_lookup (v := free) _ p1.regs rfl))
        · exact isSome ((q2.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by simp)).trans
            (gholds_lookup (v := rem - free) _ p1.regs rfl))
        · exact isSome ((keep2 18 (by decide) (by decide) (by simp)).trans H.chReg)
        · rw [show gprGet d2.σ n = gpr d2 n from rfl, keep2 n (by omega) (by omega) (by simp; omega)]
          exact saved n (by simp; omega)
      stack := (keep2 2 (by decide) (by decide) (by simp)).trans H.stack
      chanReg := gholds_lookup _ q2.regs rfl
      short := by rw [len]; decide
      layout := by rw [len]; exact geo.flush rfl hs176 (by decide) (by decide) hfd
      fdWord := by rw [read2 _ (by omega)]; exact fdWord
      descriptor := by rcases hfd with rfl | rfl; exact rt2.stdout; exact rt2.stderr
      curr := by
        rw [mem2, mem1, read8_value]
        refine (OCaml.Vm.Gc.word_writeLog_at d.σ.mem
          (Flush.MlOutputBytes.filledLog R1 (Flush.MlOutputBytes.filled_loads d.σ.mem R1)) 0 (ch + 24#64).toNat _
          rfl trivial).trans ?_
        show bytesVal .ld (read8 d.σ.mem (ch + 16#64).toNat) = _
        rw [endWord, len]
      offset := by
        rw [read2 _ (by rw [bv_add_toNat (by omega)]; omega)]; exact offWord
      ram := by rw [b72, len, C.tohost]; omega
      bytes := by
        intro i x hx
        have hi := (List.getElem?_eq_some_iff.mp hx).1
        rw [len] at hi
        rw [same2 _ (by rw [bv_add_toNat (by rw [b72]; omega), b72]; omega)]
        exact bytes i x hx
      enterHookWord := rt2.enterHookWord
      leaveHookWord := rt2.leaveHookWord
      impure := rt2.impure
      clear := rt2.clear
      quiet := rt2.quiet }
  obtain ⟨d3, run3, f⟩ := flush_partial input q2.pc
  obtain ⟨Q, hQ⟩ : ∃ Q, sp.toNat = Q + 512 := ⟨sp.toNat - 512, by omega⟩
  have hs' : (sp - 176#64).toNat = Q + 336 := by omega
  have back : ∀ x, (x < Q + 64 ∨ Q + 336 ≤ x) → (x < 0x80064d48 ∨ 0x80064d48 + 4 ≤ x) →
      (x < 0x80064668 ∨ 0x80064668 + 4 ≤ x) → (x < ch.toNat + 8 ∨ ch.toNat + 16 ≤ x) →
      (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → (d3.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0 := by
    intro x st er rp o k
    have st' : x < (sp - 176#64).toNat - 272 ∨ (sp - 176#64).toNat ≤ x := by
      rw [hs']; rcases st with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    rw [f.frame x st' (by rw [C.errno]; exact er) (by rw [C.impureData]; exact rp) o k]
    exact same2 x k
  have reg3 : ∀ n ∈ [18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr d3 n = gpr d n := by
    intro n hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rw [f.saved n (by simp; omega), keep2 n (by omega) (by omega) (by simp; omega)]
  have nine : gpr d3 9 = some (rem - free) := by
    rw [f.saved 9 (by simp), q2.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by simp)]
    exact gholds_lookup (v := rem - free) _ p1.regs rfl
  have eight : gpr d3 8 = some free := by
    rw [f.saved 8 (by simp), q2.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by simp)]
    exact gholds_lookup (v := free) _ p1.regs rfl
  have H3 := H.step (t' := 0x80016650#64) (rem' := rem - free) (pos' := pos) (by omega) (by omega) (by omega)
    f.good f.image f.minstret f.tick f.idle f.pc ⟨_, f.raReg, by decide⟩ ⟨_, f.result⟩
    (by
      intro n hn
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
      rcases hn with rfl | hn
      · rw [f.stack, H.stack]
      · exact reg3 n (by simp; omega))
    nine (by rw [reg3 23 (by simp)]; exact H.posReg)
    (fun x lo hi => back x (Or.inr (by omega)) (by omega) (by omega) (by omega) (by omega))
    (fun x lo hi => back x (by omega) (by omega) (by omega) (by omega) (by omega))
    (fun x st er rp o k _ _ => back x (by rcases st with h | h; exact Or.inl (by omega); exact Or.inr (by omega))
      er rp o k)
  refine ⟨d3, run1.trans (run2.trans run3), H3, eight, f.curr, f.offset, ?_,
    (GprsKept.of_pins p1 (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.filled_regs])).trans
      ((GprsKept.of_pins q2 (by decide) (by decide) (by simp [keysG])).trans f.gprs)⟩
  have o := f.output
  have o2 := q2.output
  have o1 := p1.output
  unfold Vsa.Machine.output at *
  rw [o, o2, o1]

/-- After a register-only step of the loop: the loop state at `t`, memory and
console unchanged. -/
structure ObStepped (t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos : BitVec 64)
    (c0 d e : Config) : Prop where
  head : ObHead t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos c0 e
  memory : e.σ.mem = d.σ.mem
  output : Vsa.Machine.output e.σ = Vsa.Machine.output d.σ
  gprs : GprsKept d e

/-- After writing a buffer out: advance the offset, and loop while bytes
remain (`more`) or leave the loop. -/
theorem ob_next {ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos free : BitVec 64}
    {v : Nat} {c0 d : Config} (more : Bool) (geo : ConsoleGeometry sp.toNat ch.toNat dom.toNat v 65536)
    (H : ObHead 0x80016650#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos c0 d)
    (eight : gpr d 8 = some free) (sign : guardB .BLT 0#64 rem = more) :
    ∃ e, Steps d e ∧ ObStepped (if more then 0x80016600#64 else 0x80016658#64) ra sp ch dom lr str s1v s2v s4v s5v
      s7v s0v s3v s6v rem (pos + free) c0 d e := by
  have G := geo.lits
  have l1 := G.low; have l2 := G.high; have l8 := G.domHigh
  obtain ⟨lk, hlk, alk⟩ := H.link
  obtain ⟨w0, hw0⟩ := H.a0
  let R : Nat → BitVec 64 := fun n => if n = 1 then lk else if n = 8 then free else if n = 9 then rem else
    if n = 10 then w0 else pos
  have leaf : LeafInput (R 1) d := ⟨H.good, H.image, H.minstret, hlk, alk, H.tick⟩
  have regs : GHolds d.σ (Flush.MlOutputBytes.again_input R) := ⟨hlk, eight, H.remReg, hw0, H.posReg, True.intro⟩
  have finish : ∀ e t', Steps d e → pcOf e = some t' →
      WriteRegistersPost [23] [] d t' (R 10) (Flush.MlOutputBytes.again_regs R
        (Flush.MlOutputBytes.again_loads d.σ.mem R)) e →
      ObHead t' ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem (pos + free) c0 e := by
    intro e t' run pc p
    have keep := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [23]) => p.toEffectPost.gpr_frame (by decide) n lo hi hn
    have mem : e.σ.mem = d.σ.mem := by rw [p.memory]; rfl
    exact H.step (by omega) (by omega) (by omega) p.good p.image p.minstret p.tick
      (p.toEffectPost.htifIdle H.idle) pc ⟨lk, (keep 1 (by decide) (by decide) (by simp)).trans hlk, alk⟩
      ⟨w0, (keep 10 (by decide) (by decide) (by simp)).trans hw0⟩
      (fun n hn => keep n (by simp at hn; omega) (by simp at hn; omega) (by simp at hn ⊢; omega))
      ((keep 9 (by decide) (by decide) (by simp)).trans H.remReg) (gholds_lookup _ p.regs rfl)
      (fun x _ _ => by rw [mem]) (fun x _ _ => by rw [mem]) (fun x _ _ _ _ _ _ _ => by rw [mem])
  cases more with
  | true =>
    obtain ⟨e, run, p⟩ := (Flush.MlOutputBytes.again_fast d R leaf regs sign).run d ⟨H.pc, rfl⟩
    exact ⟨e, run, finish e _ run p.pc p, by rw [p.memory]; rfl, by unfold Vsa.Machine.output; rw [p.output],
      GprsKept.of_pins p (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.again_regs])⟩
  | false =>
    obtain ⟨e, run, p⟩ := (Flush.MlOutputBytes.last_fast d R leaf regs sign).run d ⟨H.pc, rfl⟩
    exact ⟨e, run, finish e _ run p.pc p, by rw [p.memory]; rfl, by unfold Vsa.Machine.output; rw [p.output],
      GprsKept.of_pins p (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.last_regs])⟩

/-- memmove's library readiness survives any run that keeps register presence
and `gp` and leaves the HTIF device idle. -/
theorem _root_.OCaml.Vm.Primitives.LibraryReady.of_kept {c d : Config} (ready : LibraryReady c) (kept : GprsKept c d)
    (idle : d.σ.regs.get? Register.htif_payload_writes = some 0#4) : LibraryReady d :=
  ⟨fun n lo hi => kept.present n lo hi (ready.gprs n lo hi), kept.gp.trans ready.gp, idle⟩

/-- `sext.w` of a length below `2^31`. -/
theorem sext_small (r : Nat) (h : r < 2 ^ 31) :
    BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 r) 31 0) = BitVec.ofNat 64 r := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  have e : (Sail.BitVec.extractLsb (BitVec.ofNat 64 r) 31 0 : BitVec 32) = BitVec.ofNat 32 r := by
    apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.extractLsb]; try omega
  rw [e]
  have m : (BitVec.ofNat 32 r).msb = false := by rw [BitVec.msb_eq_decide]; simp; omega
  simp [m]; omega

/-- Signed comparison of small lengths. -/
theorem blt_small (r f : Nat) (hr : r < 2 ^ 31) (hf : f < 2 ^ 31) :
    guardB .BLT (BitVec.ofNat 64 r) (BitVec.ofNat 64 f) = decide (r < f) := by
  simp only [guardB, Functions.zopz0zI_s]
  have tr : (BitVec.ofNat 64 r).toInt = r := by rw [BitVec.toInt_eq_toNat_of_lt] <;> simp <;> omega
  have tf : (BitVec.ofNat 64 f).toInt = f := by rw [BitVec.toInt_eq_toNat_of_lt] <;> simp <;> omega
  rw [tr, tf]; simp

/-- `blt zero, r` on a small length. -/
theorem blt_small_zero (r : Nat) (hr : r < 2 ^ 31) :
    guardB .BLT 0#64 (BitVec.ofNat 64 r) = decide (0 < r) := blt_small 0 r (by decide) hr

/-- A nonnegative 63-bit int, sign-extended. -/
theorem signExtend_nonneg (n : BitVec 63) (h : 0 ≤ n.toInt) : n.signExtend 64 = BitVec.ofNat 64 n.toNat := by
  have lt : n.toNat < 2 ^ 62 := by
    have := BitVec.toInt_eq_toNat_cond n
    split at this <;> omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  have m : n.msb = false := by rw [BitVec.msb_eq_decide]; simp; omega
  simp [m]

/-- `bge zero, n` on a small length: taken exactly when it is zero. -/
theorem bge_zero (r : Nat) (hr : r < 2 ^ 31) : guardB .BGE 0#64 (BitVec.ofNat 64 r) = decide (r = 0) := by
  simp only [guardB, Functions.zopz0zKzJ_s]
  have tr : (BitVec.ofNat 64 r).toInt = r := by rw [BitVec.toInt_eq_toNat_of_lt] <;> simp <;> omega
  rw [tr]; simp

/-- A length below `2^31` passes `bge INT_MAX, len`. -/
theorem bge_max (r : Nat) (hr : r < 2 ^ 31) : guardB .BGE 2147483647#64 (BitVec.ofNat 64 r) = true := by
  simp only [guardB, Functions.zopz0zKzJ_s]
  have tr : (BitVec.ofNat 64 r).toInt = r := by rw [BitVec.toInt_eq_toNat_of_lt] <;> simp <;> omega
  rw [tr]; simp; omega

/-- `end - curr` as `subw` computes it, for a buffer of `65536` bytes with `k` used. -/
theorem free_subw (b : BitVec 64) (k : Nat) (hk : k ≤ 65536) :
    BitVec.signExtend 64 (Sail.BitVec.extractLsb (b + 65536#64) 31 0 -
      Sail.BitVec.extractLsb (b + BitVec.ofNat 64 k) 31 0) = BitVec.ofNat 64 (65536 - k) := by
  have e : b + 65536#64 = (b + BitVec.ofNat 64 k) + BitVec.ofNat 64 (65536 - k) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show k + (65536 - k) = 65536 by omega]
  rw [e]; exact subw_len _ _ (by omega)

/-- A register-only generated block keeps memmove's library readiness. -/
theorem LibraryReady.of_block {writes : List Nat} {c d : Config} {pc value : BitVec 64} {regs : GRegs}
    (p : WriteRegistersPost writes [] c pc value regs d) (keys : KeysOK writes) (no3 : 3 ∉ writes)
    (cover : ∀ n ∈ writes, n ∈ keysG regs) (ready : LibraryReady c) : LibraryReady d :=
  ready.of_kept (GprsKept.of_pins p keys no3 cover) (p.toEffectPost.htifIdle ready.htifIdle)

/-- After the chunk-size block: `n := rem` and `a1 = a5 = str + pos`; memory
and console unchanged. -/
structure ObSized (ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos : BitVec 64)
    (c0 d e : Config) : Prop where
  head : ObHead 0x80016618#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos c0 e
  eight : gpr e 8 = some rem
  eleven : gpr e 11 = some (pos + str)
  fifteen : gpr e 15 = some (pos + str)
  memory : e.σ.mem = d.σ.mem
  output : Vsa.Machine.output e.σ = Vsa.Machine.output d.σ
  ready : LibraryReady e
  gprs : GprsKept d e

/-- The chunk size: `n := rem` (a length below `2^31` is never clipped) and
the source `str + pos`. -/
theorem ob_small {ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v pos : BitVec 64} {r v : Nat} {c0 d : Config}
    (geo : ConsoleGeometry sp.toNat ch.toNat dom.toNat v 65536)
    (H : ObHead 0x80016600#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v (BitVec.ofNat 64 r) pos c0 d)
    (small : r < 2 ^ 31) (ready : LibraryReady d) :
    ∃ e, Steps d e ∧ ObSized ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v (BitVec.ofNat 64 r) pos c0 d e := by
  have G := geo.lits
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned; have l8 := G.domHigh
  obtain ⟨lk, hlk, alk⟩ := H.link
  obtain ⟨w0, hw0⟩ := H.a0
  let R : Nat → BitVec 64 := fun n => if n = 1 then lk else if n = 2 then sp - 176#64 else
    if n = 9 then BitVec.ofNat 64 r else if n = 10 then w0 else if n = 22 then 2147483647#64 else pos
  obtain ⟨e, run, p⟩ := (Flush.MlOutputBytes.small_fast d R ⟨H.good, H.image, H.minstret, hlk, alk, H.tick⟩
    ⟨hlk, H.stack, H.remReg, hw0, H.maxReg, H.posReg, True.intro⟩
    (frame_window (b := sp.toNat) (s := sp) rfl (by omega) (by omega) (k := 16) (off := 176) (by omega) (by omega)).read
    (bge_max r small)).run d ⟨H.pc, rfl⟩
  have keep := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [8, 11, 15]) => p.toEffectPost.gpr_frame (by decide) n lo hi hn
  have mem : e.σ.mem = d.σ.mem := by rw [p.memory]; rfl
  have src : bytesVal .ld (read8 d.σ.mem (R 2 + 16#64).toNat) = str := H.savedStr
  refine ⟨e, run, H.step (by omega) (by omega) (by omega) p.good p.image p.minstret p.tick
      (p.toEffectPost.htifIdle H.idle) p.pc ⟨lk, (keep 1 (by decide) (by decide) (by simp)).trans hlk, alk⟩
      ⟨w0, (keep 10 (by decide) (by decide) (by simp)).trans hw0⟩
      (fun n hn => keep n (by simp at hn; omega) (by simp at hn; omega) (by simp at hn ⊢; omega))
      ((keep 9 (by decide) (by decide) (by simp)).trans H.remReg)
      ((keep 23 (by decide) (by decide) (by simp)).trans H.posReg)
      (fun x _ _ => by rw [mem]) (fun x _ _ => by rw [mem]) (fun x _ _ _ _ _ _ _ => by rw [mem]),
    gholds_lookup _ p.regs rfl, ?_, ?_, mem, by unfold Vsa.Machine.output; rw [p.output],
    LibraryReady.of_block p (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.small_regs]) ready,
    GprsKept.of_pins p (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.small_regs])⟩
  · have l : gpr e 11 = some (R 23 + bytesVal .ld (read8 d.σ.mem (R 2 + 16#64).toNat)) := gholds_lookup _ p.regs rfl
    rw [l, src]; rfl
  · have l : gpr e 15 = some (R 23 + bytesVal .ld (read8 d.σ.mem (R 2 + 16#64).toNat)) := gholds_lookup _ p.regs rfl
    rw [l, src]; rfl

/-- The stdio footprint lies below the end of `.bss`. -/
theorem stdioFoot_high {a : Nat} (h : VsaIris.Stdio.stdioFoot a) : a < Layout.sym_bss_end := by
  simp only [VsaIris.Stdio.stdioFoot, VsaIris.Stdio.InRange, Layout.sym_bss_end] at h ⊢
  omega

/-- After a `jal memmove`: the copy, the rest of memory, the registers memmove
keeps, and the readiness for the next library call. -/
structure MoveRet (link : BitVec 64) (dst src n : Nat) (c e : Config) : Prop where
  good : GoodState e.σ
  image : ExecutableImage e
  minstret : ∃ w, e.σ.regs.get? Register.minstret = some w
  tick : e.tick < 2
  pc : pcOf e = some link
  raReg : gpr e 1 = some link
  result : gpr e 10 = some (BitVec.ofNat 64 dst)
  copied : ∀ i, i < n → byte e (dst + i) = byte c (src + i)
  kept : ∀ a, a < dst ∨ dst + n ≤ a → byte e a = byte c a
  output : Vsa.Machine.output e.σ = Vsa.Machine.output c.σ
  registers : ∀ k, 1 ≤ k → k ≤ 31 → k ∉ memmoveScratch → k ∉ [1, 10] → gpr e k = gpr c k
  ready : LibraryReady e
  gprs : GprsKept c e

/-- **A `jal memmove`** at a call site `ci`, with `a0`/`a1`/`a2` the
destination, source and length. -/
theorem ob_move {ci : CallInstr} (shape : CallShape ci) (decode : CallDecode ci)
    (target : ci.target = 0x80042644#64) (linkAligned : ci.link.toNat % 4 = 0)
    {c : Config} {dst src n : Nat} (pins : CallPins ci c) (good : GoodState c.σ) (image : ExecutableImage c)
    (tick : c.tick < 2) (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (pc : pcOf c = some ci.pc) (ready : LibraryReady c)
    (dReg : gpr c 10 = some (BitVec.ofNat 64 dst)) (sReg : gpr c 11 = some (BitVec.ofNat 64 src))
    (nReg : gpr c 12 = some (BitVec.ofNat 64 n))
    (geometry : VsaIris.Sym.MoveGeom 0 dst n dst src n)
    (sourceOut : ∀ a, src ≤ a → a < src + n → ¬ VsaIris.Stdio.stdioFoot a) :
    ∃ e, Steps c e ∧ MoveRet ci.link dst src n c e := by
  obtain ⟨c1, run1, q⟩ := (call_registers_summary shape decode c pins good image tick minstret
    [(10, BitVec.ofNat 64 dst), (11, BitVec.ofNat 64 src), (12, BitVec.ofNat 64 n)]
    ⟨dReg, sReg, nReg, True.intro⟩ (by change KeysOK [10, 11, 12]; decide) (by simp [KeysAvoidRa, keysG])
    rfl).run c ⟨pc, rfl⟩
  have keep1 := fun k (lo : 1 ≤ k) (hi : k ≤ 31) (hk : k ∉ [1]) => q.toEffectPost.gpr_frame (by decide) k lo hi hk
  have link1 : gpr c1 1 = some ci.link := gholds_lookup _ q.regs rfl
  have ready1 : LibraryReady c1 :=
    ready.of_kept (GprsKept.of_pins q (by decide) (by decide) (by simp [keysG]))
      (q.toEffectPost.htifIdle ready.htifIdle)
  obtain ⟨e, run2, m⟩ := (memmove_leaf c1 ⟨q.good, q.image, q.minstret, link1, linkAligned, q.tick⟩ ready1 geometry
    sourceOut (keep1 10 (by decide) (by decide) (by simp) ▸ dReg) (keep1 11 (by decide) (by decide) (by simp) ▸ sReg)
    (keep1 12 (by decide) (by decide) (by simp) ▸ nReg)).run c1 ⟨by show pcOf _ = _; rw [q.pc, target], rfl⟩
  have mem1 : c1.σ.mem = c.σ.mem := q.memory
  have scratch3 : 3 ∉ memmoveScratch := by decide
  have gp : gpr e 3 = gpr c 3 :=
    (m.registers 3 (by decide) (by decide) scratch3 (by simp)).trans (keep1 3 (by decide) (by decide) (by simp))
  refine ⟨e, run1.trans run2, m.good, m.image, m.minstret, m.tick, m.pc, m.raReg, m.result, ?_, ?_, ?_, ?_,
    ⟨m.libraryGood.gpr, gp.trans ready.gp, m.libraryGood.htifIdle⟩,
    ⟨fun k lo hi _ => m.libraryGood.gpr k lo hi, gp⟩⟩
  · intro i hi; rw [m.copied i hi]; simp only [byte, mem1]
  · intro a ha; rw [m.kept a ha]; simp only [byte, mem1]
  · rw [m.output]; unfold Vsa.Machine.output; rw [q.output]
  · intro k lo hi hs hk
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hk
    rw [m.registers k lo hi hs (by simp; omega), keep1 k lo hi (by simp; omega)]

/-- After the room test: `free` in `s3`, the chunk size in `s0`/`a2`, `curr` in
`a0`; memory and console unchanged. -/
structure ObTested (t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos src curr : BitVec 64)
    (r free : Nat) (c0 d e : Config) : Prop where
  head : ObHead t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos c0 e
  eight : gpr e 8 = some (BitVec.ofNat 64 r)
  twelve : gpr e 12 = some (BitVec.ofNat 64 r)
  ten : gpr e 10 = some curr
  nineteen : gpr e 19 = some (BitVec.ofNat 64 free)
  eleven : gpr e 11 = some src
  fifteen : gpr e 15 = some src
  memory : e.σ.mem = d.σ.mem
  output : Vsa.Machine.output e.σ = Vsa.Machine.output d.σ
  ready : LibraryReady e
  gprs : GprsKept d e

/-- **The room test**: `free := end - curr`; a chunk of `r` bytes fits
(`room`) when `r < free`. -/
theorem ob_test {ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos src : BitVec 64} {r k v : Nat}
    {c0 d : Config} (room : Bool) (geo : ConsoleGeometry sp.toNat ch.toNat dom.toNat v 65536)
    (H : ObHead 0x80016618#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos c0 d)
    (eight : gpr d 8 = some (BitVec.ofNat 64 r)) (eleven : gpr d 11 = some src) (fifteen : gpr d 15 = some src) (small : r < 2 ^ 31)
    (used : k ≤ 65536)
    (currWord : bytesVal .ld (read8 d.σ.mem (ch + 24#64).toNat) = ch + 72#64 + BitVec.ofNat 64 k)
    (endWord : bytesVal .ld (read8 d.σ.mem (ch + 16#64).toNat) = ch + 72#64 + 65536#64)
    (fits : decide (r < 65536 - k) = room) (ready : LibraryReady d) :
    ∃ e, Steps d e ∧ ObTested (if room then 0x800165e0#64 else 0x80016630#64) ra sp ch dom lr str s1v s2v s4v s5v
      s7v s0v s3v s6v rem pos src (ch + 72#64 + BitVec.ofNat 64 k) r (65536 - k) c0 d e := by
  have G := geo.lits
  have l1 := G.low; have l2 := G.high; have l4 := G.chanHigh; have l5 := G.chanLow; have l8 := G.domHigh
  obtain ⟨lk, hlk, alk⟩ := H.link
  obtain ⟨w0, hw0⟩ := H.a0
  let R : Nat → BitVec 64 := fun n => if n = 1 then lk else if n = 8 then BitVec.ofNat 64 r else
    if n = 10 then w0 else ch
  have regs : GHolds d.σ [(1, R 1), (8, R 8), (10, R 10), (18, R 18)] :=
    ⟨hlk, eight, hw0, H.chReg, True.intro⟩
  have sx : BitVec.signExtend 64 (Sail.BitVec.extractLsb (R 8) 31 0) = BitVec.ofNat 64 r := sext_small r small
  have fr : BitVec.signExtend 64 (Sail.BitVec.extractLsb (bytesVal .ld (read8 d.σ.mem (R 18 + 16#64).toNat)) 31 0 -
      Sail.BitVec.extractLsb (bytesVal .ld (read8 d.σ.mem (R 18 + 24#64).toNat)) 31 0) =
      BitVec.ofNat 64 (65536 - k) := by
    show BitVec.signExtend 64 (Sail.BitVec.extractLsb (bytesVal .ld (read8 d.σ.mem (ch + 16#64).toNat)) 31 0 -
      Sail.BitVec.extractLsb (bytesVal .ld (read8 d.σ.mem (ch + 24#64).toNat)) 31 0) = _
    rw [endWord, currWord]; exact free_subw _ k used
  have guard : guardB .BLT (BitVec.signExtend 64 (Sail.BitVec.extractLsb (R 8) 31 0))
      (BitVec.signExtend 64 (Sail.BitVec.extractLsb (bytesVal .ld (read8 d.σ.mem (R 18 + 16#64).toNat)) 31 0 -
        Sail.BitVec.extractLsb (bytesVal .ld (read8 d.σ.mem (R 18 + 24#64).toNat)) 31 0)) = room := by
    rw [sx, fr, blt_small r _ small (by omega), fits]
  have rd := fun (k' : Nat) (hk : k' + 8 ≤ 72) =>
    (arena_read (ch := ch.toNat) (chB := ch) (k := k') rfl (by omega) (by omega) : ReadWindow (R 18 + BitVec.ofNat 64 k') 8)
  have finish : ∀ e t (pc : pcOf e = some t) (run : Steps d e)
      (p : WriteRegistersPost [8, 10, 12, 19] [] d t
        (bytesVal .ld ((Flush.MlOutputBytes.room_loads d.σ.mem R).getD 0 []))
        (Flush.MlOutputBytes.room_regs R (Flush.MlOutputBytes.room_loads d.σ.mem R)) e),
      ∃ e, Steps d e ∧ ObTested t ra sp ch dom lr str s1v s2v s4v s5v
        s7v s0v s3v s6v rem pos src (ch + 72#64 + BitVec.ofNat 64 k) r (65536 - k) c0 d e := by
    intro e t pc run p
    have keep := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [8, 10, 12, 19]) =>
      p.toEffectPost.gpr_frame (by decide) n lo hi hn
    have mem : e.σ.mem = d.σ.mem := by rw [p.memory]; rfl
    refine ⟨e, run, H.step (by omega) (by omega) (by omega) p.good p.image p.minstret p.tick
        (p.toEffectPost.htifIdle H.idle) pc ⟨lk, (keep 1 (by decide) (by decide) (by simp)).trans hlk, alk⟩
        ⟨_, gholds_lookup (n := 10) _ p.regs rfl⟩
        (fun n hn => keep n (by simp at hn; omega) (by simp at hn; omega) (by simp at hn ⊢; omega))
        ((keep 9 (by decide) (by decide) (by simp)).trans H.remReg)
        ((keep 23 (by decide) (by decide) (by simp)).trans H.posReg)
        (fun x _ _ => by rw [mem]) (fun x _ _ => by rw [mem]) (fun x _ _ _ _ _ _ _ => by rw [mem]),
      ?_, ?_, ?_, ?_, (keep 11 (by decide) (by decide) (by simp)).trans eleven,
      (keep 15 (by decide) (by decide) (by simp)).trans fifteen, mem, by unfold Vsa.Machine.output; rw [p.output],
      LibraryReady.of_block p (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.room_regs]) ready,
      GprsKept.of_pins p (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.room_regs])⟩
    · have l : gpr e 8 = some (BitVec.signExtend 64 (Sail.BitVec.extractLsb (R 8) 31 0)) := gholds_lookup _ p.regs rfl
      rw [l, sx]
    · have l : gpr e 12 = some (BitVec.signExtend 64 (Sail.BitVec.extractLsb (R 8) 31 0)) := gholds_lookup _ p.regs rfl
      rw [l, sx]
    · have l : gpr e 10 = some (bytesVal .ld (read8 d.σ.mem (R 18 + 24#64).toNat)) := gholds_lookup _ p.regs rfl
      rw [l]; exact congrArg some currWord
    · have l : gpr e 19 = some (BitVec.signExtend 64 (Sail.BitVec.extractLsb
          (bytesVal .ld (read8 d.σ.mem (R 18 + 16#64).toNat)) 31 0 -
          Sail.BitVec.extractLsb (bytesVal .ld (read8 d.σ.mem (R 18 + 24#64).toNat)) 31 0)) := gholds_lookup _ p.regs rfl
      rw [l, fr]
  cases room with
  | true =>
    obtain ⟨e, run, p⟩ := (Flush.MlOutputBytes.room_fast d R ⟨H.good, H.image, H.minstret, hlk, alk, H.tick⟩
      regs (rd 24 (by decide)) (rd 16 (by decide)) guard).run d ⟨H.pc, rfl⟩
    exact finish e _ p.pc run p
  | false =>
    obtain ⟨e, run, p⟩ := (Flush.MlOutputBytes.full_fast d R ⟨H.good, H.image, H.minstret, hlk, alk, H.tick⟩
      regs (rd 24 (by decide)) (rd 16 (by decide)) guard).run d ⟨H.pc, rfl⟩
    exact finish e _ p.pc run p

/-- What one copy into the channel buffer did: `r` source bytes at buffer
offset `k`, the `curr` word, nothing else in memory. -/
structure ObCopy (ch curr : BitVec 64) (k r src : Nat) (d e : Config) : Prop where
  copied : ∀ i, i < r → byte e (ch.toNat + 72 + k + i) = byte d (src + i)
  currWord : bytesVal .ld (read8 e.σ.mem (ch + 24#64).toNat) = curr
  kept : ∀ a, (a < ch.toNat + 72 + k ∨ ch.toNat + 72 + k + r ≤ a) → (a < ch.toNat + 24 ∨ ch.toNat + 32 ≤ a) →
    byte e a = byte d a
  output : Vsa.Machine.output e.σ = Vsa.Machine.output d.σ
  gprs : GprsKept d e

/-- Where a copy's source may lie: in the heap, apart from the channel's
record and buffer. -/
structure ObSource (ch : BitVec 64) (src r : Nat) : Prop where
  low : Layout.sym_bss_end ≤ src
  high : src + r ≤ Vsa.Sim.DlHeap.heapEnd
  apart : src + r ≤ ch.toNat ∨ ch.toNat + 72 + 65536 ≤ src

theorem bv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- memmove's geometry for a copy of `r` bytes into the buffer at offset `k`. -/
theorem ObSource.move {ch : BitVec 64} {src r k v sp dom : Nat} (S : ObSource ch src r)
    (geo : ConsoleGeometry sp ch.toNat dom v 65536) (fit : k + r ≤ 65536) :
    VsaIris.Sym.MoveGeom 0 (ch.toNat + 72 + k) r (ch.toNat + 72 + k) src r ∧
      ∀ a, src ≤ a → a < src + r → ¬ VsaIris.Stdio.stdioFoot a := by
  have G := geo.lits
  have l4 := G.chanHigh; have l5 := G.chanLow
  have lo := S.low; have hi := S.high; have ap := S.apart
  simp only [Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd] at lo hi
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, Or.inr (by omega), by omega⟩, ?_⟩
  intro a ha _ foot
  have := stdioFoot_high foot; simp only [Layout.sym_bss_end] at this; omega

/-- **A chunk that fits**: `memmove` it to `curr`, advance `curr`, and leave
the loop (`rem - n = 0`). -/
theorem ob_room {ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v pos src : BitVec 64} {r k v : Nat}
    {c0 d : Config} (geo : ConsoleGeometry sp.toNat ch.toNat dom.toNat v 65536)
    (H : ObHead 0x800165e0#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v (BitVec.ofNat 64 r) pos c0 d)
    (eight : gpr d 8 = some (BitVec.ofNat 64 r)) (twelve : gpr d 12 = some (BitVec.ofNat 64 r))
    (ten : gpr d 10 = some (ch + 72#64 + BitVec.ofNat 64 k)) (fifteen : gpr d 15 = some src)
    (fit : k + r < 65536) (source : ObSource ch src.toNat r)
    (currWord : bytesVal .ld (read8 d.σ.mem (ch + 24#64).toNat) = ch + 72#64 + BitVec.ofNat 64 k)
    (ready : LibraryReady d) :
    ∃ e, Steps d e ∧ ObHead 0x80016658#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v 0#64
      (pos + BitVec.ofNat 64 r) c0 e ∧
      ObCopy ch (ch + 72#64 + BitVec.ofNat 64 k + BitVec.ofNat 64 r) k r src.toNat d e := by
  have G := geo.lits
  have l1 := G.low; have l2 := G.high; have l4 := G.chanHigh; have l5 := G.chanLow; have l8 := G.domHigh
  have l7 := G.domLow; have cd := G.chanDom
  have T := consoleLits.textEnd; have Rd := consoleLits.rodataEnd
  have tb : 0x80000000 ≤ Image.textBase := by decide
  have rb : 0x80000000 ≤ Image.rodataBase := by decide
  obtain ⟨lk, hlk, alk⟩ := H.link
  have hdst : ch + 72#64 + BitVec.ofNat 64 k = BitVec.ofNat 64 (ch.toNat + 72 + k) := by
    apply BitVec.eq_of_toNat_eq
    rw [bv_add_toNat (by rw [bv_add_toNat (by omega)]; omega), bv_add_toNat (by omega)]
    simp only [BitVec.toNat_ofNat]; omega
  -- a1 := src
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then lk else if n = 10 then ch + 72#64 + BitVec.ofNat 64 k else src
  obtain ⟨d1, run1, p1⟩ := (Flush.MlOutputBytes.put_fast d R1 ⟨H.good, H.image, H.minstret, hlk, alk, H.tick⟩
    ⟨hlk, ten, fifteen, True.intro⟩).run d ⟨H.pc, rfl⟩
  have keep1 := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [11]) => p1.toEffectPost.gpr_frame (by decide) n lo hi hn
  have mem1 : d1.σ.mem = d.σ.mem := by rw [p1.memory]; rfl
  obtain ⟨geom, sourceOut⟩ := source.move (k := k) geo (by omega)
  obtain ⟨d2, run2, m⟩ := ob_move Flush.MlOutputBytes.put_call_shape Flush.MlOutputBytes.put_call_decode
    (by decide) (by decide) (Flush.MlOutputBytes.put_call_pins p1.image) p1.good p1.image p1.tick p1.minstret p1.pc
    (LibraryReady.of_block p1 (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.put_regs]) ready)
    ((keep1 10 (by decide) (by decide) (by simp)).trans (ten.trans (by rw [hdst])))
    ((gholds_lookup (v := R1 15) _ p1.regs rfl).trans (by rw [bv_ofNat_toNat]; rfl))
    ((keep1 12 (by decide) (by decide) (by simp)).trans twelve) geom sourceOut
  -- the bytes `memmove` leaves alone read as before
  have byte2 : ∀ a, (a < ch.toNat + 72 + k ∨ ch.toNat + 72 + k + r ≤ a) →
      (d2.σ.mem[a]?).getD 0 = (d.σ.mem[a]?).getD 0 := fun a ha => by
    rw [← byte_total, ← byte_total, m.kept a ha]; simp only [byte, mem1]
  have h24 : (ch + 24#64).toNat = ch.toNat + 24 := bv_add_toNat (by omega)
  have curr2 : bytesVal .ld (read8 d2.σ.mem (ch + 24#64).toNat) = ch + 72#64 + BitVec.ofNat 64 k := by
    rw [read8_same fun i hi => byte2 _ (by rw [h24]; omega)]; exact currWord
  have keep2 := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hs : n ∉ memmoveScratch) (hn : n ∉ [1, 10]) => m.registers n lo hi hs hn
  let R2 : Nat → BitVec 64 := fun n => if n = 1 then Flush.MlOutputBytes.put_call.link else
    if n = 8 then BitVec.ofNat 64 r else if n = 9 then BitVec.ofNat 64 r else
    if n = 10 then BitVec.ofNat 64 (ch.toNat + 72 + k) else if n = 18 then ch else pos
  have at2 := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hs : n ∉ memmoveScratch) (hn : n ∉ [1, 10, 11]) =>
    (keep2 n lo hi hs (by simp at hn ⊢; omega)).trans (keep1 n lo hi (by simp at hn ⊢; omega))
  have within : ∀ e ∈ Flush.MlOutputBytes.doneLog R2 (Flush.MlOutputBytes.done_loads d2.σ.mem R2),
      e.1 = ch.toNat + 24 ∧ e.2.1 = 8 := by
    intro e he
    simp only [Flush.MlOutputBytes.doneLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he; exact ⟨h24, rfl⟩
  have linkAl : (R2 1).toNat % 4 = 0 := (by decide : Flush.MlOutputBytes.put_call.link.toNat % 4 = 0)
  have l6 := G.chanAligned
  obtain ⟨d3, run3, p3⟩ := (Flush.MlOutputBytes.done_fast d2 R2 ⟨m.good, m.image, m.minstret, m.raReg, linkAl, m.tick⟩
    ⟨m.raReg, (at2 8 (by decide) (by decide) (by decide) (by simp)).trans eight,
      (at2 9 (by decide) (by decide) (by decide) (by simp)).trans H.remReg, m.result,
      (at2 18 (by decide) (by decide) (by decide) (by simp)).trans H.chReg,
      (at2 23 (by decide) (by decide) (by decide) (by simp)).trans H.posReg, True.intro⟩
    (arena_read (ch := ch.toNat) (chB := ch) (k := 24) rfl (by omega) (by omega))
    (arena_write (ch := ch.toNat) (k := 24) rfl (by omega) (by omega) (by omega))
    ⟨outLRange_of_each fun e he => by obtain ⟨a, b⟩ := within e he; omega,
     outLRange_of_each fun e he => by obtain ⟨a, b⟩ := within e he; omega⟩
    (by show guardB .BGE 0#64 (BitVec.ofNat 64 r - BitVec.ofNat 64 r) = true
        rw [BitVec.sub_self]; decide)).run d2 ⟨m.pc, rfl⟩
  have mem3 : d3.σ.mem = writeLog d2.σ.mem (Flush.MlOutputBytes.doneLog R2 (Flush.MlOutputBytes.done_loads d2.σ.mem R2)) :=
    p3.memory
  have out3 : ∀ x, (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) →
      OutL (Flush.MlOutputBytes.doneLog R2 (Flush.MlOutputBytes.done_loads d2.σ.mem R2)) x :=
    fun x hx => outL_of_each fun e he => by obtain ⟨a, b⟩ := within e he; omega
  have keep3 := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [9, 15, 23]) => p3.toEffectPost.gpr_frame (by decide) n lo hi hn
  have same : ∀ x, (x < ch.toNat + 72 + k ∨ ch.toNat + 72 + k + r ≤ x) → (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) →
      (d3.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0 := fun x a b => by
    rw [mem3, writeLog_out _ _ _ (out3 x b), byte2 x a]
  refine ⟨d3, run1.trans (run2.trans run3), H.step (by omega) (by omega) (by omega) p3.good p3.image p3.minstret
      p3.tick (p3.toEffectPost.htifIdle m.ready.htifIdle) p3.pc
      ⟨_, (keep3 1 (by decide) (by decide) (by simp)).trans m.raReg, by decide⟩
      ⟨_, (keep3 10 (by decide) (by decide) (by simp)).trans m.result⟩
      (fun n hn => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
        rw [keep3 n (by omega) (by omega) (by simp; omega)]
        exact at2 n (by omega) (by omega) (by simp [memmoveScratch]; omega) (by simp; omega))
      (by have l : gpr d3 9 = some (R2 9 - R2 8) := gholds_lookup _ p3.regs rfl
          rw [l]; simp only [R2, ↓reduceIte, Nat.reduceEqDiff, BitVec.sub_self])
      (by have l : gpr d3 23 = some (R2 23 + R2 8) := gholds_lookup _ p3.regs rfl
          rw [l]; rfl)
      (fun x lo hi => same x (Or.inr (by omega)) (Or.inr (by omega)))
      (fun x lo hi => same x (by omega) (by omega))
      (fun x _ _ _ _ k' bu _ => same x (by omega) k'), ?_, ?_, ?_, ?_,
    m.gprs.trans (GprsKept.of_pins p3 (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.done_regs]))
      |> (GprsKept.of_pins p1 (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.put_regs])).trans⟩
  · intro i hi
    rw [byte_total, byte_total, mem3, writeLog_out _ _ _ (out3 _ (by omega)), ← byte_total, m.copied i hi,
      byte_total, mem1]
  · rw [mem3, read8_value]
    refine (OCaml.Vm.Gc.word_writeLog_at d2.σ.mem
      (Flush.MlOutputBytes.doneLog R2 (Flush.MlOutputBytes.done_loads d2.σ.mem R2)) 0 (ch + 24#64).toNat _
      rfl trivial).trans ?_
    show bytesVal .ld (read8 d2.σ.mem (ch + 24#64).toNat) + BitVec.ofNat 64 r = _
    rw [curr2]
  · intro a ha hb; rw [byte_total, byte_total]; exact same a ha hb
  · have o3 := p3.output; have o1 := p1.output; have o2 := m.output
    unfold Vsa.Machine.output at *
    rw [o3, o2, o1]

/-- **A chunk that fills the buffer**: `memmove` the `free = 65536 - k`
bytes that fit, up to the `curr := end` block. -/
theorem ob_fill {ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos src : BitVec 64} {k v : Nat}
    {c0 d : Config} (geo : ConsoleGeometry sp.toNat ch.toNat dom.toNat v 65536)
    (H : ObHead 0x80016630#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos c0 d)
    (ten : gpr d 10 = some (ch + 72#64 + BitVec.ofNat 64 k)) (eleven : gpr d 11 = some src)
    (nineteen : gpr d 19 = some (BitVec.ofNat 64 (65536 - k)))
    (used : k ≤ 65536) (source : ObSource ch src.toNat (65536 - k))
    (currWord : bytesVal .ld (read8 d.σ.mem (ch + 24#64).toNat) = ch + 72#64 + BitVec.ofNat 64 k)
    (ready : LibraryReady d) :
    ∃ e, Steps d e ∧ ObHead 0x80016638#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos c0 e ∧
      gpr e 19 = some (BitVec.ofNat 64 (65536 - k)) ∧ ObCopy ch (ch + 72#64 + BitVec.ofNat 64 k) k (65536 - k) src.toNat d e ∧
      LibraryReady e := by
  have G := geo.lits
  have l1 := G.low; have l2 := G.high; have l4 := G.chanHigh; have l5 := G.chanLow; have l8 := G.domHigh
  have l7 := G.domLow; have cd := G.chanDom
  obtain ⟨lk, hlk, alk⟩ := H.link
  have hdst : ch + 72#64 + BitVec.ofNat 64 k = BitVec.ofNat 64 (ch.toNat + 72 + k) := by
    apply BitVec.eq_of_toNat_eq
    rw [bv_add_toNat (by rw [bv_add_toNat (by omega)]; omega), bv_add_toNat (by omega)]
    simp only [BitVec.toNat_ofNat]; omega
  -- a2 := free
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then lk else if n = 10 then ch + 72#64 + BitVec.ofNat 64 k else
    BitVec.ofNat 64 (65536 - k)
  obtain ⟨d1, run1, p1⟩ := (Flush.MlOutputBytes.fill_fast d R1 ⟨H.good, H.image, H.minstret, hlk, alk, H.tick⟩
    ⟨hlk, ten, nineteen, True.intro⟩).run d ⟨H.pc, rfl⟩
  have keep1 := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [12]) => p1.toEffectPost.gpr_frame (by decide) n lo hi hn
  have mem1 : d1.σ.mem = d.σ.mem := by rw [p1.memory]; rfl
  obtain ⟨geom, sourceOut⟩ := source.move (k := k) geo (by omega)
  obtain ⟨d2, run2, m⟩ := ob_move Flush.MlOutputBytes.fill_call_shape Flush.MlOutputBytes.fill_call_decode
    (by decide) (by decide) (Flush.MlOutputBytes.fill_call_pins p1.image) p1.good p1.image p1.tick p1.minstret p1.pc
    (LibraryReady.of_block p1 (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.fill_regs]) ready)
    ((keep1 10 (by decide) (by decide) (by simp)).trans (ten.trans (by rw [hdst])))
    ((keep1 11 (by decide) (by decide) (by simp)).trans (eleven.trans (by rw [bv_ofNat_toNat])))
    (gholds_lookup (v := R1 19) _ p1.regs rfl) geom sourceOut
  have byte2 : ∀ a, (a < ch.toNat + 72 + k ∨ ch.toNat + 72 + k + (65536 - k) ≤ a) →
      (d2.σ.mem[a]?).getD 0 = (d.σ.mem[a]?).getD 0 := fun a ha => by
    rw [← byte_total, ← byte_total, m.kept a ha, byte_total, byte_total, mem1]
  have h24 : (ch + 24#64).toNat = ch.toNat + 24 := bv_add_toNat (by omega)
  have keep2 := fun n (lo : 1 ≤ n) (hi : n ≤ 31) (hs : n ∉ memmoveScratch) (hn : n ∉ [1, 10, 12]) =>
    (m.registers n lo hi hs (by simp at hn ⊢; omega)).trans (keep1 n lo hi (by simp at hn ⊢; omega))
  refine ⟨d2, run1.trans run2, H.step (by omega) (by omega) (by omega) m.good m.image m.minstret m.tick
      m.ready.htifIdle m.pc ⟨_, m.raReg, by decide⟩ ⟨_, m.result⟩
      (fun n hn => keep2 n (by simp at hn; omega) (by simp at hn; omega) (by simp [memmoveScratch] at hn ⊢; omega)
        (by simp at hn ⊢; omega))
      ((keep2 9 (by decide) (by decide) (by decide) (by simp)).trans H.remReg)
      ((keep2 23 (by decide) (by decide) (by decide) (by simp)).trans H.posReg)
      (fun x lo hi => byte2 x (Or.inr (by omega)))
      (fun x lo hi => byte2 x (by omega))
      (fun x _ _ _ _ _ bu _ => byte2 x (by omega)),
    (keep2 19 (by decide) (by decide) (by decide) (by simp)).trans nineteen,
    ⟨fun i hi => by rw [m.copied i hi, byte_total, byte_total, mem1],
     by rw [read8_same fun i hi => byte2 _ (by rw [h24]; omega)]; exact currWord,
     fun a ha _ => by rw [byte_total, byte_total]; exact byte2 a ha,
     by have o1 := p1.output; have o2 := m.output; unfold Vsa.Machine.output at *; rw [o2, o1],
     (GprsKept.of_pins p1 (by decide) (by decide) (by simp [keysG, Flush.MlOutputBytes.fill_regs])).trans m.gprs⟩,
    m.ready⟩


end OCaml.Vm.Primitives.ConsoleWrite
