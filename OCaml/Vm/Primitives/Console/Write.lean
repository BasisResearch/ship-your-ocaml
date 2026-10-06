import OCaml.Vm.Primitives.Console.Loop
import OCaml.Vm.Primitives.ExitPath.Machine

/-! newlib `_write(fd, buf, n)` on a console descriptor: every byte is
printed by one HTIF putchar store, and `n` is returned. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable
open ExitPath (LogWithin LogWithin.outL LogWithin.outLRange)

/-- `_write`'s 96-byte native frame below `sp`, disjoint from the image, the
`fs_ready` flag, the descriptor's kind word and the buffer. -/
structure WriteLayout (sp fd buf : BitVec 64) (len : Nat) : Prop where
  low : 0x80000000 + 96 ≤ sp.toNat
  high : sp.toNat ≤ 0x100000000
  htif : Layout.sym_tohost + 16 + 96 ≤ sp.toNat
  aligned : sp.toNat % 16 = 0
  text : Image.textBase + Image.textSize ≤ sp.toNat - 96 ∨ sp.toNat ≤ Image.textBase
  rodata : Image.rodataBase + Image.rodataSize ≤ sp.toNat - 96 ∨ sp.toNat ≤ Image.rodataBase
  ready : fsReady.toNat + 4 ≤ sp.toNat - 96 ∨ sp.toNat ≤ fsReady.toNat
  kind : (kindAddress fd).toNat + 8 ≤ sp.toNat - 96 ∨ sp.toNat ≤ (kindAddress fd).toNat
  buffer : buf.toNat + len ≤ sp.toNat - 96 ∨ sp.toNat ≤ buf.toNat

/-- The runtime's descriptor table: the file system is initialised and `fd`
is an open console (kind neither invalid, ≤ 1, nor a regular file, 4). -/
structure ConsoleFd (fd : BitVec 64) (c : Config) : Prop where
  ready : bytesVal .lw (read8 c.σ.mem fsReady.toNat) ≠ 0#64
  range : fd.toNat < 32
  kindWindow : ReadWindow (kindAddress fd) 4
  console : 1 < (bytesVal .lw (read8 c.σ.mem (kindAddress fd).toNat)).toNat
  notFile : bytesVal .lw (read8 c.σ.mem (kindAddress fd).toNat) ≠ 4#64

structure WriteInput (ra sp fd buf : BitVec 64) (bs : List UInt8) (c : Config) : Prop
    extends LeafInput ra c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  saved : ∀ n ∈ [8, 9, 18], (gprGet c.σ n).isSome
  stack : gpr c 2 = some sp
  fdReg : gpr c 10 = some fd
  bufReg : gpr c 11 = some buf
  lenReg : gpr c 12 = some (BitVec.ofNat 64 bs.length)
  layout : WriteLayout sp fd buf bs.length
  descriptor : ConsoleFd fd c
  ram : 0x80000000 ≤ buf.toNat ∧ buf.toNat + bs.length ≤ 0x100000000 ∧
    (buf.toNat + bs.length ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 8 ≤ buf.toNat)
  bytes : ∀ i x, bs[i]? = some x → (c.σ.mem[(buf + BitVec.ofNat 64 i).toNat]?).getD 0 = BitVec.ofNat 8 x.toNat

/-- Return from `_write`: `n` in `a0`, the bytes appended to the console
output, callee-saved registers restored, only the frame saves written. -/
structure WritePost (ra sp : BitVec 64) (bs : List UInt8) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some ra
  result : gpr d 10 = some (BitVec.ofNat 64 bs.length)
  stack : gpr d 2 = some sp
  saved : ∀ n ∈ [1, 8, 9, 18], gpr d n = gpr c n
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ ++ bytesToString bs
  frame : ∀ x, ((sp.toNat - 96) > x ∨ sp.toNat ≤ x) → (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0


theorem WriteLayout.write {sp fd buf x : BitVec 64} {len : Nat} (h : WriteLayout sp fd buf len)
    (slot : sp.toNat - 96 ≤ x.toNat ∧ x.toNat + 8 ≤ sp.toNat ∧ x.toNat % 8 = 0) : WriteWindow x 8 := by
  have l := h.low; have u := h.high; have t := h.htif
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem WriteLayout.image {sp fd buf : BitVec 64} {len : Nat} (h : WriteLayout sp fd buf len) {log : List WEntry}
    (within : LogWithin log (sp.toNat - 96) sp.toNat) : ImageOutside log :=
  ⟨within.outLRange h.text, within.outLRange h.rodata⟩

/-- A word outside an exact log reads as before. -/
theorem read8_outside {m : Std.ExtHashMap Nat (BitVec 8)} {log : List WEntry} {lo hi a : Nat}
    (within : LogWithin log lo hi) (apart : a + 8 ≤ lo ∨ hi ≤ a) : read8 (writeLog m log) a = read8 m a := by
  simp only [read8]
  rw [writeLog_out _ _ _ (within.outL (by omega)), writeLog_out _ _ _ (within.outL (by omega)),
    writeLog_out _ _ _ (within.outL (by omega)), writeLog_out _ _ _ (within.outL (by omega)),
    writeLog_out _ _ _ (within.outL (by omega)), writeLog_out _ _ _ (within.outL (by omega)),
    writeLog_out _ _ _ (within.outL (by omega)), writeLog_out _ _ _ (within.outL (by omega))]

theorem write_console {ra sp fd buf bs c} (h : WriteInput ra sp fd buf bs c)
    (entry : pcOf c = some 0x80000d54#64) :
    ∃ d, Steps c d ∧ WritePost ra sp bs c d := by
  have L := h.layout
  have D := h.descriptor
  have present := fun n (hn : n ∈ [8, 9, 18]) => by
    have := h.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  let len : BitVec 64 := BitVec.ofNat 64 bs.length
  let R0 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else if n = 10 then fd else
    if n = 11 then buf else if n = 12 then len else (gpr c n).getD 0
  have within : LogWithin (entryLog R0) (sp.toNat - 96) sp.toNat := by
    have := L.low
    intro e he
    simp only [entryLog, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;>
      (simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; frame_arith)
  have e0 := entry_fast c R0 h.toLeafInput
    ⟨h.raReg, h.stack, present 8 (by simp), present 9 (by simp), h.fdReg, h.bufReg, h.lenReg,
      present 18 (by simp), True.intro⟩
    ⟨by decide, by decide, Or.inr (by decide)⟩
    (by
      intro k hk
      have := L.low; have := L.aligned
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;>
        exact L.write (by simp only [R0, ↓reduceIte, Nat.reduceEqDiff]; frame_arith))
    (L.image within) D.ready
  obtain ⟨d1, run1, p1⟩ := e0.run c ⟨entry, rfl⟩
  have ok1 : LoopOk d1 := p1.loopOk ⟨h.good, h.tick, h.idle⟩
  have mem1 : d1.σ.mem = writeLog c.σ.mem (entryLog R0) := p1.memory
  have fd1 : gpr d1 8 = some fd := gholds_lookup _ p1.regs rfl
  have len1 : gpr d1 9 = some len := gholds_lookup _ p1.regs rfl
  have buf1 : gpr d1 18 = some buf := gholds_lookup _ p1.regs rfl
  have sp1 : gpr d1 2 = some (sp - 96#64) := gholds_lookup _ p1.regs rfl
  -- fd < 32
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then ra else fd
  have e1 := range_fast d1 R1 ⟨p1.good, p1.image, p1.minstret, gholds_lookup _ p1.regs rfl, h.aligned, p1.tick⟩
    ⟨gholds_lookup _ p1.regs rfl, fd1, gholds_lookup _ p1.regs rfl, True.intro⟩
    (by have := D.range; simp [R1, guardB, Functions.zopz0zI_u, Sail.BitVec.toNatInt]; omega)
  obtain ⟨d2, run2, p2⟩ := e1.run d1 ⟨p1.pc, rfl⟩
  have ok2 := p2.loopOk ok1
  have keep2 := fun n lo hi (hn : n ∉ [15]) => p2.toEffectPost.gpr_frame (by decide) n lo hi hn
  -- fds[fd].kind > 1
  have kindRead : read8 d2.σ.mem (kindAddress fd).toNat = read8 c.σ.mem (kindAddress fd).toNat := by
    rw [p2.memory, show writeLog d1.σ.mem [] = d1.σ.mem from rfl, mem1]
    exact read8_outside within L.kind
  have e2 := kind_fast d2 R1 ⟨p2.good, p2.image, p2.minstret, (keep2 1 (by decide) (by decide) (by simp)).trans
      (gholds_lookup _ p1.regs rfl), h.aligned, p2.tick⟩
    ⟨(keep2 1 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl),
      (keep2 8 (by decide) (by decide) (by simp)).trans fd1,
      (keep2 10 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl), True.intro⟩
    D.kindWindow
    (by show guardB .BGEU 1#64 (bytesVal .lw (read8 d2.σ.mem (kindAddress fd).toNat)) = false
        rw [kindRead]; have := D.console; simp [guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt]; omega)
  obtain ⟨d3, run3, p3⟩ := e2.run d2 ⟨p2.pc, rfl⟩
  -- the common return: `a0 := s1`, then reload ra, s0–s2 and return
  have finish : ∀ d, LoopOk d → ExecutableImage d → (∃ v, d.σ.regs.get? Register.minstret = some v) →
      pcOf d = some 0x80000f3c#64 → gpr d 1 = some ra → gpr d 2 = some (sp - 96#64) →
      gpr d 9 = some len → (∃ v, gpr d 10 = some v) →
      d.σ.mem = writeLog c.σ.mem (entryLog R0) →
      Vsa.Machine.output d.σ = Vsa.Machine.output c.σ ++ bytesToString bs →
      ∃ f, Steps d f ∧ WritePost ra sp bs c f := by
    intro d ok image mins pc raR spR lenR aR mem out
    obtain ⟨a, ha⟩ := aR
    let R5 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 9 then len else a
    have e5 := result_fast d R5 ⟨ok.good, image, mins, raR, h.aligned, ok.tick⟩ ⟨raR, lenR, ha, True.intro⟩
    obtain ⟨d5, run5, p5⟩ := e5.run d ⟨pc, rfl⟩
    have sp5 : gpr d5 2 = some (sp - 96#64) :=
      (p5.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by simp)).trans spR
    let R6 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp - 96#64 else len
    have mem5 : d5.σ.mem = writeLog c.σ.mem (entryLog R0) := by rw [p5.memory]; exact mem
    have slotNat := fun (k : Nat) (hk : k ≤ 88) => (show (sp - 96#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 96 + k by
      have := L.low; frame_arith)
    have back := fun (i k : Nat) (v : BitVec 64) (sel : (entryLog R0)[i]? = some ((sp - 96#64 + BitVec.ofNat 64 k).toNat, 8, v))
        (after : OutLRange ((entryLog R0).drop (i + 1)) (sp - 96#64 + BitVec.ofNat 64 k).toNat 8) =>
      (show bytesVal .ld (read8 d5.σ.mem (sp - 96#64 + BitVec.ofNat 64 k).toNat) = v by
        rw [read8_value, mem5]; exact Gc.word_writeLog_at _ _ i _ _ sel after)
    have raBack := back 3 88 ra rfl True.intro
    have e6 := leave_fast d5 ra R6 ⟨p5.good, p5.image, p5.minstret, gholds_lookup _ p5.regs rfl, h.aligned, p5.tick⟩
      ⟨sp5, gholds_lookup _ p5.regs rfl, True.intro⟩
      (by
        intro k hk
        have := L.low; have := L.aligned
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;>
          exact (L.write (by simp only [R6, ↓reduceIte, Nat.reduceEqDiff]; frame_arith)).read)
      raBack h.aligned
    obtain ⟨d6, run6, p6⟩ := e6.run d5 ⟨p5.pc, rfl⟩
    have apart := fun (j k : Nat) (hj : j ≤ 88) (hk : k ≤ 88) (ne : j + 8 ≤ k ∨ k + 8 ≤ j) =>
      (show (sp - 96#64 + BitVec.ofNat 64 j).toNat + 8 ≤ (sp - 96#64 + BitVec.ofNat 64 k).toNat ∨
          (sp - 96#64 + BitVec.ofNat 64 k).toNat + 8 ≤ (sp - 96#64 + BitVec.ofNat 64 j).toNat by
        rw [slotNat j hj, slotNat k hk]; omega)
    have s0Back := back 0 80 (R0 8) rfl ⟨by dsimp only; exact apart 80 72 (by decide) (by decide) (by decide),
      by dsimp only; exact apart 80 64 (by decide) (by decide) (by decide),
      by dsimp only; exact apart 80 88 (by decide) (by decide) (by decide), True.intro⟩
    have s1Back := back 1 72 (R0 9) rfl ⟨by dsimp only; exact apart 72 64 (by decide) (by decide) (by decide),
      by dsimp only; exact apart 72 88 (by decide) (by decide) (by decide), True.intro⟩
    have s2Back := back 2 64 (R0 18) rfl ⟨by dsimp only; exact apart 64 88 (by decide) (by decide) (by decide), True.intro⟩
    have restore : ∀ n ∈ [8, 9, 18], gpr c n = some (R0 n) := fun n hn => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
      rcases hn with rfl | rfl | rfl <;> exact present _ (by simp)
    refine ⟨d6, run5.trans run6, p6.good, p6.image, p6.minstret, p6.tick,
      ((p6.loopOk (p5.loopOk ok))).htifIdle, p6.pc, ?_, ?_, ?_, ?_, ?_⟩
    · have l : gpr d6 10 = some (R6 10) := gholds_lookup _ p6.regs rfl
      exact l
    · have l : gpr d6 2 = some (sp - 96#64 + 96#64) := gholds_lookup _ p6.regs rfl
      rw [l, BitVec.sub_add_cancel]
    · intro n hn
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl
      · have l : gpr d6 1 = some (bytesVal .ld (read8 d5.σ.mem (sp - 96#64 + BitVec.ofNat 64 88).toNat)) :=
          gholds_lookup _ p6.regs rfl
        rw [l, raBack]; exact h.raReg.symm
      · have l : gpr d6 8 = some (bytesVal .ld (read8 d5.σ.mem (sp - 96#64 + BitVec.ofNat 64 80).toNat)) :=
          gholds_lookup _ p6.regs rfl
        rw [l, s0Back]; exact (restore 8 (by simp)).symm
      · have l : gpr d6 9 = some (bytesVal .ld (read8 d5.σ.mem (sp - 96#64 + BitVec.ofNat 64 72).toNat)) :=
          gholds_lookup _ p6.regs rfl
        rw [l, s1Back]; exact (restore 9 (by simp)).symm
      · have l : gpr d6 18 = some (bytesVal .ld (read8 d5.σ.mem (sp - 96#64 + BitVec.ofNat 64 64).toNat)) :=
          gholds_lookup _ p6.regs rfl
        rw [l, s2Back]; exact (restore 18 (by simp)).symm
    · have o6 : Vsa.Machine.output d6.σ = Vsa.Machine.output d.σ := by
        unfold Vsa.Machine.output; rw [p6.output, p5.output]
      rw [o6, out]
    · intro x hx
      rw [p6.memory, show writeLog d5.σ.mem [] = d5.σ.mem from rfl, mem5,
        writeLog_out _ _ _ (within.outL (by omega))]
  -- not a regular file: the console branch
  let kv : BitVec 64 := bytesVal .lw (read8 d2.σ.mem (kindAddress fd).toNat)
  have keep3 := fun n lo hi (hn : n ∉ [11, 13, 14, 15, 16]) => p3.toEffectPost.gpr_frame (by decide) n lo hi hn
  have ra3 : gpr d3 1 = some ra := (keep3 1 (by decide) (by decide) (by simp)).trans
    ((keep2 1 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl))
  let R3 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 10 then fd else kv
  have e3 := console_fast d3 R3 ⟨p3.good, p3.image, p3.minstret, ra3, h.aligned, p3.tick⟩
    ⟨ra3, (keep3 10 (by decide) (by decide) (by simp)).trans
      ((keep2 10 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl)),
      gholds_lookup _ p3.regs rfl, True.intro⟩
    (by show guardB .BNE kv 4#64 = true
        simp only [kv]; rw [kindRead]; simp [guardB, D.notFile])
  obtain ⟨d4, run4, p4⟩ := e3.run d3 ⟨p3.pc, rfl⟩
  have ok4 := p4.loopOk (p3.loopOk ok2)
  have keep4 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [11, 12, 13, 14, 15, 16] → gpr d4 n = gpr d1 n := fun n lo hi hn => by
    rw [p4.toEffectPost.gpr_frame (by decide) n lo hi (by simp at hn ⊢; omega),
      keep3 n lo hi (by simp at hn ⊢; omega), keep2 n lo hi (by simp at hn ⊢; omega)]
  have mem4 : d4.σ.mem = writeLog c.σ.mem (entryLog R0) := by
    rw [p4.memory, show writeLog d3.σ.mem [] = d3.σ.mem from rfl, p3.memory,
      show writeLog d2.σ.mem [] = d2.σ.mem from rfl, p2.memory, show writeLog d1.σ.mem [] = d1.σ.mem from rfl, mem1]
  have out4 : Vsa.Machine.output d4.σ = Vsa.Machine.output c.σ := by
    unfold Vsa.Machine.output; rw [p4.output, p3.output, p2.output, p1.output]
  let R4 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 9 then len else if n = 10 then fd else buf
  have ra4 : gpr d4 1 = some ra := (keep4 1 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl)
  have regs4 : GHolds d4.σ (empty_input R4) := ⟨ra4,
    (keep4 9 (by decide) (by decide) (by simp)).trans len1,
    (keep4 10 (by decide) (by decide) (by simp)).trans (gholds_lookup _ p1.regs rfl),
    (keep4 18 (by decide) (by decide) (by simp)).trans buf1, True.intro⟩
  have leaf4 : LeafInput (R4 1) d4 := ⟨p4.good, p4.image, p4.minstret, ra4, h.aligned, p4.tick⟩
  have sp4 : gpr d4 2 = some (sp - 96#64) := (keep4 2 (by decide) (by decide) (by simp)).trans sp1
  have lenNat : len.toNat = bs.length := by
    have := h.ram.2.1; simp only [len, BitVec.toNat_ofNat]; omega
  by_cases zero : bs.length = 0
  · have e4 := empty_fast d4 R4 leaf4 regs4 (by simp only [R4, ↓reduceIte, Nat.reduceEqDiff, len, zero])
    obtain ⟨d5, run5, p5⟩ := e4.run d4 ⟨p4.pc, rfl⟩
    have keep5 := fun n lo hi (hn : n ∉ [11, 13, 14]) => p5.toEffectPost.gpr_frame (by decide) n lo hi hn
    obtain ⟨f, runf, post⟩ := finish d5 (p5.loopOk ok4) p5.image p5.minstret p5.pc
      ((keep5 1 (by decide) (by decide) (by simp)).trans ra4)
      ((keep5 2 (by decide) (by decide) (by simp)).trans sp4)
      (gholds_lookup _ p5.regs rfl) ⟨_, gholds_lookup (n := 10) _ p5.regs rfl⟩
      (by rw [p5.memory]; exact mem4)
      (by unfold Vsa.Machine.output; rw [p5.output]
          have := out4; unfold Vsa.Machine.output at this; rw [this, List.length_eq_zero_iff.mp zero]
          simp [bytesToString])
    exact ⟨f, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans runf)))), post⟩
  · have nonempty : 0 < bs.length := Nat.pos_of_ne_zero zero
    have e4 := start_fast d4 R4 leaf4 regs4 (by
      simp only [R4, ↓reduceIte, Nat.reduceEqDiff]
      intro eq
      have := congrArg BitVec.toNat eq
      rw [lenNat] at this
      exact zero (by simpa using this))
    obtain ⟨d5, run5, p5⟩ := e4.run d4 ⟨p4.pc, rfl⟩
    have ok5 := p5.loopOk ok4
    have keep5 := fun n lo hi (hn : n ∉ [11, 13, 14]) => p5.toEffectPost.gpr_frame (by decide) n lo hi hn
    have ra5 : gpr d5 1 = some ra := (keep5 1 (by decide) (by decide) (by simp)).trans ra4
    have mem5 : d5.σ.mem = writeLog c.σ.mem (entryLog R0) := by rw [p5.memory]; exact mem4
    have input : LoopInput ra buf bs d5 :=
      { good := p5.good, image := p5.image, minstret := p5.minstret, raReg := ra5, aligned := h.aligned,
        tick := p5.tick, ok := ok5,
        stop := by
          have l : gpr d5 13 = some (R4 18 + R4 9) := gholds_lookup _ p5.regs rfl
          rw [l]; rfl
        mask := gholds_lookup _ p5.regs rfl
        arg := ⟨_, gholds_lookup (n := 10) _ p5.regs rfl⟩
        ram := h.ram
        bytes := by
          intro i x hx
          have hi := (List.getElem?_eq_some_iff.mp hx).1
          rw [mem5, writeLog_out _ _ _ (within.outL ?_)]
          · exact h.bytes i x hx
          · rw [cursor_toNat h.ram.2.1 (Nat.le_of_lt hi)]
            have := L.buffer; omega }
    obtain ⟨d6, run6, frame6, pc6, out6⟩ := console_loop input nonempty p5.pc (gholds_lookup _ p5.regs rfl)
    let R6 : Nat → BitVec 64 := fun n => if n = 1 then ra else fd
    have ra6 : gpr d6 1 = some ra := (frame6.kept 1 (by decide) (by decide) (by simp)).trans ra5
    have a5 : gpr d5 10 = some fd := gholds_lookup _ p5.regs rfl
    have a6 : gpr d6 10 = some fd := (frame6.kept 10 (by decide) (by decide) (by simp)).trans a5
    have e6 := jump_fast d6 R6 ⟨frame6.ok.good, frame6.image, frame6.minstret, ra6, h.aligned, frame6.ok.tick⟩
      ⟨ra6, a6, True.intro⟩
    obtain ⟨d7, run7, p7⟩ := e6.run d6 ⟨pc6, rfl⟩
    have keep7 := fun n lo hi => p7.toEffectPost.gpr_frame (by decide) n lo hi (by simp)
    obtain ⟨f, runf, post⟩ := finish d7 (p7.loopOk frame6.ok) p7.image p7.minstret p7.pc
      ((keep7 1 (by decide) (by decide)).trans ra6)
      ((keep7 2 (by decide) (by decide)).trans ((frame6.kept 2 (by decide) (by decide) (by simp)).trans
        ((keep5 2 (by decide) (by decide) (by simp)).trans sp4)))
      ((keep7 9 (by decide) (by decide)).trans ((frame6.kept 9 (by decide) (by decide) (by simp)).trans
        ((keep5 9 (by decide) (by decide) (by simp)).trans ((keep4 9 (by decide) (by decide) (by simp)).trans len1))))
      ⟨_, (keep7 10 (by decide) (by decide)).trans a6⟩
      (by rw [p7.memory, show writeLog d6.σ.mem [] = d6.σ.mem from rfl, frame6.memory]; exact mem5)
      (by have o7 : Vsa.Machine.output d7.σ = Vsa.Machine.output d6.σ := by
            unfold Vsa.Machine.output; rw [p7.output]
          rw [o7, out6]
          have o5 : Vsa.Machine.output d5.σ = Vsa.Machine.output c.σ := by
            have := out4; unfold Vsa.Machine.output at this ⊢; rw [p5.output, this]
          rw [o5])
    exact ⟨f, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans runf)))))), post⟩
