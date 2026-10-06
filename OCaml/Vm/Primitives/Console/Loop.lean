import OCaml.Vm.Primitives.Console.Effects
import Vsa.Sim.DeriveLoop

/-! `_write`'s console loop: one HTIF putchar per buffer byte. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable

theorem bytesToString_snoc (bs : List UInt8) (x : UInt8) :
    bytesToString (bs ++ [x]) = bytesToString bs ++ toString (Char.ofNat (BitVec.ofNat 8 x.toNat).toNat) := by
  have hx : (BitVec.ofNat 8 x.toNat).toNat = x.toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.toNat_lt
  rw [hx]
  simp [bytesToString, String.ofList_append]
  rfl

/-- Machine health along the console loop. -/
structure LoopOk (d : Config) : Prop where
  good : GoodState d.σ
  tick : d.tick < 2
  htifIdle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)

theorem PutcharPost.loopOk {c d b} (post : PutcharPost c b d) : LoopOk d :=
  ⟨post.good, post.tick, post.idle⟩

theorem _root_.OCaml.Vm.Primitives.RegistersPost.loopOk {writes mem before after pc value regs}
    (post : RegistersPost writes mem before pc value regs after) (pre : LoopOk before) : LoopOk after := by
  refine ⟨post.good, post.tick, ?_⟩
  rw [post.frame _ (fun n _ => by
    have h := gprReg_htif_payload n
    exact fun eq => by rw [eq, beq_self_eq_true] at h; contradiction) (by decide)]
  exact pre.htifIdle

/-- Facts fixed for the whole loop, relative to its entry configuration `e`. -/
structure LoopFrame (e d : Config) : Prop where
  ok : LoopOk d
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  memory : d.σ.mem = e.σ.mem
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [11, 12, 15] → gpr d n = gpr e n

/-- At the loop head having printed `k` bytes, or finished after all of them. -/
inductive LoopState (e : Config) (buf : BitVec 64) (bs : List UInt8) :
    Config → Prop where
  | looping {d : Config} (k : Nat) (hk : k < bs.length) (frame : LoopFrame e d)
      (pc : pcOf d = some 0x80000f6c#64) (cursor : gpr d 11 = some (buf + BitVec.ofNat 64 k))
      (out : Vsa.Machine.output d.σ = Vsa.Machine.output e.σ ++ bytesToString (bs.take k)) :
      LoopState e buf bs d
  | finished {d : Config} (frame : LoopFrame e d) (pc : pcOf d = some 0x80000f84#64)
      (out : Vsa.Machine.output d.σ = Vsa.Machine.output e.σ ++ bytesToString bs) :
      LoopState e buf bs d

/-- The loop's entry: the end pointer, the putchar mask and the buffer bytes. -/
structure LoopInput (ra buf : BitVec 64) (bs : List UInt8) (e : Config) : Prop
    extends LeafInput ra e where
  ok : LoopOk e
  stop : gpr e 13 = some (buf + BitVec.ofNat 64 bs.length)
  mask : gpr e 14 = some (257#64 <<< 48)
  arg : ∃ v, gpr e 10 = some v
  ram : 0x80000000 ≤ buf.toNat ∧ buf.toNat + bs.length ≤ 0x100000000 ∧
    (buf.toNat + bs.length ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 8 ≤ buf.toNat)
  bytes : ∀ i x, bs[i]? = some x → (e.σ.mem[(buf + BitVec.ofNat 64 i).toNat]?).getD 0 = BitVec.ofNat 8 x.toNat

def loopMeasure (d : Config) : Nat := (((gpr d 13).getD 0) - ((gpr d 11).getD 0)).toNat


theorem putc_data (b : BitVec 8) :
    bytesVal .lbu [b] ||| 257#64 <<< 48 = putcWord b := by
  simp only [bytesVal, List.getD_cons_zero, putcWord]
  rw [BitVec.or_comm]
  congr 1


theorem cursor_toNat {buf : BitVec 64} {k len : Nat} (ram : buf.toNat + len ≤ 0x100000000) (hk : k ≤ len) :
    (buf + BitVec.ofNat 64 k).toNat = buf.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- One iteration from the loop head: a byte is loaded, printed by the HTIF
putchar store, and the back-edge returns to the head or exits. -/
theorem loop_iteration {ra buf bs e d} (h : LoopInput ra buf bs e) {k : Nat}
    (hk : k < bs.length) (frame : LoopFrame e d) (pc : pcOf d = some 0x80000f6c#64)
    (cursor : gpr d 11 = some (buf + BitVec.ofNat 64 k))
    (out : Vsa.Machine.output d.σ = Vsa.Machine.output e.σ ++ bytesToString (bs.take k)) :
    ∃ d', Steps d d' ∧ LoopState e buf bs d' ∧ loopMeasure d' < loopMeasure d := by
  obtain ⟨v, hv⟩ := h.arg
  have ram := h.ram
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  let R : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 10 then v else
    if n = 11 then buf + BitVec.ofNat 64 k else if n = 13 then buf + BitVec.ofNat 64 bs.length else 257#64 <<< 48
  have keep := frame.kept
  have leaf : LeafInput (R 1) d := ⟨frame.ok.good, frame.image, frame.minstret,
    (keep 1 (by decide) (by decide) (by decide)).trans h.raReg, h.aligned, frame.ok.tick⟩
  have regs : GHolds d.σ (byte_input R) := ⟨(keep 1 (by decide) (by decide) (by decide)).trans h.raReg,
    (keep 10 (by decide) (by decide) (by decide)).trans hv, cursor, (keep 13 (by decide) (by decide) (by decide)).trans h.stop,
    (keep 14 (by decide) (by decide) (by decide)).trans h.mask, True.intro⟩
  have address := cursor_toNat ram.2.1 (Nat.le_of_lt hk)
  have slot : ReadWindow (buf + BitVec.ofNat 64 k) 1 :=
    ⟨by rw [address]; omega, by rw [address]; have := ram.2.1; omega,
      by rw [address]; rcases ram.2.2 with below | above
         · exact Or.inl (by omega)
         · exact Or.inr (by omega)⟩
  obtain ⟨d1, run1, p1⟩ := (byte_fast d R leaf regs slot).run d ⟨pc, rfl⟩
  have ok1 := p1.loopOk frame.ok
  -- the loaded byte is the buffer's k-th byte
  have xk : bs[k]? = some bs[k] := List.getElem?_eq_getElem hk
  have byte : (d.σ.mem[(R 11).toNat]?).getD 0 = BitVec.ofNat 8 (bs[k]).toNat := by
    rw [frame.memory]; exact h.bytes k _ xk
  have data : gpr d1 15 = some (putcWord (BitVec.ofNat 8 (bs[k]).toNat)) := by
    rw [← putc_data, ← byte]; exact gholds_lookup _ p1.regs rfl
  obtain ⟨d2, step2, p2⟩ := putchar_step p1.good p1.image p1.tick p1.pc (gholds_lookup _ p1.regs rfl) data ok1.htifIdle
  have ok2 := p2.loopOk
  have kept2 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [11, 12, 15] → gpr d2 n = gpr e n := fun n lo hi hn => by
    rw [p2.gpr n, p1.toEffectPost.gpr_frame (by decide) n lo hi (by simpa using hn)]
    exact keep n lo hi hn
  have mem2 : d2.σ.mem = e.σ.mem := by rw [p2.memory, p1.memory]; exact frame.memory
  have out2 : Vsa.Machine.output d2.σ = Vsa.Machine.output e.σ ++ bytesToString (bs.take (k + 1)) := by
    rw [p2.output, show Vsa.Machine.output d1.σ = Vsa.Machine.output d.σ by
      unfold Vsa.Machine.output; rw [p1.output], out, List.take_add_one, xk, Option.toList_some,
      bytesToString_snoc, String.append_assoc]
  have next : gpr d2 11 = some (buf + BitVec.ofNat 64 (k + 1)) := by
    have l : gpr d1 11 = some (R 11 + 1#64) := gholds_lookup _ p1.regs rfl
    rw [p2.gpr 11, l]
    simp only [R, ↓reduceIte, Nat.reduceEqDiff]
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  let R2 : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 10 then v else
    if n = 11 then buf + BitVec.ofNat 64 (k + 1) else buf + BitVec.ofNat 64 bs.length
  have leaf2 : LeafInput (R2 1) d2 := ⟨p2.good, p2.image, p2.minstret,
    (kept2 1 (by decide) (by decide) (by decide)).trans h.raReg, h.aligned, p2.tick⟩
  have regs2 : GHolds d2.σ (again_input R2) := ⟨(kept2 1 (by decide) (by decide) (by decide)).trans h.raReg,
    (kept2 10 (by decide) (by decide) (by decide)).trans hv, next,
    (kept2 13 (by decide) (by decide) (by decide)).trans h.stop, True.intro⟩
  have stopNat := cursor_toNat (k := bs.length) ram.2.1 (Nat.le_refl _)
  have nextNat := cursor_toNat (k := k + 1) ram.2.1 hk
  have measure0 : loopMeasure d = bs.length - k := by
    unfold loopMeasure
    rw [(keep 13 (by decide) (by decide) (by decide)).trans h.stop, cursor]
    simp only [Option.getD_some]
    rw [BitVec.toNat_sub, stopNat, address]
    have := buf.isLt; omega
  have frame3 := fun {pc' : BitVec 64} {regs' : GRegs} {d3 : Config}
      (p3 : WriteRegistersPost [] [] d2 pc' (R2 10) regs' d3) =>
    (⟨p3.loopOk ok2, p3.image, p3.minstret, by rw [p3.memory]; exact mem2,
      fun n lo hi hn => (p3.toEffectPost.gpr_frame (by decide) n lo hi (by simp)).trans (kept2 n lo hi hn)⟩ :
      LoopFrame e d3)
  by_cases more : k + 1 < bs.length
  · have ne : R2 13 ≠ R2 11 := by
      simp only [R2, ↓reduceIte, Nat.reduceEqDiff]
      intro eq
      have := congrArg BitVec.toNat eq
      rw [stopNat, nextNat] at this
      omega
    obtain ⟨d3, run3, p3⟩ := (again_fast d2 R2 leaf2 regs2 ne).run d2 ⟨p2.pc, rfl⟩
    refine ⟨d3, run1.trans (.head step2 run3), .looping (k + 1) more (frame3 p3) p3.pc ?_ ?_, ?_⟩
    · rw [p3.toEffectPost.gpr_frame (by decide) 11 (by decide) (by decide) (by simp)]; exact next
    · unfold Vsa.Machine.output; rw [p3.output]; exact out2
    · rw [measure0]
      unfold loopMeasure
      rw [p3.toEffectPost.gpr_frame (by decide) 13 (by decide) (by decide) (by simp),
        p3.toEffectPost.gpr_frame (by decide) 11 (by decide) (by decide) (by simp),
        kept2 13 (by decide) (by decide) (by decide), h.stop, next]
      simp only [Option.getD_some]
      rw [BitVec.toNat_sub, stopNat, nextNat]
      have := buf.isLt; omega
  · have last : k + 1 = bs.length := by omega
    have eq : R2 13 = R2 11 := by simp only [R2, ↓reduceIte, Nat.reduceEqDiff, last]
    obtain ⟨d3, run3, p3⟩ := (done_fast d2 R2 leaf2 regs2 eq).run d2 ⟨p2.pc, rfl⟩
    refine ⟨d3, run1.trans (.head step2 run3), .finished (frame3 p3) p3.pc ?_, ?_⟩
    · unfold Vsa.Machine.output; rw [p3.output]
      have := out2; rw [last, List.take_length] at this; exact this
    · rw [measure0]
      unfold loopMeasure
      rw [p3.toEffectPost.gpr_frame (by decide) 13 (by decide) (by decide) (by simp),
        p3.toEffectPost.gpr_frame (by decide) 11 (by decide) (by decide) (by simp),
        kept2 13 (by decide) (by decide) (by decide), h.stop, next]
      simp only [Option.getD_some, last, BitVec.sub_self, BitVec.toNat_zero]
      omega


/-- The whole byte loop, from its head with a non-empty buffer, to its exit
having printed every byte. -/
theorem console_loop {ra buf bs e} (h : LoopInput ra buf bs e) (nonempty : 0 < bs.length)
    (pc : pcOf e = some 0x80000f6c#64) (cursor : gpr e 11 = some buf) :
    ∃ d, Steps e d ∧ LoopFrame e d ∧ pcOf d = some 0x80000f84#64 ∧
      Vsa.Machine.output d.σ = Vsa.Machine.output e.σ ++ bytesToString bs := by
  have body : ∀ n, Vsa.Logic.Triple
      (fun d => LoopState e buf bs d ∧ pcOf d = some 0x80000f6c#64 ∧ loopMeasure d = n)
      (fun d => LoopState e buf bs d ∧ loopMeasure d < n) := by
    intro n d pre
    obtain ⟨state, head, measure⟩ := pre
    cases state with
    | looping k hk frame _ cursor out =>
      obtain ⟨d', run, state', lt⟩ := loop_iteration h hk frame head cursor out
      exact ⟨d', run, state', measure ▸ lt⟩
    | finished _ pc' _ =>
      have bad : some (0x80000f84#64 : BitVec 64) = some 0x80000f6c#64 := pc'.symm.trans head
      exact absurd bad (by decide)
  have start : LoopState e buf bs e := .looping 0 nonempty
    ⟨h.ok, h.image, h.minstret, rfl, fun _ _ _ _ => rfl⟩ pc (by rw [cursor]; simp)
    (by simp [bytesToString])
  obtain ⟨d, run, state, stopped⟩ := loopFromBody loopMeasure body e start
  cases state with
  | looping _ _ _ pc' _ _ => exact absurd pc' stopped
  | finished frame pc' out => exact ⟨d, run, frame, pc', out⟩

end OCaml.Vm.Primitives.ConsoleWrite
