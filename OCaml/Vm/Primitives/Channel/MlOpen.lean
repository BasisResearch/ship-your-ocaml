import OCaml.Vm.Primitives.Channel.OpenDescriptorCall
import OCaml.Vm.Primitives.Channel.OpenOut
import OCaml.Vm.Gc.OpenChannels

/-! `caml_ml_open_descriptor_out(v)` as a call summary:
* untag the descriptor and open it with `caml_open_descriptor_in`
  (`open_descriptor_in`);
* mark the record an output channel the collector manages (`max := NULL`,
  `CHANNEL_FLAG_MANAGED_BY_GC`, one reference);
* wrap it in a custom block with `caml_alloc_custom_mem`, a named obligation
  (`CustomMemCall`) because it is the collector-integrated allocation;
* store the record in the block and return the block. -/
namespace OCaml.Vm.Primitives.Channel
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap LeanRV64DExecutable
open OCaml.Vm.Boot.Startup
open OCaml.Vm.Sim (FrameOnD)
open ExitPath (LogWithin)
set_option autoImplicit false
variable {live : Nat → Prop}

/-- `Int_val(v)` as the prologue computes it (`srai 1; sext.w`). -/
def fdOf (v : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.extractLsb 31 0 (Functions.shift_bits_right_arith v 1#6))

/-- The entry registers the prologue reads. -/
def outR (sp ra s0 v : BitVec 64) : Nat → BitVec 64 := fun n =>
  if n = 1 then ra else if n = 2 then sp else if n = 8 then s0 else v

/-- The prologue's two saves into its 16-byte frame. -/
def outSaveLog (sp ra s0 : BitVec 64) : List WEntry :=
  [((sp - 16#64 + 8#64).toNat, 8, ra), ((sp - 16#64).toNat, 8, s0)]

/-- The registers handed to `caml_open_descriptor_in`. -/
def outCallArgs (sp s0 v : BitVec 64) : GRegs :=
  [(10, fdOf v), (2, sp - 16#64), (8, s0)]

theorem outStack (sp : BitVec 64) : sp - 16#64 = nativeStack sp 16 := by
  rw [nativeStack, BitVec.sub_eq_add_neg]

theorem outFrame_word {sp} (frame : NativeFrame sp 16) {off : Nat} (bound : off + 8 ≤ 16)
    (aligned : off % 8 = 0) : WriteWindow (sp - 16#64 + BitVec.ofNat 64 off) 8 := by
  rw [BitVec.sub_eq_add_neg, frame.address _ (by omega)]
  exact frame.word bound aligned

theorem outFrame_slot {sp} (frame : NativeFrame sp 16) {off : Nat} (bound : off ≤ 16) :
    (sp - 16#64 + BitVec.ofNat 64 off).toNat = sp.toNat - 16 + off := by
  rw [BitVec.sub_eq_add_neg, frame.address _ bound, frame.slot_nat bound]
  rfl

theorem outSaveLog_inside {sp ra s0} (frame : NativeFrame sp 16) :
    LogInW [⟨sp.toNat - 16, sp.toNat⟩] (outSaveLog sp ra s0) := by
  have low := frame.lower
  have e0 := outFrame_slot frame (off := 0) (by decide)
  have e8 := outFrame_slot frame (off := 8) (by decide)
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at e0
  simp only [outSaveLog, LogInW, InsideW, e0]
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, e8]
  refine ⟨Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, trivial⟩
  all_goals omega

/-- What `caml_ml_open_descriptor_out(v)` needs: `open_descriptor_in`'s
premises for `Int_val(v)`, with room for the primitive's own 16-byte frame. -/
structure OutInput (live : Nat → Prop) (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra s0 s1 s2 v head : BitVec 64)
    (c : Config) : Prop where
  ready : RuntimeReadyL live H (capacity + charge) sp ra c
  frame : NativeFrame sp 592
  saved0 : gprGet c.σ 8 = some s0
  saved1 : gprGet c.σ 9 = some s1
  saved2 : gprGet c.σ 18 = some s2
  value : gprGet c.σ 10 = some v
  charged : vsaChg recordBytes charge
  runtime : ConsoleWrite.ConsoleRuntime c
  descriptor : SeekFd (fdOf v) c
  headWord : bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat) = head
  /-- The old head is a channel record: a live block of `H`, word-aligned. -/
  headLive : head ≠ 0#64 → (∃ e ∈ H, e.1 ≤ head.toNat ∧ head.toNat + 64 ≤ e.1 + e.2) ∧ head.toNat % 8 = 0

/-- At the entry of `caml_open_descriptor_in`: its premises one frame down,
after the prologue's two saves. -/
structure OutEntered (live : Nat → Prop) (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra s0 s1 s2 v head : BitVec 64)
    (c d : Config) : Prop where
  input : OpenInput live H capacity charge (sp - 16#64) OpenOut.pro_call.link s0 s1 s2 (fdOf v) head d
  pc : pcOf d = some 0x80015130#64
  memory : d.σ.mem = writeLog c.σ.mem (outSaveLog sp ra s0)
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 10] → gprGet d.σ n = gprGet c.σ n
  gprs : GprsKept c d

/-- From the entry of `caml_ml_open_descriptor_out` to the call of
`caml_open_descriptor_in`. -/
theorem out_enter (c : Config) {H : List (Nat × Nat)} {capacity charge : Nat}
    {sp ra s0 s1 s2 v head : BitVec 64} (h : OutInput live H capacity charge sp ra s0 s1 s2 v head c) :
    FnSummary 0x80015f50#64 (fun d => d = c) (OutEntered live H capacity charge sp ra s0 s1 s2 v head c) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have short := h.frame.resize (small := 16) (by decide) (by decide)
  have nested : NativeFrame (sp - 16#64) 576 := by
    rw [outStack]; exact h.frame.nested (front := 16) (by decide)
  have inside : LogInW [⟨sp.toNat - 16, sp.toNat⟩] (outSaveLog sp ra s0) := outSaveLog_inside short
  have insideBase : LogInW [⟨nativeFrameBase sp 16, sp.toNat⟩] (outSaveLog sp ra s0) := inside
  let R := outR sp ra s0 v
  obtain ⟨saved, run1, setup⟩ := (OpenOut.pro_fast c R h.ready.toLeafInput
    ⟨h.ready.raReg, h.ready.stack, h.saved0, h.value, trivial⟩
    (outFrame_word short (off := 8) (by decide) (by decide))
    (by
      show WriteWindow (sp - 16#64) 8
      have w := outFrame_word short (off := 0) (by decide) (by decide)
      rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at w)
    (short.image_outside insideBase)).run c ⟨pc, rfl⟩
  have savedReady : RuntimeReadyL live H (capacity + charge) (sp - 16#64) ra saved :=
    h.ready.stack_log setup (by decide) (by simp only [OpenOut.pro_regs, keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ setup.regs (by rfl))
      (gholds_lookup (n := 1) _ setup.regs (by rfl)) h.ready.aligned short insideBase
  have args : GHolds saved.σ (outCallArgs sp s0 v) :=
    holds_project setup.regs (by simp [outCallArgs, OpenOut.pro_regs, R, outR, lookupG, fdOf])
  obtain ⟨called, run2, call⟩ := (call_registers_summary OpenOut.pro_call_shape OpenOut.pro_call_decode saved
    (OpenOut.pro_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ args
    (by change KeysOK [10, 2, 8]; decide) (by simp only [KeysAvoidRa, keysG, outCallArgs]; decide)
    (by rfl)).run saved ⟨setup.pc, rfl⟩
  have calledReady : RuntimeReadyL live H (capacity + charge) (sp - 16#64) OpenOut.pro_call.link called :=
    savedReady.effect call (by decide)
      (by simp only [keysG, outCallArgs]; decide) (by decide)
      (gholds_lookup (n := 2) _ call.regs (by rfl))
      (gholds_lookup (n := 1) _ call.regs (by rfl)) (by decide)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have memory : called.σ.mem = writeLog c.σ.mem (outSaveLog sp ra s0) := by
    rw [call.memory, setup.memory]; rfl
  have lower := h.frame.lower
  have hSE : heapStart ≤ heapEnd := by decide
  have static : StaticKept c called :=
    StaticKept.of_log inside (fun a ⟨below, _, _⟩ => ⟨Or.inl (by
      show a < sp.toNat - 16
      arena_omega), trivial⟩) called memory
  have kept (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [1, 2, 10]) : gprGet called.σ n = gprGet c.σ n := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    exact (call.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      (setup.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega))
  have headBytes : read8 called.σ.mem (2147896128#64).toNat = read8 c.σ.mem (2147896128#64).toNat := by
    apply read8_keep
    intro i hi
    have hE : heapEnd = 0x86800000 := rfl
    rw [memory, frameOn_writeLog _ _ _ inside _ ⟨Or.inl (by
      show (2147896128#64).toNat + i < sp.toNat - 16
      rw [show (2147896128#64).toNat = 2147896128 from rfl]
      rw [hE] at lower; omega), trivial⟩]
  refine ⟨called, run1.trans run2, ?_⟩
  exact {
    input := {
      ready := calledReady
      frame := nested
      saved0 := gholds_lookup (n := 8) _ call.regs (by rfl)
      saved1 := (kept 9 (by decide) (by decide) (by decide)).trans h.saved1
      saved2 := (kept 18 (by decide) (by decide) (by decide)).trans h.saved2
      fdReg := gholds_lookup (n := 10) _ call.regs (by rfl)
      charged := h.charged
      runtime := h.runtime.keep static
      descriptor := h.descriptor.keep static
      headWord := by rw [headBytes]; exact h.headWord
      headLive := h.headLive }
    pc := call.pc
    memory := memory
    kept := kept
    gprs := (GprsKept.of_pins setup (by decide) (by decide) (by simp [keysG, OpenOut.pro_regs])).trans
      (GprsKept.of_pins call (by decide) (by decide) (by simp [keysG])) }

/-- `caml_open_descriptor_in` keeps x20–x27: the checked allocation keeps
them (`StatCheckedReturned.keep_upper`), and no other phase writes them. -/
theorem OpenedIn.keep_upper {H : List (Nat × Nat)} {capacity : Nat} {sp ra s0 s1 s2 fd head : BitVec 64}
    {c d : Config} (o : OpenedIn live H capacity sp ra s0 s1 s2 fd head c d) {k : Nat} {x : BitVec 64}
    (lo : 20 ≤ k) (hi : k ≤ 27) (h : gprGet c.σ k = some x) : gprGet d.σ k = some x := by
  have a := (o.allocation.setup.toEffectPost.gpr_frame (by decide) k (by omega) (by omega)
    (by simp; omega)).trans h
  have b := (o.allocation.call.toEffectPost.gpr_frame (by decide) k (by omega) (by omega)
    (by simp; omega)).trans a
  have e := o.allocation.allocation.keep_upper lo hi b
  have f := (o.seek.kept k (by omega) (by omega) (by simp; omega)).trans e
  exact (o.link.kept k (by omega) (by omega) (by simp; omega)).trans f

/-! ### The record's words -/

/-- A record word's address, inside the arena. -/
theorem recordAt {p : BitVec 64} (high : p.toNat + recordBytes ≤ heapEnd) {k : Nat} (bound : k ≤ 65608) :
    (p + BitVec.ofNat 64 k).toNat = p.toNat + k :=
  record_toNat (by unfold recordBytes at high; omega)

/-- One byte as a one-byte total read. -/
theorem bytesT_one_byte (m : Std.ExtHashMap Nat (BitVec 8)) (x : Nat) : bytesT m x 1 = (m[x]?).getD 0 := by
  simp only [bytesT]
  change (0#0).append ((m[x]?).getD 0) = _
  rw [BitVec.append]
  simp

/-- The bytes of a zero word. -/
theorem byte_of_zero {m : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} (h : bytesT m a 8 = 0#64) {j : Nat}
    (hj : j < 8) : (m[a + j]?).getD 0 = 0#8 := by
  have e := bytesT_extract m a 8 j 1 (by omega)
  rw [h, bytesT_one_byte] at e
  rw [← e]
  simp

/-- A signed word load of four zero bytes. -/
theorem lw_zero {m : Std.ExtHashMap Nat (BitVec 8)} {x : Nat}
    (z : ∀ j, j < 4 → (m[x + j]?).getD 0 = 0#8) : bytesVal .lw (read8 m x) = 0#64 := by
  have z0 := z 0 (by decide)
  rw [Nat.add_zero] at z0
  simp only [bytesVal, read8, List.getD_cons_zero, List.getD_cons_succ, z0, z 1 (by decide),
    z 2 (by decide), z 3 (by decide)]
  decide

/-- The record as `caml_open_descriptor_in` leaves it: `fd`, `offset`, `end`,
`curr`, `next`, and `refcount`/`flags` zero. -/
structure OpenedRecord (m : Std.ExtHashMap Nat (BitVec 8)) (p fd head : BitVec 64) : Prop where
  fd : bytesT m p.toNat 4 = fd.setWidth 32
  offset : bytesT m (p.toNat + 8) 8 = -1#64
  bufEnd : bytesT m (p.toNat + 16) 8 = p + (65536#64 + 72#64)
  curr : bytesT m (p.toNat + 24) 8 = p + 72#64
  next : bytesT m (p.toNat + 48) 8 = head
  zero : bytesT m (p.toNat + 64) 8 = 0#64

/-- The record `caml_ml_open_descriptor_out` returns (`runtime/caml/io.h`):
an output channel (`max = NULL`) with one reference, managed by the
collector (`CHANNEL_FLAG_MANAGED_BY_GC`), its buffer empty. -/
structure OutRecord (m : Std.ExtHashMap Nat (BitVec 8)) (p fd head : BitVec 64) : Prop where
  fd : bytesT m p.toNat 4 = fd.setWidth 32
  offset : bytesT m (p.toNat + 8) 8 = -1#64
  bufEnd : bytesT m (p.toNat + 16) 8 = p + (65536#64 + 72#64)
  curr : bytesT m (p.toNat + 24) 8 = p + 72#64
  max : bytesT m (p.toNat + 32) 8 = 0#64
  next : bytesT m (p.toNat + 48) 8 = head
  refcount : bytesT m (p.toNat + 64) 4 = 1#32
  flags : bytesT m (p.toNat + 68) 4 = 4#32

/-- The record's words read the same when its first 72 bytes do. -/
theorem OutRecord.keep {m m' : Std.ExtHashMap Nat (BitVec 8)} {p fd head : BitVec 64}
    (h : OutRecord m p fd head)
    (same : ∀ a, p.toNat ≤ a → a < p.toNat + 72 → (m'[a]?).getD 0 = (m[a]?).getD 0) :
    OutRecord m' p fd head := by
  have k (off n : Nat) (bound : off + n ≤ 72) : bytesT m' (p.toNat + off) n = bytesT m (p.toNat + off) n :=
    bytesT_keep fun j hj => same _ (by omega) (by omega)
  have k0 : bytesT m' p.toNat 4 = bytesT m p.toNat 4 := k 0 4 (by decide)
  exact ⟨k0 ▸ h.fd, (k 8 8 (by decide)) ▸ h.offset, (k 16 8 (by decide)) ▸ h.bufEnd,
    (k 24 8 (by decide)) ▸ h.curr, (k 32 8 (by decide)) ▸ h.max, (k 48 8 (by decide)) ▸ h.next,
    (k 64 4 (by decide)) ▸ h.refcount, (k 68 4 (by decide)) ▸ h.flags⟩

/-- **The returned record represents BcSem's new output channel** (`openChan`
on a stream: `offset = -1`, empty buffer). -/
theorem OutRecord.chanAt {c : Config} {p fd head : BitVec 64} {cfd : Int}
    (h : OutRecord c.σ.mem p fd head) (fdInt : (fd.setWidth 32).toInt = cfd) (open_ : cfd ≠ -1)
    (high : p.toNat + recordBytes ≤ heapEnd) (align : p.toNat % 16 = 0) :
    OCaml.Vm.ChanAt c p.toNat ⟨cfd, true, [], [], 0, -1⟩ := by
  have t (k : Nat) (b : k ≤ 65608) := recordAt (p := p) high b
  have e72 : (p + 72#64).toNat = p.toNat + 72 := t 72 (by decide)
  have eEnd : (p + (65536#64 + 72#64)).toNat = p.toNat + 65608 := by
    rw [show (65536#64 + 72#64 : BitVec 64) = BitVec.ofNat 64 65608 from rfl]; exact t 65608 (by decide)
  simp only [OCaml.Vm.ChanAt, OCaml.Vm.word, OCaml.Vm.word32, OCaml.Vm.chanOffFd, OCaml.Vm.chanOffOffset,
    OCaml.Vm.chanOffCurr, OCaml.Vm.chanOffMax, OCaml.Vm.chanOffEnd, OCaml.Vm.chanOffFlags,
    OCaml.Vm.chanOffBuff, OCaml.Vm.chanFlagUnbuffered, Chan.cursor, Chan.buffer, open_, ite_false,
    ite_true, Nat.add_zero, List.length_nil, h.fd, h.offset, h.curr, h.max, h.bufEnd, h.flags, e72, eEnd]
  exact ⟨fdInt, by simp, trivial, rfl, by unfold ioBufferSize; omega, by decide, by simp,
    Nat.zero_le _, Nat.zero_le _, by omega⟩

/-- `caml_ml_open_descriptor_out`'s three record stores: `max := NULL`, the
GC flag and the reference. -/
def outFlagsLog (p : BitVec 64) : List WEntry :=
  [(p.toNat + 32, 8, 0#64), (p.toNat + 68, 4, 4#64), (p.toNat + 64, 4, 1#64)]

theorem outFlagsLog_within {p : BitVec 64} :
    LogWithin (outFlagsLog p) p.toNat (p.toNat + 72) := by
  intro e he
  simp only [outFlagsLog, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> (dsimp only; omega)

theorem OpenedRecord.flags {m : Std.ExtHashMap Nat (BitVec 8)} {p fd head : BitVec 64}
    (h : OpenedRecord m p fd head) : OutRecord (writeLog m (outFlagsLog p)) p fd head := by
  have out (x n : Nat) (sep : x + n ≤ p.toNat + 32 ∨ (p.toNat + 40 ≤ x ∧ x + n ≤ p.toNat + 64)) :
      bytesT (writeLog m (outFlagsLog p)) x n = bytesT m x n := by
    apply bytesT_writeLog_out
    simp only [outFlagsLog, OutLRange, and_true]
    omega
  have split : outFlagsLog p = [(p.toNat + 32, 8, 0#64), (p.toNat + 68, 4, 4#64)] ++ [(p.toNat + 64, 4, 1#64)] := rfl
  have split' : [(p.toNat + 32, 8, 0#64), (p.toNat + 68, 4, 4#64)] =
      [(p.toNat + 32, 8, 0#64)] ++ [(p.toNat + 68, 4, 4#64)] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [out _ _ (Or.inl (by omega))]; exact h.fd
  · rw [out _ _ (Or.inl (by omega))]; exact h.offset
  · rw [out _ _ (Or.inl (by omega))]; exact h.bufEnd
  · rw [out _ _ (Or.inl (by omega))]; exact h.curr
  · exact OCaml.Vm.Gc.word_writeLog_at m (outFlagsLog p) 0 _ _ rfl
      (by simp only [outFlagsLog, List.drop, OutLRange, and_true]; omega)
  · rw [out _ _ (Or.inr ⟨by omega, by omega⟩)]; exact h.next
  · rw [split, writeLog_append, word32_writeLog]; rfl
  · rw [split, writeLog_append, bytesT_writeLog_out _ (by simp only [OutLRange, and_true]; omega),
      split', writeLog_append, word32_writeLog]; rfl

/-- The flags block's stores, with the zero `refcount`/`flags` word read. -/
theorem flagsLog_eq {m : Std.ExtHashMap Nat (BitVec 8)} {p : BitVec 64} {R : Nat → BitVec 64}
    (record : R 10 = p) (high : p.toNat + recordBytes ≤ heapEnd)
    (zero : bytesT m (p.toNat + 64) 8 = 0#64) :
    OpenOut.flagsLog R (OpenOut.flags_loads m R) = outFlagsLog p := by
  have z (j : Nat) (hj : j < 8) := byte_of_zero zero hj
  have a68 : (p + 68#64).toNat = p.toNat + 68 := recordAt high (k := 68) (by decide)
  have a64 : (p + 64#64).toNat = p.toNat + 64 := recordAt high (k := 64) (by decide)
  have a32 : (p + 32#64).toNat = p.toNat + 32 := recordAt high (k := 32) (by decide)
  have l68 : bytesVal .lw (read8 m (p.toNat + 68)) = 0#64 :=
    lw_zero fun j hj => by rw [show p.toNat + 68 + j = p.toNat + 64 + (4 + j) by omega]; exact z _ (by omega)
  have l64 : bytesVal .lw (read8 m (p.toNat + 64)) = 0#64 :=
    lw_zero fun j hj => z j (by omega)
  simp only [OpenOut.flagsLog, OpenOut.flags_loads, record, a68, a64, a32, List.getD_cons_zero,
    List.getD_cons_succ, l68, l64, outFlagsLog]
  rfl

/-- A fresh block lies apart from every range inside a live block. -/
theorem fresh_apart {H : List (Nat × Nat)} {p n : Nat}
    (fresh : ∀ e ∈ H, ∀ y, InExt (p, n) y → ¬ InExt e y) (pos : 0 < n)
    {e : Nat × Nat} (he : e ∈ H) {x k : Nat} (kpos : 0 < k) (lo : e.1 ≤ x) (hi : x + k ≤ e.1 + e.2) :
    x + k ≤ p ∨ p + n ≤ x := by
  rcases Nat.lt_or_ge p (x + k) with l | l
  · rcases Nat.lt_or_ge x (p + n) with g | g
    · exfalso
      rcases Nat.le_total p x with o | o
      · exact fresh e he x ⟨o, by dsimp only; omega⟩ ⟨lo, by omega⟩
      · exact fresh e he p ⟨Nat.le_refl _, by dsimp only; omega⟩ ⟨by omega, by omega⟩
    · exact Or.inr g
  · exact Or.inl l

/-- The list update misses every range above the list head's word and apart
from the old head's `prev`. -/
theorem linkLog_out {p head : BitVec 64} {x n : Nat} (above : 2147896136 ≤ x)
    (prev : head ≠ 0#64 → x + n ≤ (head + 56#64).toNat ∨ (head + 56#64).toNat + 8 ≤ x) :
    OutLRange (linkLog p head) x n := by
  by_cases hz : head = 0#64
  · simp only [linkLog, hz, ite_true, List.nil_append, OutLRange, and_true]
    omega
  · simp only [linkLog, hz, ite_false, List.singleton_append, OutLRange, and_true]
    exact ⟨prev hz, by omega⟩

/-- The record and the list head as `caml_open_descriptor_in` returns them. -/
theorem OpenedIn.record_words {H : List (Nat × Nat)} {capacity charge : Nat}
    {sp ra s0 s1 s2 fd head : BitVec 64} {c d : Config}
    (h : OpenInput live H capacity charge sp ra s0 s1 s2 fd head c)
    (o : OpenedIn live H capacity sp ra s0 s1 s2 fd head c d) :
    OpenedRecord d.σ.mem o.record fd head ∧ bytesT d.σ.mem 2147896128 8 = o.record := by
  have low := o.low
  have high := o.high
  unfold recordBytes at high
  have hS : heapStart = 0x8007d140 := rfl
  have t (k : Nat) (bound : k ≤ 65608) := recordAt (p := o.record) o.high bound
  -- the old head's `prev` lies apart from the record
  have prevApart (hz : head ≠ 0#64) {x n : Nat} (inside : o.record.toNat ≤ x) (hi : x + n ≤ o.record.toNat + 65616) :
      x + n ≤ (head + 56#64).toNat ∨ (head + 56#64).toNat + 8 ≤ x := by
    obtain ⟨⟨e, he, lo, hi'⟩, _⟩ := h.headLive hz
    have bounds := h.ready.heap.block_bounds (q := e.1) (n := e.2) he
    have prevNat : (head + 56#64).toNat = head.toNat + 56 := record_toNat (by omega)
    rw [prevNat]
    rcases fresh_apart o.fresh (by unfold recordBytes; decide) he (x := head.toNat + 56) (k := 8)
      (by decide) (by omega) (by omega) with l | l
    · right; omega
    · left; unfold recordBytes at l; omega
  have linkOut {x n : Nat} (inside : o.record.toNat ≤ x) (hi : x + n ≤ o.record.toNat + 65616) :
      OutLRange (linkLog o.record head) x n :=
    linkLog_out (by rw [hS] at low; omega) fun hz => prevApart hz inside hi
  have mem : d.σ.mem = writeLog (writeLog o.linked.σ.mem (recordInitLog o.record head)) (linkLog o.record head) := by
    rw [o.link.memory, writeLog_append]
  have init (x n : Nat) (inside : o.record.toNat ≤ x) (hi : x + n ≤ o.record.toNat + 65616) :
      bytesT d.σ.mem x n = bytesT (writeLog o.linked.σ.mem (recordInitLog o.record head)) x n := by
    rw [mem, bytesT_writeLog_out _ (linkOut inside hi)]
  have word (i k : Nat) (v : BitVec 64) (bound : k ≤ 65608)
      (entry : (recordInitLog o.record head)[i]? = some ((o.record + BitVec.ofNat 64 k).toNat, 8, v))
      (later : OutLRange ((recordInitLog o.record head).drop (i + 1)) (o.record.toNat + k) 8) :
      bytesT d.σ.mem (o.record.toNat + k) 8 = v := by
    rw [init _ _ (by omega) (by omega)]
    have e := OCaml.Vm.Gc.word_writeLog_at o.linked.σ.mem _ i _ v entry (by rw [t k bound]; exact later)
    rwa [t k bound] at e
  have recInit : ∀ x n, OutLRange (recordInitLog o.record head) x n ↔
      ((x + n ≤ o.record.toNat + 40 ∨ o.record.toNat + 40 + 8 ≤ x) ∧
       (x + n ≤ o.record.toNat + 64 ∨ o.record.toNat + 64 + 8 ≤ x) ∧
       (x + n ≤ o.record.toNat + 56 ∨ o.record.toNat + 56 + 8 ≤ x) ∧
       (x + n ≤ o.record.toNat + 16 ∨ o.record.toNat + 16 + 8 ≤ x) ∧
       (x + n ≤ o.record.toNat + 32 ∨ o.record.toNat + 32 + 8 ≤ x) ∧
       (x + n ≤ o.record.toNat + 24 ∨ o.record.toNat + 24 + 8 ≤ x) ∧
       (x + n ≤ o.record.toNat + 48 ∨ o.record.toNat + 48 + 8 ≤ x) ∧
       (x + n ≤ o.record.toNat + 65608 ∨ o.record.toNat + 65608 + 8 ≤ x)) := by
    intro x n
    simp only [recordInitLog, OutLRange, endAddress, and_true]
    rw [show (40#64 : BitVec 64) = BitVec.ofNat 64 40 from rfl, t 40 (by decide),
      show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, t 64 (by decide),
      show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, t 56 (by decide),
      show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, t 16 (by decide),
      show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, t 32 (by decide),
      show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, t 24 (by decide),
      show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, t 48 (by decide), t 65608 (by decide)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [init _ _ (Nat.le_refl _) (by omega),
      bytesT_writeLog_out _ ((recInit _ _).mpr (by omega))]
    exact o.seek.fdWord
  · rw [init _ _ (by omega) (by omega), bytesT_writeLog_out _ ((recInit _ _).mpr (by omega))]
    exact o.seek.offsetWord
  · exact word 3 16 _ (by decide) rfl (by
      simp only [recordInitLog, List.drop, OutLRange, endAddress, and_true]
      rw [show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, t 32 (by decide),
        show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, t 24 (by decide),
        show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, t 48 (by decide), t 65608 (by decide)]
      omega)
  · exact word 5 24 _ (by decide) rfl (by
      simp only [recordInitLog, List.drop, OutLRange, endAddress, and_true]
      rw [show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, t 48 (by decide), t 65608 (by decide)]
      omega)
  · exact word 6 48 _ (by decide) rfl (by
      simp only [recordInitLog, List.drop, OutLRange, endAddress, and_true]
      rw [t 65608 (by decide)]
      omega)
  · exact word 1 64 _ (by decide) rfl (by
      simp only [recordInitLog, List.drop, OutLRange, endAddress, and_true]
      rw [show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, t 56 (by decide),
        show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, t 16 (by decide),
        show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, t 32 (by decide),
        show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, t 24 (by decide),
        show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, t 48 (by decide), t 65608 (by decide)]
      omega)
  · have split : recordInitLog o.record head ++ linkLog o.record head =
        (recordInitLog o.record head ++ (if head = 0#64 then [] else [((head + 56#64).toNat, 8, o.record)])) ++
          [(2147896128, 8, o.record)] := by
      rw [linkLog, List.append_assoc]
    rw [o.link.memory, split, writeLog_append]
    exact OCaml.Vm.Gc.word_writeLog_at _ [(2147896128, 8, o.record)] 0 _ _ rfl trivial

/-! ### The flags block and the custom block -/

/-- The registers handed to `caml_alloc_custom_mem(&channel_operations,
sizeof(struct channel *), sizeof(struct channel))`, with the record in `s0`. -/
def customArgs (sp p : BitVec 64) : GRegs :=
  [(10, 2147891728#64), (11, 8#64), (12, 65616#64), (8, p), (2, sp)]

/-- At the call of `caml_alloc_custom_mem`: the record's three stores done. -/
structure OutFlagged (sp p : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  pc : pcOf d = some 0x800247f8#64
  link : gprGet d.σ 1 = some OpenOut.flags_call.link
  regs : GHolds d.σ (customArgs sp p)
  memory : d.σ.mem = writeLog c.σ.mem (outFlagsLog p)
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 8, 10, 11, 12, 14, 15] → gprGet d.σ n = gprGet c.σ n
  gprs : GprsKept c d

/-- From `caml_open_descriptor_in`'s return to the call of
`caml_alloc_custom_mem`: `max := NULL`, the GC flag, one reference. -/
theorem out_flags (o : Config) {sp p : BitVec 64} (leaf : LeafInput OpenOut.pro_call.link o)
    (stack : gprGet o.σ 2 = some sp) (record : gprGet o.σ 10 = some p)
    (low : heapStart ≤ p.toNat) (high : p.toNat + recordBytes ≤ heapEnd) (align : p.toNat % 16 = 0)
    (zero : bytesT o.σ.mem (p.toNat + 64) 8 = 0#64) :
    FnSummary 0x80015f68#64 (fun d => d = o) (OutFlagged sp p o) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  let R : Nat → BitVec 64 := fun n => if n = 1 then OpenOut.pro_call.link else if n = 2 then sp else p
  have hlog := flagsLog_eq (m := o.σ.mem) (R := R) rfl high zero
  have t (k : Nat) (b : k ≤ 65608) := recordAt (p := p) high b
  have win (k n : Nat) (b : k + n ≤ 72) (al : (p.toNat + k) % n = 0) : WriteWindow (p + BitVec.ofNat 64 k) n :=
    heapWindow (by rw [t k (by omega)]; omega) (by rw [t k (by omega)]; unfold recordBytes at high; omega)
      (by rw [t k (by omega)]; exact al)
  have inside : LogInW [⟨heapStart, heapEnd⟩] (outFlagsLog p) :=
    OCaml.Vm.Primitives.Channel.LogWithin.inW
      (OCaml.Vm.Primitives.Channel.LogWithin.widen outFlagsLog_within low
        (by unfold recordBytes at high; omega))
  obtain ⟨flagged, run1, F⟩ := (OpenOut.flags_fast o R leaf ⟨leaf.raReg, stack, record, trivial⟩
    (win 68 4 (by decide) (by omega)).read (win 64 4 (by decide) (by omega)).read
    (win 32 8 (by decide) (by omega)) (win 68 4 (by decide) (by omega)) (win 64 4 (by decide) (by omega))
    (by rw [hlog]; exact heap_image_outside inside)).run o ⟨pc, rfl⟩
  have args : GHolds flagged.σ (customArgs sp p) :=
    holds_project F.regs (by simp [customArgs, OpenOut.flags_regs, R, lookupG])
  obtain ⟨called, run2, call⟩ := (call_registers_summary OpenOut.flags_call_shape OpenOut.flags_call_decode
    flagged (OpenOut.flags_call_pins F.image) F.good F.image F.tick F.minstret _ args
    (by change KeysOK [10, 11, 12, 8, 2]; decide) (by simp only [KeysAvoidRa, keysG, customArgs]; decide)
    (by rfl)).run flagged ⟨F.pc, rfl⟩
  refine ⟨called, run1.trans run2, ?_⟩
  exact {
    good := call.good, image := call.image, minstret := call.minstret, tick := call.tick
    pc := by rw [call.pc, OpenOut.flags_call_target]
    link := gholds_lookup (n := 1) _ call.regs (by rfl)
    regs := holds_project call.regs (by simp [customArgs, lookupG])
    memory := by rw [call.memory, F.memory, hlog]; rfl
    kept := fun n lo hi hn => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      exact (call.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
        (F.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega))
    gprs := (GprsKept.of_pins F (by decide) (by decide) (by simp [keysG, OpenOut.flags_regs])).trans
      (GprsKept.of_pins call (by decide) (by decide) (by simp [keysG])) }

/-- At the call of `caml_alloc_custom_mem` from `caml_ml_open_descriptor_out`
entered at `c` with stack `sp`: the record `p` is a fresh block of the
allocator, and memory reads as at `c` outside the opening's windows, the
allocator's footprint and the primitive's frame. -/
structure CustomMemInput (H : List (Nat × Nat)) (capacity : Nat) (sp p head : BitVec 64)
    (c f : Config) : Prop where
  leaf : LeafInput OpenOut.flags_call.link f
  pc : pcOf f = some 0x800247f8#64
  regs : GHolds f.σ (customArgs (sp - 16#64) p)
  frame : NativeFrame (sp - 16#64) 576
  heap : HeapReady ((p.toNat, recordBytes) :: H) capacity f
  low : heapStart ≤ p.toNat
  high : p.toNat + recordBytes ≤ heapEnd
  static : StaticKept c f
  kept : ∀ a, OutW (openWindows (sp - 16#64) p head) a → ¬ vsaFoot H a →
    (a < sp.toNat - 16 ∨ sp.toNat ≤ a) → (f.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0

/-- `caml_alloc_custom_mem` returned the custom block `v`: its operations
word set, its data word writable and apart from the record, the callee-saved
registers, the caller's frame, the record and the list head kept. -/
structure CustomMemReturned (sp p v : BitVec 64) (f d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ x, d.σ.regs.get? Register.minstret = some x
  tick : d.tick < 2
  link : ∃ r, gprGet d.σ 1 = some r ∧ r.toNat % 4 = 0
  pc : pcOf d = some OpenOut.flags_call.link
  stack : gprGet d.σ 2 = some (sp - 16#64)
  record : gprGet d.σ 8 = some p
  result : gprGet d.σ 10 = some v
  saved : ∀ n ∈ [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet d.σ n = gprGet f.σ n
  gprs : GprsKept f d
  block : heapStart ≤ v.toNat ∧ v.toNat + 16 ≤ heapEnd ∧ v.toNat % 8 = 0
  apart : v.toNat + 16 ≤ p.toNat ∨ p.toNat + recordBytes ≤ v.toNat
  ops : bytesT d.σ.mem v.toNat 8 = 2147891728#64
  callerFrame : ∀ a, sp.toNat - 16 ≤ a → a < sp.toNat → (d.σ.mem[a]?).getD 0 = (f.σ.mem[a]?).getD 0
  recordKept : ∀ a, p.toNat ≤ a → a < p.toNat + recordBytes → (d.σ.mem[a]?).getD 0 = (f.σ.mem[a]?).getD 0
  headKept : ∀ a, 2147896128 ≤ a → a < 2147896136 → (d.σ.mem[a]?).getD 0 = (f.σ.mem[a]?).getD 0

/-- **`caml_alloc_custom_mem` returns a custom block** (named obligation,
a6-gc). It is the collector-integrated allocation: `Alloc_small` in the minor
heap, the custom table, the GC speed accounting. `Ready` is the collector's
state at the primitive's entry `c`, which a6-gc chooses; the call sees `c`'s
memory except for the opening's stores (`CustomMemInput.kept`). -/
def CustomMemCall (Ready : Config → Prop) : Prop :=
  ∀ (H : List (Nat × Nat)) (capacity : Nat) (sp p head : BitVec 64) (c f : Config),
    Ready c → CustomMemInput H capacity sp p head c f →
    FnSummary 0x800247f8#64 (fun d => d = f) (fun d => ∃ v, CustomMemReturned sp p v f d)

/-- The return: the record stored in the block, the saved `ra`/`s0` reloaded. -/
structure OutDone (sp ra s0 p v : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ x, d.σ.regs.get? Register.minstret = some x
  tick : d.tick < 2
  pc : pcOf d = some ra
  raReg : gprGet d.σ 1 = some ra
  stack : gprGet d.σ 2 = some sp
  result : gprGet d.σ 10 = some v
  s0Reg : gprGet d.σ 8 = some s0
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 8] → gprGet d.σ n = gprGet c.σ n
  gprs : GprsKept c d
  memory : d.σ.mem = writeLog c.σ.mem [((v + 8#64).toNat, 8, p)]

theorem out_done (a : Config) {sp ra s0 p v : BitVec 64} {f : Config}
    (ret : CustomMemReturned sp p v f a) (frame : NativeFrame sp 592)
    (savedRa : bytesT a.σ.mem (sp.toNat - 8) 8 = ra) (savedS0 : bytesT a.σ.mem (sp.toNat - 16) 8 = s0)
    (raAligned : ra.toNat % 4 = 0) :
    FnSummary 0x80015fa0#64 (fun d => d = a) (OutDone sp ra s0 p v a) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨r, rReg, rAligned⟩ := ret.link
  obtain ⟨vLow, vHigh, vAlign⟩ := ret.block
  have lower := frame.lower
  have upper := frame.upper
  have short := frame.resize (small := 16) (by decide) (by decide)
  have s8 : (sp - 16#64 + 8#64).toNat = sp.toNat - 8 := by
    have e := outFrame_slot short (off := 8) (by decide); rw [e]; omega
  have s0' : (sp - 16#64).toNat = sp.toNat - 16 := by
    have e := outFrame_slot short (off := 0) (by decide)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at e; rw [e]; omega
  have v8 : (v + 8#64).toNat = v.toNat + 8 := record_toNat (off := 8) (by omega)
  have hE : heapEnd = 0x86800000 := rfl
  have read (x : BitVec 64) (k : Nat) (hx : x.toNat = sp.toNat - 16 + k) (bound : k ≤ 8) : ReadWindow x 8 :=
    ⟨by rw [hx]; rw [hE] at lower; omega, by rw [hx]; unfold Layout.sym_stack_top at upper; omega,
      Or.inr (by rw [hx]; unfold Layout.sym_tohost; rw [hE] at lower; omega)⟩
  have out (k : Nat) (bound : k ≤ 8) : OutLRange [((v + 8#64).toNat, 8, p)] (sp.toNat - 16 + k) 8 := by
    simp only [OutLRange, and_true, v8]; arena_omega
  let R : Nat → BitVec 64 := fun n => if n = 1 then r else if n = 2 then sp - 16#64 else if n = 8 then p else v
  have raSlot : bytesVal .ld (read8 a.σ.mem (sp - 16#64 + 8#64).toNat) = ra := by
    rw [read8_value, s8]; exact savedRa
  obtain ⟨d, run, post⟩ := (OpenOut.done_fast a ra R ⟨ret.good, ret.image, ret.minstret, rReg, rAligned, ret.tick⟩
    ⟨ret.stack, ret.record, ret.result, trivial⟩
    (heapWindow (x := v + 8#64) (by rw [v8]; arena_omega) (by rw [v8]; arena_omega) (by rw [v8]; omega))
    (read (sp - 16#64 + 8#64) 8 (by rw [s8]; omega) (by decide))
    (by show OutLRange [((v + 8#64).toNat, 8, p)] (sp - 16#64 + 8#64).toNat 8; rw [s8]
        have o := out 8 (by decide); rwa [show sp.toNat - 16 + 8 = sp.toNat - 8 by omega] at o)
    (read (sp - 16#64) 0 (by rw [s0']; rfl) (by decide))
    (by show OutLRange [((v + 8#64).toNat, 8, p)] (sp - 16#64).toNat 8; rw [s0']; exact out 0 (by decide))
    (by
      show ImageOutside [((v + 8#64).toNat, 8, p)]
      exact heap_image_outside ⟨Or.inl ⟨by rw [v8]; arena_omega, by rw [v8]; arena_omega⟩, trivial⟩)
    raSlot raAligned).run a ⟨pc, rfl⟩
  refine ⟨d, run, ?_⟩
  exact {
    good := post.good, image := post.image, minstret := post.minstret, tick := post.tick
    pc := post.pc
    raReg := (gholds_lookup (n := 1) _ post.regs (by rfl)).trans (congrArg some raSlot)
    stack := (gholds_lookup (n := 2) _ post.regs (by rfl)).trans
      (congrArg some (BitVec.sub_add_cancel sp 16#64))
    result := gholds_lookup (n := 10) _ post.regs (by rfl)
    s0Reg := (gholds_lookup (n := 8) _ post.regs (by rfl)).trans (congrArg some (by
      show bytesVal .ld (read8 a.σ.mem (sp - 16#64).toNat) = s0
      rw [read8_value, s0']; exact savedS0))
    kept := fun n lo hi hn => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      exact post.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)
    gprs := GprsKept.of_pins post (by decide) (by decide) (by simp [keysG, OpenOut.done_regs])
    memory := post.memory }

/-! ### The whole primitive -/

/-- `caml_ml_open_descriptor_out(v)` returned the custom block `value` holding
the new output channel `record`, linked at the head of
`caml_all_opened_channels`. -/
structure OpenedOut (live : Nat → Prop) (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra s0 s1 s2 v head : BitVec 64)
    (c d : Config) where
  entered : Config
  opened : Config
  flagged : Config
  allocated : Config
  value : BitVec 64
  enter : OutEntered live H capacity charge sp ra s0 s1 s2 v head c entered
  opening : OpenedIn live H capacity (sp - 16#64) OpenOut.pro_call.link s0 s1 s2 (fdOf v) head entered opened
  flags : OutFlagged (sp - 16#64) opening.record opened flagged
  custom : CustomMemReturned sp opening.record value flagged allocated
  done : OutDone sp ra s0 opening.record value allocated d
  record : OutRecord d.σ.mem opening.record (fdOf v) head
  linked : OCaml.Vm.Gc.OpenChannelsLinked c.σ.mem d.σ.mem opening.record.toNat
  /-- `Channel(res) = chan` -/
  channel : bytesT d.σ.mem (value.toNat + 8) 8 = opening.record
  ops : bytesT d.σ.mem value.toNat 8 = 2147891728#64

theorem ml_open_descriptor_out [LibraryLive live] (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 s2 v head : BitVec 64) {Ready : Config → Prop} (custom : CustomMemCall Ready)
    (ready : Ready c) (h : OutInput live H capacity charge sp ra s0 s1 s2 v head c) :
    FnSummary 0x80015f50#64 (fun d => d = c)
      (fun d => Nonempty (OpenedOut live H capacity charge sp ra s0 s1 s2 v head c d)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have lower := h.frame.lower
  have hSE : heapStart ≤ heapEnd := by decide
  have hS : heapStart = 0x8007d140 := rfl
  obtain ⟨entered, run1, E⟩ := (out_enter c h).run c ⟨pc, rfl⟩
  obtain ⟨opened, run2, ⟨O⟩⟩ := (open_descriptor_in entered H capacity charge (sp - 16#64) _ s0 s1 s2
    (fdOf v) head E.input).run entered ⟨E.pc, rfl⟩
  obtain ⟨rec, headW⟩ := OpenedIn.record_words E.input O
  have pLow := O.low
  have pHigh : O.record.toNat + 65616 ≤ heapEnd := O.high
  have sp16 : (sp - 16#64).toNat = sp.toNat - 16 := by
    have e := outFrame_slot (h.frame.resize (small := 16) (by decide) (by decide)) (off := 0) (by decide)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at e; rw [e]; omega
  have leaf : LeafInput OpenOut.pro_call.link opened :=
    ⟨O.link.good, O.link.image, O.link.minstret, O.link.raReg, by decide, O.link.tick⟩
  obtain ⟨flagged, run3, F⟩ := (out_flags opened leaf O.link.stack O.link.result O.low O.high O.align
    rec.zero).run opened ⟨O.link.pc, rfl⟩
  have flagsIn : LogInW [⟨O.record.toNat, O.record.toNat + 72⟩] (outFlagsLog O.record) :=
    OCaml.Vm.Primitives.Channel.LogWithin.inW outFlagsLog_within
  have flagsOut (a : Nat) (out : a < O.record.toNat ∨ O.record.toNat + 72 ≤ a) :
      (flagged.σ.mem[a]?).getD 0 = (opened.σ.mem[a]?).getD 0 := by
    rw [F.memory, frameOn_writeLog _ _ _ flagsIn a ⟨out, trivial⟩]
  have saveIn := outSaveLog_inside (ra := ra) (s0 := s0) (h.frame.resize (small := 16) (by decide) (by decide))
  -- runtime globals and the bytes outside the opening's stores, at the custom call
  have staticE : StaticKept c entered :=
    StaticKept.of_log saveIn (fun a ⟨below, _, _⟩ => ⟨Or.inl (by show a < sp.toNat - 16; arena_omega), trivial⟩)
      entered E.memory
  have staticF : StaticKept opened flagged := fun a ⟨below, _, _⟩ => flagsOut a (Or.inl (by arena_omega))
  have openOut (a : Nat) (o : OutW (openWindows (sp - 16#64) O.record head) a) :
      a < O.record.toNat ∨ O.record.toNat + 72 ≤ a := by
    have base := ((outW_append _ _ a).mp o).1
    simp only [OutW, and_true] at base
    obtain ⟨_, _, _, o4, _⟩ := base
    unfold recordBytes at o4
    omega
  have input : CustomMemInput H capacity sp O.record head c flagged := {
    leaf := ⟨F.good, F.image, F.minstret, F.link, by decide, F.tick⟩
    pc := F.pc
    regs := F.regs
    frame := E.input.frame
    heap := OCaml.Vm.Gc.HeapReady.keep_windows O.heap (ws := [⟨O.record.toNat, O.record.toNat + 72⟩])
      (fun w hw => by
        simp only [List.mem_singleton] at hw
        subst hw
        exact Or.inl ⟨_, List.mem_cons_self, Nat.le_refl _, by dsimp only; unfold recordBytes; omega⟩)
      (fun a out => flagsOut a (out _ List.mem_cons_self))
    low := O.low
    high := O.high
    static := staticE.trans (O.static.trans staticF)
    kept := fun a o notFoot frame => by
      rw [flagsOut a (openOut a o), O.frame a o notFoot, E.memory,
        frameOn_writeLog _ _ _ saveIn a ⟨frame, trivial⟩] }
  obtain ⟨allocated, run4, ⟨value, C⟩⟩ := (custom H capacity sp O.record head c flagged ready input).run
    flagged ⟨F.pc, rfl⟩
  -- the primitive's saves survive the opening, the flags and the custom block
  have slotKept (x : Nat) (lo : sp.toNat - 16 ≤ x) (hi : x + 8 ≤ sp.toNat) :
      bytesT allocated.σ.mem x 8 = bytesT entered.σ.mem x 8 := by
    apply bytesT_keep
    intro j hj
    have aboveHeap : heapEnd ≤ x + j := by arena_omega
    have notFoot : ¬ vsaFoot H (x + j) := by
      rintro (g | ⟨_, l, _⟩)
      · rcases allocGlobal_off_arena _ g with y | y
        · unfold heapStart heapEnd at *; omega
        · unfold allocGlobal InRange at g; unfold heapEnd at aboveHeap; omega
      · omega
    have o : OutW (openWindows (sp - 16#64) O.record head) (x + j) := by
      apply OCaml.Vm.Gc.outW_all
      intro w hw
      unfold openWindows at hw
      rcases List.mem_append.mp hw with hw | hw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · right; dsimp only; rw [sp16]; omega
        all_goals (right; dsimp only; try unfold recordBytes
                   arena_omega)
      · by_cases hz : head = 0#64
        · simp [hz] at hw
        · simp only [hz, ite_false, List.mem_singleton] at hw
          subst hw
          obtain ⟨⟨e, he, _, hi'⟩, _⟩ := h.headLive hz
          have bounds := h.ready.heap.block_bounds (q := e.1) (n := e.2) he
          right; dsimp only; arena_omega
    rw [C.callerFrame _ (by omega) (by omega), flagsOut _ (Or.inr (by arena_omega)),
      O.frame _ o notFoot]
  have s8 : (sp - 16#64 + 8#64).toNat = sp.toNat - 8 := by
    have e := outFrame_slot (h.frame.resize (small := 16) (by decide) (by decide)) (off := 8) (by decide)
    rw [e]; omega
  have savedRa : bytesT allocated.σ.mem (sp.toNat - 8) 8 = ra := by
    rw [slotKept _ (by omega) (by omega), E.memory, ← s8]
    exact OCaml.Vm.Gc.word_writeLog_at _ (outSaveLog sp ra s0) 0 _ _ rfl (by
      simp only [outSaveLog, List.drop, OutLRange, and_true, s8, sp16]; omega)
  have savedS0 : bytesT allocated.σ.mem (sp.toNat - 16) 8 = s0 := by
    rw [slotKept _ (by omega) (by omega), E.memory, ← sp16]
    exact OCaml.Vm.Gc.word_writeLog_at _ (outSaveLog sp ra s0) 1 _ _ rfl trivial
  obtain ⟨d, run5, D⟩ := (out_done allocated C h.frame savedRa savedS0 h.ready.aligned).run
    allocated ⟨C.pc, rfl⟩
  -- the record, the list head and the block at the return
  obtain ⟨vLow, vHigh, _⟩ := C.block
  have v8 : (value + 8#64).toNat = value.toNat + 8 := record_toNat (off := 8) (by omega)
  have doneOut (a : Nat) (out : a < value.toNat + 8 ∨ value.toNat + 16 ≤ a) :
      (d.σ.mem[a]?).getD 0 = (allocated.σ.mem[a]?).getD 0 := by
    have inside : LogInW [⟨value.toNat + 8, value.toNat + 16⟩] [((value + 8#64).toNat, 8, O.record)] :=
      ⟨Or.inl ⟨by dsimp only; rw [v8]; exact Nat.le_refl _, by dsimp only; rw [v8]; omega⟩, trivial⟩
    rw [D.memory, frameOn_writeLog _ _ _ inside a ⟨out, trivial⟩]
  have apart := C.apart
  have recordD : OutRecord d.σ.mem O.record (fdOf v) head := by
    have r := rec.flags
    rw [← F.memory] at r
    exact (r.keep fun a lo hi => C.recordKept a lo (by unfold recordBytes; omega)).keep
      fun a lo hi => doneOut a (by unfold recordBytes at apart; omega)
  have headC : bytesT c.σ.mem 2147896128 8 = head := by
    have e := h.headWord
    rwa [read8_value] at e
  have headD : bytesT d.σ.mem 2147896128 8 = O.record := by
    rw [← headW]
    apply bytesT_keep
    intro j hj
    rw [doneOut _ (Or.inl (by arena_omega)), C.headKept _ (by omega) (by omega),
      flagsOut _ (Or.inl (by arena_omega))]
  refine ⟨d, run1.trans (run2.trans (run3.trans (run4.trans run5))), ⟨{
    entered := entered, opened := opened, flagged := flagged, allocated := allocated, value := value
    enter := E, opening := O, flags := F, custom := C, done := D
    record := recordD
    linked := {
      head := by rw [Layout.sym_caml_all_opened_channels, headD]; simp
      next := by rw [Layout.sym_caml_all_opened_channels, headC]; exact recordD.next
      nonzero := by arena_omega }
    channel := by
      rw [D.memory, ← v8]
      exact OCaml.Vm.Gc.word_writeLog_at _ [((value + 8#64).toNat, 8, O.record)] 0 _ _ rfl trivial
    ops := by
      rw [D.memory, bytesT_writeLog_out _ (by simp only [OutLRange, and_true, v8]; omega)]
      exact C.ops }⟩⟩

/-- `caml_ml_open_descriptor_out` keeps x20–x27 (among them `caml_interprete`'s
`env`, accumulator and dispatch registers). -/
theorem OpenedOut.keep_upper {H : List (Nat × Nat)} {capacity charge : Nat}
    {sp ra s0 s1 s2 v head : BitVec 64} {c d : Config}
    (o : OpenedOut live H capacity charge sp ra s0 s1 s2 v head c d) {k : Nat} {x : BitVec 64}
    (lo : 20 ≤ k) (hi : k ≤ 27) (h : gprGet c.σ k = some x) : gprGet d.σ k = some x := by
  have a := (o.enter.kept k (by omega) (by omega) (by simp; omega)).trans h
  have b := o.opening.keep_upper lo hi a
  have e := (o.flags.kept k (by omega) (by omega) (by simp; omega)).trans b
  have f := (o.custom.saved k (by simp; omega)).trans e
  exact (o.done.kept k (by omega) (by omega) (by simp; omega)).trans f

end OCaml.Vm.Primitives.Channel
