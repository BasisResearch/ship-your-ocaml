import OCaml.Vm.Primitives.Channel.OpenDescriptorCall
import OCaml.Vm.Primitives.Channel.OpenOut
import OCaml.Vm.Primitives.Channel.OpenIn
import OCaml.Vm.Gc.OpenChannels
import OCaml.Vm.Gc.F1Heap
import OCaml.Vm.Gc.CustomMem

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

/-- `Int_val` of the tagged console descriptors. -/
theorem fdOf_stdout : fdOf 3#64 = 1#64 := by decide
theorem fdOf_stderr : fdOf 5#64 = 2#64 := by decide

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
structure OutEntered (link : BitVec 64) (live : Nat → Prop) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 s2 v head : BitVec 64) (c d : Config) : Prop where
  input : OpenInput live H capacity charge (sp - 16#64) link s0 s1 s2 (fdOf v) head d
  pc : pcOf d = some 0x80015130#64
  memory : d.σ.mem = writeLog c.σ.mem (outSaveLog sp ra s0)
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 10] → gprGet d.σ n = gprGet c.σ n
  gprs : GprsKept c d
  output : d.σ.sailOutput = c.σ.sailOutput

/-- `caml_open_descriptor_in` keeps x20–x27: the checked allocation keeps
them (`StatCheckedReturned.keep_upper`), and no other phase writes them. -/
theorem OpenedIn.keep_upper {H : List (Nat × Nat)} {capacity : Nat} {sp ra s0 s1 s2 fd head : BitVec 64}
    {c d : Config} (o : OpenedIn live H capacity sp ra s0 s1 s2 fd head c d) {k : Nat} {x : BitVec 64}
    (lo : 19 ≤ k) (hi : k ≤ 27) (h : gprGet c.σ k = some x) : gprGet d.σ k = some x := by
  have a := (o.allocation.setup.toEffectPost.gpr_frame (by decide) k (by omega) (by omega)
    (by simp; omega)).trans h
  have b := (o.allocation.call.toEffectPost.gpr_frame (by decide) k (by omega) (by omega)
    (by simp; omega)).trans a
  have e : gprGet o.allocated.σ k = some x := by
    rcases Nat.eq_or_lt_of_le lo with rfl | gt
    · exact o.allocation.allocation.keep_saved (by simp) b
    · exact o.allocation.allocation.keep_upper gt hi b
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
  max : bytesT m (p.toNat + 32) 8 = p + 72#64
  next : bytesT m (p.toNat + 48) 8 = head
  zero : bytesT m (p.toNat + 64) 8 = 0#64

/-- The record `caml_ml_open_descriptor_{out,in}` returns (`runtime/caml/io.h`):
an output channel (`max = NULL`) or an input one (`max = buff`, nothing read
ahead), with one reference, managed by the collector
(`CHANNEL_FLAG_MANAGED_BY_GC`), its buffer empty. -/
structure OpenRecord (out : Bool) (m : Std.ExtHashMap Nat (BitVec 8)) (p fd head : BitVec 64) : Prop where
  fd : bytesT m p.toNat 4 = fd.setWidth 32
  offset : bytesT m (p.toNat + 8) 8 = -1#64
  bufEnd : bytesT m (p.toNat + 16) 8 = p + (65536#64 + 72#64)
  curr : bytesT m (p.toNat + 24) 8 = p + 72#64
  max : bytesT m (p.toNat + 32) 8 = if out then 0#64 else p + 72#64
  next : bytesT m (p.toNat + 48) 8 = head
  refcount : bytesT m (p.toNat + 64) 4 = 1#32
  flags : bytesT m (p.toNat + 68) 4 = 4#32

/-- The record's words read the same when its first 72 bytes do. -/
theorem OpenRecord.keep {out : Bool} {m m' : Std.ExtHashMap Nat (BitVec 8)} {p fd head : BitVec 64}
    (h : OpenRecord out m p fd head)
    (same : ∀ a, p.toNat ≤ a → a < p.toNat + 72 → (m'[a]?).getD 0 = (m[a]?).getD 0) :
    OpenRecord out m' p fd head := by
  have k (off n : Nat) (bound : off + n ≤ 72) : bytesT m' (p.toNat + off) n = bytesT m (p.toNat + off) n :=
    bytesT_keep fun j hj => same _ (by omega) (by omega)
  have k0 : bytesT m' p.toNat 4 = bytesT m p.toNat 4 := k 0 4 (by decide)
  exact ⟨k0 ▸ h.fd, (k 8 8 (by decide)) ▸ h.offset, (k 16 8 (by decide)) ▸ h.bufEnd,
    (k 24 8 (by decide)) ▸ h.curr, (k 32 8 (by decide)) ▸ h.max, (k 48 8 (by decide)) ▸ h.next,
    (k 64 4 (by decide)) ▸ h.refcount, (k 68 4 (by decide)) ▸ h.flags⟩

/-- **The returned record represents BcSem's new channel** (`openChan` on a
stream: `offset = -1`, empty buffer, nothing read ahead). -/
theorem OpenRecord.chanAt {out : Bool} {c : Config} {p fd head : BitVec 64} {cfd : Int}
    (h : OpenRecord out c.σ.mem p fd head) (fdInt : (fd.setWidth 32).toInt = cfd) (open_ : cfd ≠ -1)
    (high : p.toNat + recordBytes ≤ heapEnd) (align : p.toNat % 16 = 0) :
    OCaml.Vm.ChanAt c p.toNat ⟨cfd, out, [], [], 0, -1⟩ := by
  have t (k : Nat) (b : k ≤ 65608) := recordAt (p := p) high b
  have e72 : (p + 72#64).toNat = p.toNat + 72 := t 72 (by decide)
  have eEnd : (p + (65536#64 + 72#64)).toNat = p.toNat + 65608 := by
    rw [show (65536#64 + 72#64 : BitVec 64) = BitVec.ofNat 64 65608 from rfl]; exact t 65608 (by decide)
  simp only [OCaml.Vm.ChanAt, OCaml.Vm.word, OCaml.Vm.word32, OCaml.Vm.chanOffFd, OCaml.Vm.chanOffOffset,
    OCaml.Vm.chanOffCurr, OCaml.Vm.chanOffMax, OCaml.Vm.chanOffEnd, OCaml.Vm.chanOffFlags,
    OCaml.Vm.chanOffBuff, OCaml.Vm.chanFlagUnbuffered, OCaml.Vm.chanFlagManaged, Chan.cursor, Chan.buffer, open_, ite_false,
    ite_true, Nat.add_zero, List.length_nil, h.fd, h.offset, h.curr, h.max, h.bufEnd, h.flags, e72, eEnd]
  cases out
  · simp only [Bool.false_eq_true, ite_false, e72, Chan.cursor, Chan.buffer, open_, List.length_nil]
    exact ⟨fdInt, by simp, by simp, by simp, by unfold ioBufferSize; omega, by decide, by simp,
      ⟨Nat.zero_le _, Nat.zero_le _, by omega⟩, by decide⟩
  · exact ⟨fdInt, by simp, by simp, by simp, by unfold ioBufferSize; omega, by decide, by simp,
      ⟨Nat.zero_le _, Nat.zero_le _, by omega⟩, by decide⟩

/-- `caml_ml_open_descriptor_{out,in}`'s record stores: `max := NULL` (output
only), the GC flag and the reference. -/
def chanFlagsLog (out : Bool) (p : BitVec 64) : List WEntry :=
  (if out then [(p.toNat + 32, 8, 0#64)] else []) ++ [(p.toNat + 68, 4, 4#64), (p.toNat + 64, 4, 1#64)]

/-- The output primitive's three stores. -/
abbrev outFlagsLog (p : BitVec 64) : List WEntry := chanFlagsLog true p

theorem chanFlagsLog_within {out : Bool} {p : BitVec 64} :
    LogWithin (chanFlagsLog out p) p.toNat (p.toNat + 72) := by
  intro e he
  cases out <;> simp only [chanFlagsLog, ite_true, Bool.false_eq_true, ite_false, List.nil_append,
    List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at he
  · rcases he with rfl | rfl <;> (dsimp only; omega)
  · rcases he with rfl | rfl | rfl <;> (dsimp only; omega)

theorem outFlagsLog_within {p : BitVec 64} :
    LogWithin (outFlagsLog p) p.toNat (p.toNat + 72) := chanFlagsLog_within

theorem OpenedRecord.flags_in {m : Std.ExtHashMap Nat (BitVec 8)} {p fd head : BitVec 64}
    (h : OpenedRecord m p fd head) : OpenRecord false (writeLog m (chanFlagsLog false p)) p fd head := by
  have out (x n : Nat) (sep : x + n ≤ p.toNat + 64) :
      bytesT (writeLog m (chanFlagsLog false p)) x n = bytesT m x n := by
    apply bytesT_writeLog_out
    simp only [chanFlagsLog, Bool.false_eq_true, ite_false, List.nil_append, OutLRange, and_true]
    omega
  have split : chanFlagsLog false p = [(p.toNat + 68, 4, 4#64)] ++ [(p.toNat + 64, 4, 1#64)] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [out _ _ (by omega)]; exact h.fd
  · rw [out _ _ (by omega)]; exact h.offset
  · rw [out _ _ (by omega)]; exact h.bufEnd
  · rw [out _ _ (by omega)]; exact h.curr
  · rw [out _ _ (by omega)]; exact h.max
  · rw [out _ _ (by omega)]; exact h.next
  · rw [split, writeLog_append, word32_writeLog]; rfl
  · rw [split, writeLog_append, bytesT_writeLog_out _ (by simp only [OutLRange, and_true]; omega),
      show ([(p.toNat + 68, 4, 4#64)] : List WEntry) = [] ++ [(p.toNat + 68, 4, 4#64)] from rfl,
      writeLog_append, word32_writeLog]; rfl

theorem OpenedRecord.flags {m : Std.ExtHashMap Nat (BitVec 8)} {p fd head : BitVec 64}
    (h : OpenedRecord m p fd head) : OpenRecord true (writeLog m (outFlagsLog p)) p fd head := by
  have out (x n : Nat) (sep : x + n ≤ p.toNat + 32 ∨ (p.toNat + 40 ≤ x ∧ x + n ≤ p.toNat + 64)) :
      bytesT (writeLog m (outFlagsLog p)) x n = bytesT m x n := by
    apply bytesT_writeLog_out
    simp only [outFlagsLog, chanFlagsLog, ite_true, List.singleton_append, List.cons_append, List.nil_append, OutLRange, and_true]
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
      (by simp only [outFlagsLog, chanFlagsLog, ite_true, List.singleton_append, List.cons_append, List.nil_append, List.drop, OutLRange, and_true]; omega)
  · rw [out _ _ (Or.inr ⟨by omega, by omega⟩)]; exact h.next
  · rw [split, writeLog_append, word32_writeLog]; rfl
  · rw [split, writeLog_append, bytesT_writeLog_out _ (by simp only [OutLRange, and_true]; omega),
      split', writeLog_append, word32_writeLog]; rfl

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
    rcases Gc.fresh_apart_covered o.fresh (x := (head.toNat + 56, 8)) ⟨e, he, by dsimp only; omega,
      by dsimp only; omega⟩ (by dsimp only; omega) (n := recordBytes) (by unfold recordBytes; decide) (Nat.le_refl _)
      with l | l
    · left; dsimp only at l; unfold recordBytes at l; omega
    · right; dsimp only at l; omega
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
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
  · exact word 4 32 _ (by decide) rfl (by
      simp only [recordInitLog, List.drop, OutLRange, endAddress, and_true]
      rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, t 24 (by decide),
        show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, t 48 (by decide), t 65608 (by decide)]
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

/-- The call of `caml_alloc_custom_mem` inside the primitive's 16-byte frame,
returning to `0x80015fa0` with the record in `s0`. -/
def outSite (ret sp p : BitVec 64) : Gc.CustomMemSite := ⟨ret, sp, p, 16⟩

/-- The registers handed to `caml_alloc_custom_mem(&channel_operations,
sizeof(struct channel *), sizeof(struct channel))`. -/
def customArgs (sp p : BitVec 64) : GRegs := (outSite 0 sp p).args

/-- At the call of `caml_alloc_custom_mem`: the record's three stores done. -/
structure OutFlagged (ret : BitVec 64) (out : Bool) (sp p : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  pc : pcOf d = some 0x800247f8#64
  link : gprGet d.σ 1 = some ret
  regs : GHolds d.σ (customArgs sp p)
  memory : d.σ.mem = writeLog c.σ.mem (chanFlagsLog out p)
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 8, 10, 11, 12, 14, 15] → gprGet d.σ n = gprGet c.σ n
  gprs : GprsKept c d
  output : d.σ.sailOutput = c.σ.sailOutput

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
  output : d.σ.sailOutput = c.σ.sailOutput
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)

end OCaml.Vm.Primitives.Channel
