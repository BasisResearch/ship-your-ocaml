import OCaml.Vm.Primitives.Channel.OpenDescriptor
import OCaml.Vm.Primitives.Channel.LseekCall
import OCaml.Vm.Primitives.Console.Blocking
import OCaml.Vm.Boot.Startup.StatCheckedFrame
import OCaml.Vm.Boot.Startup.MainArgv
import OCaml.Vm.Gc.LibHeap
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Reloc
import OCaml.Vm.Sim.ConsoleCall
import OCaml.Vm.Primitives.Word32Access
import Vsa.Sim.FrameComposition

/-! `caml_open_descriptor_in(fd)` as a call summary: allocate the record with
the checked `caml_stat_alloc` (the landed malloc contract), store the
descriptor, seek (`lseek_call`: -1 on a console stream) inside a blocking
section, initialize the record and link it at the head of
`caml_all_opened_channels`. -/
namespace OCaml.Vm.Primitives.Channel
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap LeanRV64DExecutable
open OCaml.Vm.Boot.Startup
open ExitPath (LogWithin LogWithin.outLRange)
open FdWrite (errnoGlobal impurePtr enterHook leaveHook pendingSignals)
open ConsoleWrite (fsReady kindAddress enter_blocking leave_blocking LeaveInput LeavePost QuietReturn)
open OCaml.Vm.Sim (FrameOnD)
open OpenDescriptor
variable {live : Nat → Prop}

/-- `struct channel`'s size, `sizeof(struct channel)`: the header words and
the `IO_BUFFER_SIZE` buffer, then the name pointer. -/
def recordBytes : Nat := 65616

/-- The entry registers `caml_open_descriptor_in` reads: `ra`, `sp`, the
saved `s0`–`s2` and the descriptor in `a0`. -/
def openR (sp ra s0 s1 s2 fd : BitVec 64) : Nat → BitVec 64 := fun n =>
  if n = 1 then ra else if n = 2 then sp else if n = 8 then s0 else if n = 9 then s1
  else if n = 18 then s2 else fd

/-- The prologue's four saves into its 32-byte frame. -/
def openSaveLog (sp ra s0 s1 s2 : BitVec 64) : List WEntry :=
  [((sp - 32#64).toNat, 8, s2), ((sp - 32#64 + 24#64).toNat, 8, ra),
   ((sp - 32#64 + 16#64).toNat, 8, s0), ((sp - 32#64 + 8#64).toNat, 8, s1)]

/-- The registers handed to `caml_stat_alloc`. -/
def openCallArgs (sp s0 s1 fd : BitVec 64) : GRegs :=
  [(10, 65616#64), (18, fd), (2, sp - 32#64), (8, s0), (9, s1)]

theorem openStack (sp : BitVec 64) : sp - 32#64 = nativeStack sp 32 := by
  rw [nativeStack, BitVec.sub_eq_add_neg]

theorem openFrame_slot {sp} (frame : NativeFrame sp 32) {off : Nat} (bound : off ≤ 32) :
    (sp - 32#64 + BitVec.ofNat 64 off).toNat = nativeFrameBase sp 32 + off := by
  rw [BitVec.sub_eq_add_neg, frame.address _ bound, frame.slot_nat bound]

theorem openFrame_base {sp} (frame : NativeFrame sp 32) :
    (sp - 32#64).toNat = nativeFrameBase sp 32 := by
  rw [openStack, frame.stack_nat]

theorem openFrame_word {sp} (frame : NativeFrame sp 32) {off : Nat} (bound : off + 8 ≤ 32)
    (aligned : off % 8 = 0) : WriteWindow (sp - 32#64 + BitVec.ofNat 64 off) 8 := by
  rw [BitVec.sub_eq_add_neg, frame.address _ (by omega)]
  exact frame.word bound aligned

theorem openSaveLog_inside {sp ra s0 s1 s2} (frame : NativeFrame sp 32) :
    LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (openSaveLog sp ra s0 s1 s2) := by
  have low := frame.lower
  have e0 := openFrame_base frame
  have e8 := openFrame_slot frame (off := 8) (by decide)
  have e16 := openFrame_slot frame (off := 16) (by decide)
  have e24 := openFrame_slot frame (off := 24) (by decide)
  simp only [openSaveLog, LogInW, InsideW, e0]
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, e8,
    show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, e16,
    show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, e24]
  refine ⟨Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, trivial⟩
  all_goals unfold nativeFrameBase at *; omega

/-- The prologue and the checked allocation of the channel record. -/
structure OpenAllocated (live : Nat → Prop) (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 fd : BitVec 64)
    (before after : Config) where
  saved : Config
  called : Config
  setup : WriteRegistersPost [2, 10, 18] (openSaveLog sp ra s0 s1 s2) before pro_call.pc
    65616#64 (pro_regs (openR sp ra s0 s1 s2 fd) []) saved
  call : RegistersPost [1] saved.σ.mem saved pro_call.target 65616#64
    ((1, pro_call.link) :: openCallArgs sp s0 s1 fd) called
  allocation : StatCheckedReturnedL live H capacity (sp - 32#64) pro_call.link s0 65616#64 called after

/-- From the entry of `caml_open_descriptor_in` to the return of its checked
`caml_stat_alloc(sizeof(struct channel))`. -/
theorem open_allocate [LibraryLive live] (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 s2 fd : BitVec 64) (ready : RuntimeReadyL live H (capacity + charge) sp ra c)
    (frame : NativeFrame sp 576) (saved0 : gprGet c.σ 8 = some s0)
    (saved1 : gprGet c.σ 9 = some s1) (saved2 : gprGet c.σ 18 = some s2)
    (fdReg : gprGet c.σ 10 = some fd) (charged : vsaChg recordBytes charge) :
    FnSummary 0x80015130#64 (fun d => d = c)
      (fun after => Nonempty (OpenAllocated live H capacity sp ra s0 s1 s2 fd c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have short := frame.resize (small := 32) (by decide) (by decide)
  have nested : NativeFrame (sp - 32#64) 544 := by
    rw [openStack]; exact frame.nested (front := 32) (by decide)
  let R := openR sp ra s0 s1 s2 fd
  have inside : LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (openSaveLog sp ra s0 s1 s2) :=
    openSaveLog_inside short
  obtain ⟨saved, run1, setup⟩ := (pro_fast c R ready.toLeafInput
    ⟨ready.raReg, ready.stack, saved0, saved1, fdReg, saved2, trivial⟩
    (by
      show WriteWindow (sp - 32#64) 8
      have w := openFrame_word short (off := 0) (by decide) (by decide)
      rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at w)
    (openFrame_word short (off := 24) (by decide) (by decide))
    (openFrame_word short (off := 16) (by decide) (by decide))
    (openFrame_word short (off := 8) (by decide) (by decide))
    (short.image_outside inside)).run c ⟨pc, rfl⟩
  have savedReady : RuntimeReadyL live H (capacity + charge) (sp - 32#64) ra saved :=
    ready.stack_log setup (by decide) (by simp only [pro_regs, keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ setup.regs (by rfl))
      (gholds_lookup (n := 1) _ setup.regs (by rfl)) ready.aligned short inside
  have args : GHolds saved.σ (openCallArgs sp s0 s1 fd) :=
    holds_project setup.regs (by simp [openCallArgs, pro_regs, R, openR, lookupG])
  obtain ⟨called, run2, call⟩ := (call_registers_summary pro_call_shape pro_call_decode saved
    (pro_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ args
    (by change KeysOK [10, 18, 2, 8, 9]; decide) (by simp only [KeysAvoidRa, keysG, openCallArgs]; decide)
    (by rfl)).run saved ⟨setup.pc, rfl⟩
  have calledReady := savedReady.effect call (by decide)
    (by simp only [keysG, openCallArgs]; decide) (by decide)
    (gholds_lookup (n := 2) _ call.regs (by rfl))
    (gholds_lookup (n := 1) _ call.regs (by rfl)) (by decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  obtain ⟨after, run3, ⟨allocated⟩⟩ := (stat_checkedL called H capacity charge _ pro_call.link s0
    65616#64 calledReady nested (gholds_lookup (n := 8) _ call.regs (by rfl)) call.result
    charged).run called ⟨call.pc, rfl⟩
  exact ⟨after, run1.trans (run2.trans run3), ⟨saved, called, setup, call, allocated⟩⟩

/-! ### Runtime globals across the opening

Below the arena, the opening writes only the allocator's globals (which hold
the two `errno` words) and `caml_all_opened_channels`; every other runtime
global reads the same afterwards. -/

/-- A byte the opening never writes outside the allocator: a static global
other than the allocator's and `caml_all_opened_channels`. -/
abbrev StaticByte (a : Nat) : Prop :=
  a < heapStart ∧ ¬ allocGlobal a ∧
    (a < Layout.sym_caml_all_opened_channels ∨ Layout.sym_caml_all_opened_channels + 8 ≤ a)

/-- Every `StaticByte` reads the same in `d` as in `c`. -/
def StaticKept (c d : Config) : Prop :=
  ∀ a, StaticByte a → (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0

theorem StaticKept.trans {c d e : Config} (first : StaticKept c d) (second : StaticKept d e) :
    StaticKept c e := fun a h => (second a h).trans (first a h)

theorem StaticKept.of_memory {c d : Config} (same : d.σ.mem = c.σ.mem) : StaticKept c d :=
  fun _ _ => by rw [same]

theorem StaticKept.of_frame {c d : Config} {ws : List W} (frame : FrameOnD ws c.σ.mem d.σ.mem)
    (out : ∀ a, StaticByte a → OutW ws a) : StaticKept c d :=
  fun a h => frame a (out a h)

theorem StaticKept.of_log {c : Config} {ws : List W} {log : List WEntry} (inside : LogInW ws log)
    (out : ∀ a, StaticByte a → OutW ws a) (d : Config) (memory : d.σ.mem = writeLog c.σ.mem log) :
    StaticKept c d :=
  fun a h => by rw [memory, frameOn_writeLog _ _ _ inside a (out a h)]

/-- `omega` with the arena bounds as atoms (`omega` exhausts the recursion
depth on some goals that mention them unfolded). -/
macro "arena_omega" : tactic =>
  `(tactic| (try simp only [Nat.sub_sub] at *
             generalize heapEnd = E at *
             generalize heapStart = S at *
             omega))

local macro "static_byte" : tactic =>
  `(tactic| (intro i hi; refine ⟨?_, ?_, ?_⟩ <;>
    simp only [heapStart, allocGlobal, InRange, Layout.sym_caml_all_opened_channels] <;> omega))

theorem StaticKept.read8 {c d : Config} (k : StaticKept c d) {a : Nat}
    (static : ∀ i, i < 8 → StaticByte (a + i)) : read8 d.σ.mem a = read8 c.σ.mem a := by
  have e (i : Nat) (hi : i < 8) := k (a + i) (static i hi)
  simp only [OCaml.Vm.Primitives.read8, List.cons.injEq, and_true]
  exact ⟨by simpa using e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide),
    e 4 (by decide), e 5 (by decide), e 6 (by decide), e 7 (by decide)⟩

theorem SeekFd.keep {fd : BitVec 64} {c d : Config} (h : SeekFd fd c) (k : StaticKept c d) :
    SeekFd fd d := by
  have slot := slotAddress_toNat h.range
  have range := h.range
  have ready : read8 d.σ.mem fsReady.toNat = read8 c.σ.mem fsReady.toNat :=
    k.read8 (by rw [show fsReady.toNat = 0x80064918 from rfl]; static_byte)
  have kind : read8 d.σ.mem (slotAddress fd).toNat = read8 c.σ.mem (slotAddress fd).toNat :=
    k.read8 (by rw [slot]; static_byte)
  exact ⟨by rw [ready]; exact h.ready, range, h.slotWindow, by rw [kind]; exact h.live,
    by rw [kind]; exact h.notFile⟩

theorem _root_.OCaml.Vm.Primitives.ConsoleWrite.ConsoleFd.keep {fd : BitVec 64} {c d : Config} (h : ConsoleWrite.ConsoleFd fd c)
    (k : StaticKept c d) : ConsoleWrite.ConsoleFd fd d := by
  have range := h.range
  have slot : (kindAddress fd).toNat = 2147896728 + 24 * fd.toNat := by
    unfold kindAddress
    rw [BitVec.toNat_add, BitVec.add_def]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    omega
  have ready : read8 d.σ.mem fsReady.toNat = read8 c.σ.mem fsReady.toNat :=
    k.read8 (by rw [show fsReady.toNat = 0x80064918 from rfl]; static_byte)
  have word : read8 d.σ.mem (kindAddress fd).toNat = read8 c.σ.mem (kindAddress fd).toNat :=
    k.read8 (by rw [slot]; static_byte)
  exact ⟨by rw [ready]; exact h.ready, range, h.kindWindow, by rw [word]; exact h.console,
    by rw [word]; exact h.notFile⟩

/-- A console descriptor is seekable in `_lseek`'s sense: the same descriptor
table slot, live and not a file. -/
theorem _root_.OCaml.Vm.Primitives.ConsoleWrite.ConsoleFd.seekFd {fd : BitVec 64} {c : Config}
    (h : ConsoleWrite.ConsoleFd fd c) : SeekFd fd c := by
  have range := h.range
  have same : slotAddress fd = kindAddress fd := by
    apply BitVec.eq_of_toNat_eq
    rw [slotAddress_toNat range]
    unfold kindAddress
    rw [BitVec.toNat_add, BitVec.add_def]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    omega
  refine ⟨h.ready, range, same ▸ h.kindWindow, ?_, by rw [same]; exact h.notFile⟩
  rw [same]
  intro zero
  have console := h.console
  rw [zero] at console
  exact absurd console (by decide)

theorem _root_.OCaml.Vm.Primitives.ConsoleWrite.ConsoleRuntime.keep {c d : Config} (h : ConsoleWrite.ConsoleRuntime c) (k : StaticKept c d) :
    ConsoleWrite.ConsoleRuntime d where
  stdout := h.stdout.keep k
  stderr := h.stderr.keep k
  enterHookWord := by
    rw [k.read8 (by rw [show enterHook.toNat = 0x80064870 from rfl]; static_byte)]
    exact h.enterHookWord
  leaveHookWord := by
    rw [k.read8 (by rw [show leaveHook.toNat = 0x80064868 from rfl]; static_byte)]
    exact h.leaveHookWord
  impure := by
    rw [k.read8 (by rw [show impurePtr.toNat = 0x800648f8 from rfl]; static_byte)]
    exact h.impure
  clear := by
    intro i hi
    have e := h.clear i hi
    rw [ConsoleWrite.slot_toNat i hi] at e ⊢
    rw [k.read8 (by rw [show pendingSignals.toNat = 0x80068690 from rfl]; static_byte)]
    exact e
  quiet := by
    rw [k.read8 (by rw [show ConsoleWrite.somethingToDo.toNat = 0x80064b30 from rfl]; static_byte)]
    exact h.quiet
  lockNull := by
    rw [k.read8 (by rw [show ConsoleWrite.channelLock.toNat = 0x80064b58 from rfl]; static_byte)]
    exact h.lockNull
  unlockNull := by
    rw [k.read8 (by rw [show ConsoleWrite.channelUnlock.toNat = 0x80064b50 from rfl]; static_byte)]
    exact h.unlockNull

/-! ### Descriptor, blocking section, seek -/

theorem heapWindow {x : BitVec 64} {n : Nat} (low : heapStart ≤ x.toNat) (high : x.toNat + n ≤ heapEnd)
    (aligned : x.toNat % n = 0) : WriteWindow x n :=
  ⟨by unfold heapStart at low; omega, by unfold heapEnd at high; omega,
    by unfold heapStart Layout.sym_tohost at *; omega, aligned⟩

theorem heap_image_outside {log : List WEntry} (inside : LogInW [⟨heapStart, heapEnd⟩] log) :
    ImageOutside log := by
  have text : Image.textBase + Image.textSize ≤ heapStart := by decide
  have rodata : Image.rodataBase + Image.rodataSize ≤ heapStart := by decide
  constructor
  all_goals apply OCaml.Vm.Sim.outLRange_of_windows inside
  all_goals change (_ ≤ heapStart ∨ heapEnd ≤ _) ∧ True
  all_goals exact ⟨Or.inl (by omega), trivial⟩

theorem record_toNat {p : BitVec 64} {off : Nat} (high : p.toNat + off ≤ heapEnd) :
    (p + BitVec.ofNat 64 off).toNat = p.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  unfold heapEnd at high
  omega

/-- An aligned word of the record. -/
theorem recordWord {p : BitVec 64} {off : Nat} (low : heapStart ≤ p.toNat)
    (high : p.toNat + off + 8 ≤ heapEnd) (align : p.toNat % 16 = 0) (aligned : off % 8 = 0) :
    WriteWindow (p + BitVec.ofNat 64 off) 8 := by
  have e := record_toNat (p := p) (off := off) (by omega)
  exact heapWindow (by rw [e]; omega) (by rw [e]; omega) (by rw [e]; omega)

theorem stack_toNat {sp : BitVec 64} {k : Nat} (frame : NativeFrame sp 576) (bound : k ≤ 576) :
    (sp - BitVec.ofNat 64 k).toNat = sp.toNat - k := by
  have lower := frame.lower
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  unfold heapEnd at lower
  omega

/-- The writes from the record's allocation to the end of the blocking
section: the native stack below the entry sp, newlib's two `errno` words and
the record's `fd` and `offset` words. -/
def seekCallWindows (sp : BitVec 64) : List W :=
  [⟨sp.toNat - 576, sp.toNat - 32⟩, ⟨0x80064668, 0x8006466c⟩, ⟨0x80064d48, 0x80064d4c⟩]

def seekWindows (sp p : BitVec 64) : List W := seekCallWindows sp ++ [⟨p.toNat, p.toNat + 16⟩]

/-- Bytes kept over each piece of the frame are kept over all of it. -/
theorem bytesT_keep {m m' : Std.ExtHashMap Nat (BitVec 8)} {a n : Nat}
    (same : ∀ j, j < n → (m'[a + j]?).getD 0 = (m[a + j]?).getD 0) : bytesT m' a n = bytesT m a n := by
  have one (m : Std.ExtHashMap Nat (BitVec 8)) (x : Nat) : bytesT m x 1 = (m[x]?).getD 0 := by
    simp only [bytesT]
    change (0#0).append ((m[x]?).getD 0) = _
    rw [BitVec.append]
    simp
  exact OCaml.Vm.Reloc.bytesT_congr fun j hj => by rw [one, one]; exact same j hj

theorem seekWindows_static {sp p : BitVec 64} (frame : NativeFrame sp 576) (low : heapStart ≤ p.toNat) :
    ∀ a, StaticByte a → OutW (seekWindows sp p) a := by
  intro a ⟨below, notAlloc, _⟩
  have lower := frame.lower
  simp only [allocGlobal, InRange] at notAlloc
  simp only [seekWindows, seekCallWindows, List.cons_append, List.nil_append, OutW, and_true]
  unfold heapStart heapEnd at *
  omega

/-- At the return from the allocation: the record `p`, the descriptor in
`s2`, the runtime's console state and a seekable (console) descriptor. -/
structure OpenSeekInput (sp p fd : BitVec 64) (c : Config) : Prop extends LeafInput pro_call.link c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  stack : gprGet c.σ 2 = some (sp - 32#64)
  record : gprGet c.σ 10 = some p
  fdReg : gprGet c.σ 18 = some fd
  frame : NativeFrame sp 576
  low : heapStart ≤ p.toNat
  high : p.toNat + recordBytes ≤ heapEnd
  align : p.toNat % 16 = 0
  runtime : ConsoleWrite.ConsoleRuntime c
  descriptor : SeekFd fd c

/-- After `caml_leave_blocking_section`: `fd` and `offset` (-1: the console
streams do not seek) are stored, everything else outside `seekWindows` reads
the same. -/
structure OpenSeekPost (sp p fd : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some 0x80015178#64
  link : gprGet d.σ 1 = some offset_call.link
  stack : gprGet d.σ 2 = some (sp - 32#64)
  record : gprGet d.σ 8 = some p
  a0 : ∃ v, gprGet d.σ 10 = some v
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17] →
    gprGet d.σ n = gprGet c.σ n
  gprs : GprsKept c d
  fdWord : bytesT d.σ.mem p.toNat 4 = fd.setWidth 32
  offsetWord : bytesT d.σ.mem (p.toNat + 8) 8 = -1#64
  frame : FrameOnD (seekWindows sp p) c.σ.mem d.σ.mem

theorem open_seek (c : Config) (sp p fd : BitVec 64) (h : OpenSeekInput sp p fd c) :
    FnSummary 0x80015154#64 (fun d => d = c) (fun d => OpenSeekPost sp p fd c d) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have frame := h.frame
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have lower := frame.lower
  have upper := frame.upper
  have low := h.low
  have high := h.high
  have align := h.align
  unfold recordBytes at high
  have e8p : (p + 8#64).toNat = p.toNat + 8 := record_toNat (by omega)
  have rp : BitVec.ofNat 64 Layout.sym_impure_data = 0x80064668#64 := rfl
  have sp32 : (sp - 32#64).toNat = sp.toNat - 32 := stack_toNat frame (by decide)
  have static := seekWindows_static frame low
  -- `c->fd = fd`, then `caml_enter_blocking_section()`
  let R1 : Nat → BitVec 64 := fun n =>
    if n = 1 then pro_call.link else if n = 2 then sp - 32#64 else if n = 10 then p else fd
  have fdInside : LogInW (seekWindows sp p) [(p.toNat, 4, fd)] := by
    simp only [seekWindows, seekCallWindows, List.cons_append, List.nil_append, LogInW, InsideW,
      and_true, or_false]
    omega
  obtain ⟨s1, run1, st1⟩ := (fd_fast c R1 h.toLeafInput ⟨h.raReg, h.stack, h.record, h.fdReg, trivial⟩
    (show WriteWindow p 4 from heapWindow low (by omega) (by omega))
    (heap_image_outside (log := [(p.toNat, 4, fd)]) (by
      simp only [LogInW, InsideW, and_true, or_false]; omega))).run c ⟨pc, rfl⟩
  have m1 : s1.σ.mem = writeLog c.σ.mem [(p.toNat, 4, fd)] := st1.memory
  have a1 : GHolds s1.σ [(8, p), (2, sp - 32#64), (10, p), (18, fd)] :=
    holds_project st1.regs (by simp [fd_regs, R1, lookupG])
  obtain ⟨s2, run2, call1⟩ := (call_registers_summary fd_call_shape fd_call_decode s1
    (fd_call_pins st1.image) st1.good st1.image st1.tick st1.minstret _ a1
    (by change KeysOK [8, 2, 10, 18]; decide) (by simp only [KeysAvoidRa, keysG]; decide)
    (by rfl)).run s1 ⟨st1.pc, rfl⟩
  have k2 : StaticKept c s2 := StaticKept.of_log fdInside static s2 (by rw [call1.memory, m1])
  have rt2 := h.runtime.keep k2
  obtain ⟨s3, run3, q⟩ := enter_blocking (ra := fd_call.link)
    ⟨call1.good, call1.image, call1.minstret, gholds_lookup (n := 1) _ call1.regs (by rfl), by decide,
      call1.tick⟩
    (call1.toEffectPost.htifIdle (st1.toEffectPost.htifIdle h.idle))
    ⟨p, gholds_lookup (n := 10) _ call1.regs (by rfl)⟩ rt2.enterHookWord
    (by rw [call1.pc, fd_call_target])
  have k3 : StaticKept c s3 := k2.trans (StaticKept.of_memory q.memory)
  have reg3 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ [15]) : gprGet s3.σ n = gprGet s2.σ n :=
    q.kept n lo hi hn
  -- `offset = lseek(fd, 0, SEEK_CUR)`
  let R2 : Nat → BitVec 64 := fun n =>
    if n = 1 then fd_call.link else if n = 2 then sp - 32#64 else if n = 8 then p else fd
  have l3 : gprGet s3.σ 1 = some fd_call.link :=
    (reg3 1 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 1) _ call1.regs (by rfl))
  obtain ⟨s4, run4, st4⟩ := (seek_fast s3 R2 ⟨q.good, q.image, q.minstret, l3,
      show fd_call.link.toNat % 4 = 0 by decide, q.tick⟩
    ⟨l3, (reg3 2 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 2) _ call1.regs (by rfl)),
      (reg3 8 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 8) _ call1.regs (by rfl)),
      (reg3 18 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 18) _ call1.regs (by rfl)),
      trivial⟩).run s3 ⟨q.pc, rfl⟩
  have a4 : GHolds s4.σ [(10, fd), (11, 0#64), (12, 1#64), (2, sp - 32#64), (8, p), (18, fd)] :=
    holds_project st4.regs (by simp [seek_regs, R2, lookupG])
  obtain ⟨s5, run5, call2⟩ := (call_registers_summary seek_call_shape seek_call_decode s4
    (seek_call_pins st4.image) st4.good st4.image st4.tick st4.minstret _ a4
    (by change KeysOK [10, 11, 12, 2, 8, 18]; decide) (by simp only [KeysAvoidRa, keysG]; decide)
    (by rfl)).run s4 ⟨st4.pc, rfl⟩
  have k5 : StaticKept c s5 :=
    k3.trans (StaticKept.of_memory (by rw [call2.memory, st4.memory]; rfl))
  have rt5 := h.runtime.keep k5
  have spSeek (k : Nat) (bound : k ≤ 544) : (sp - 32#64 - BitVec.ofNat 64 k).toNat = sp.toNat - 32 - k := by
    rw [BitVec.toNat_sub, sp32, BitVec.toNat_ofNat]; unfold heapEnd at lower; omega
  have word (x : BitVec 64) (k : Nat) (hx : x.toNat = sp.toNat - k) (bound : 8 ≤ k) (bound' : k ≤ 576)
      (aligned : k % 8 = 0) : WriteWindow x 8 :=
    ⟨by rw [hx]; unfold heapEnd at lower; omega, by rw [hx]; unfold Layout.sym_stack_top at upper; omega,
      by rw [hx]; unfold Layout.sym_tohost heapEnd at *; omega,
      by rw [hx]; have := frame.aligned; omega⟩
  have e16 := spSeek 16 (by decide)
  have e8 : (sp - 32#64 - 16#64 + 8#64).toNat = sp.toNat - 40 := by
    rw [BitVec.toNat_add, e16]; simp only [BitVec.toNat_ofNat]; unfold heapEnd at lower; omega
  have e40 : (sp - 32#64 - 16#64 - 48#64 + 40#64).toNat = sp.toNat - 56 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub, e16]; simp only [BitVec.toNat_ofNat]
    unfold heapEnd at lower; omega
  have errnoW : WriteWindow (0x80064668#64) 4 := ⟨by decide, by decide, by decide, by decide⟩
  have seekIn : SeekInput seek_call.link (sp - 32#64) p fd 0#64 1#64 0x80064668#64 s5 := {
    toLeafInput := ⟨call2.good, call2.image, call2.minstret, gholds_lookup (n := 1) _ call2.regs (by rfl),
      by decide, call2.tick⟩
    idle := call2.toEffectPost.htifIdle (st4.toEffectPost.htifIdle q.idle)
    stack := gholds_lookup (n := 2) _ call2.regs (by rfl)
    s0Reg := gholds_lookup (n := 8) _ call2.regs (by rfl)
    fdReg := gholds_lookup (n := 10) _ call2.regs (by rfl)
    offReg := gholds_lookup (n := 11) _ call2.regs (by rfl)
    whenceReg := gholds_lookup (n := 12) _ call2.regs (by rfl)
    whenceOk := by decide
    descriptor := h.descriptor.keep k5
    deep := by rw [sp32]; unfold heapEnd at lower; omega
    frameLow := word _ 48 (by rw [e16]; omega) (by decide) (by decide) (by decide)
    frameHigh := word _ 40 e8 (by decide) (by decide) (by decide)
    slot := word _ 56 e40 (by decide) (by decide) (by decide)
    text := Or.inl (by rw [sp32]; unfold Image.textBase Image.textSize heapEnd at *; omega)
    rodata := Or.inl (by rw [sp32]; unfold Image.rodataBase Image.rodataSize heapEnd at *; omega)
    apart := by
      have slot := slotAddress_toNat h.descriptor.range
      have range := h.descriptor.range
      intro a member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rw [sp32]
      rcases member with rfl | rfl | rfl | rfl
      all_goals first
        | (rw [slot]; unfold heapEnd at lower; omega)
        | (left; unfold heapEnd at lower; simp only [fsReady, impurePtr, errnoGlobal, Layout.sym_fs_ready,
            BitVec.toNat_ofNat]; omega)
    impure := by rw [rt5.impure, rp]
    errnoWindow := errnoW
    errnoText := Or.inr (by decide)
    errnoRodata := Or.inr (by decide)
    errnoStack := Or.inl (by rw [sp32]; unfold heapEnd at lower; simp only [BitVec.toNat_ofNat]; omega)
    errnoApart := Or.inl (by decide) }
  obtain ⟨s6, run6, post6, s0At6⟩ := lseek_call seekIn (by rw [call2.pc, seek_call_target])
  have seekInside : LogInW (seekCallWindows sp) (seekLog seek_call.link (sp - 32#64) p 0x80064668#64) := by
    simp only [seekLog, htifSeekLog, List.cons_append, List.nil_append, LogInW, InsideW, seekCallWindows]
    rw [e16, e8, show (sp - 32#64 - 16#64 - 48#64 + 40#64) = sp - 32#64 - 16#64 - 48#64 + 40#64 from rfl, e40]
    simp only [errnoGlobal, BitVec.toNat_ofNat]
    unfold heapEnd at lower
    refine ⟨Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)), Or.inl ⟨?_, ?_⟩,
      Or.inr (Or.inl ⟨?_, ?_⟩), trivial⟩ <;> omega
  have callOut (a : Nat) (out : OutW (seekWindows sp p) a) : OutW (seekCallWindows sp) a :=
    ((outW_append _ _ a).mp out).1
  have k6 : StaticKept c s6 :=
    k5.trans (StaticKept.of_log seekInside (fun a h => callOut a (static a h)) s6 post6.memory)
  have rt6 := h.runtime.keep k6
  -- `c->offset = offset`, then `caml_leave_blocking_section()`
  let R3 : Nat → BitVec 64 := fun n =>
    if n = 1 then seek_call.link else if n = 2 then sp - 32#64 else if n = 8 then p else -1#64
  have reg6 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (hn : n ∉ seekWrites) : gprGet s6.σ n = gprGet s5.σ n :=
    post6.kept n lo hi hn
  have offInside : LogInW (seekWindows sp p) [((p + 8#64).toNat, 8, -1#64)] := by
    simp only [seekWindows, seekCallWindows, List.cons_append, List.nil_append, LogInW, InsideW,
      and_true, or_false, e8p]
    omega
  have w8 : WriteWindow (p + 8#64) 8 := recordWord low (by omega) align (by decide)
  obtain ⟨s7, run7, st7⟩ := (offset_fast s6 R3 ⟨post6.good, post6.image, post6.minstret, post6.raReg,
      show seek_call.link.toNat % 4 = 0 by decide, post6.tick⟩
    ⟨post6.raReg, post6.stack, s0At6, post6.result, trivial⟩
    w8
    (heap_image_outside (log := [((p + 8#64).toNat, 8, -1#64)]) (by
      simp only [LogInW, InsideW, and_true, or_false, e8p]; omega))).run s6 ⟨post6.pc, rfl⟩
  have m7 : s7.σ.mem = writeLog s6.σ.mem [((p + 8#64).toNat, 8, -1#64)] := st7.memory
  have a7 : GHolds s7.σ [(2, sp - 32#64), (8, p), (10, -1#64)] :=
    holds_project st7.regs (by simp [offset_regs, R3, lookupG])
  obtain ⟨s8, run8, call3⟩ := (call_registers_summary offset_call_shape offset_call_decode s7
    (offset_call_pins st7.image) st7.good st7.image st7.tick st7.minstret _ a7
    (by change KeysOK [2, 8, 10]; decide) (by simp only [KeysAvoidRa, keysG]; decide)
    (by rfl)).run s7 ⟨st7.pc, rfl⟩
  have k8 : StaticKept c s8 :=
    k6.trans (StaticKept.of_log offInside static s8 (by rw [call3.memory, m7]))
  have rt8 := h.runtime.keep k8
  have leaveIn : LeaveInput offset_call.link (sp - 32#64) p 0x80064668#64
      (bytesVal .lw (read8 s8.σ.mem (0x80064668#64).toNat)) s8 := {
    toLeafInput := ⟨call3.good, call3.image, call3.minstret, gholds_lookup (n := 1) _ call3.regs (by rfl),
      by decide, call3.tick⟩
    idle := call3.toEffectPost.htifIdle (st7.toEffectPost.htifIdle post6.idle)
    stack := gholds_lookup (n := 2) _ call3.regs (by rfl)
    s0Reg := gholds_lookup (n := 8) _ call3.regs (by rfl)
    a0 := ⟨_, gholds_lookup (n := 10) _ call3.regs (by rfl)⟩
    frameLow := word _ 48 (by rw [show (sp - 32#64 - 16#64) = sp - 32#64 - BitVec.ofNat 64 16 from rfl, e16]; omega)
      (by decide) (by decide) (by decide)
    frameHigh := word _ 40 e8 (by decide) (by decide) (by decide)
    text := Or.inl (by rw [sp32]; unfold Image.textBase Image.textSize heapEnd at *; omega)
    rodata := Or.inl (by rw [sp32]; unfold Image.rodataBase Image.rodataSize heapEnd at *; omega)
    hook := rt8.leaveHookWord
    impure := by rw [rt8.impure, rp]
    errnoWrite := errnoW
    errnoValue := rfl
    errnoText := Or.inr (by decide)
    errnoRodata := Or.inr (by decide)
    apart := by
      intro a member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rw [sp32]
      unfold heapEnd at lower
      rcases member with rfl | rfl | rfl
      all_goals left; simp only [leaveHook, impurePtr, BitVec.toNat_ofNat]; omega
    errnoFrame := Or.inl (by rw [sp32]; unfold heapEnd at lower; simp only [BitVec.toNat_ofNat]; omega)
    pending := Or.inl (by rw [sp32]; unfold heapEnd at lower; simp only [pendingSignals, BitVec.toNat_ofNat]; omega)
    clear := rt8.clear }
  obtain ⟨s9, run9, post9⟩ := leave_blocking leaveIn (by rw [call3.pc, offset_call_target])
  have frame9 : FrameOnD (seekWindows sp p) s8.σ.mem s9.σ.mem := by
    intro a out
    simp only [seekWindows, seekCallWindows, List.cons_append, List.nil_append, OutW] at out
    apply post9.frame a
    · rw [sp32]; omega
    · simp only [BitVec.toNat_ofNat]; omega
  have m5 : s5.σ.mem = s1.σ.mem := by rw [call2.memory, st4.memory, q.memory, call1.memory]; rfl
  have m8 : s8.σ.mem = writeLog s6.σ.mem [((p + 8#64).toNat, 8, -1#64)] := by rw [call3.memory, m7]
  have frame : FrameOnD (seekWindows sp p) c.σ.mem s9.σ.mem := by
    intro a out
    rw [frame9 a out, m8, frameOn_writeLog _ _ _ offInside a out, post6.memory,
      frameOn_writeLog _ _ _ seekInside a (callOut a out), m5, m1, frameOn_writeLog _ _ _ fdInside a out]
  have recordByte (j : Nat) (hj : j < 8) : (s9.σ.mem[p.toNat + j]?).getD 0 = (s8.σ.mem[p.toNat + j]?).getD 0 :=
    post9.frame _ (Or.inl (by rw [sp32]; omega)) (Or.inr (by simp only [BitVec.toNat_ofNat]; omega))
  have offsetByte (j : Nat) (hj : j < 8) :
      (s9.σ.mem[p.toNat + 8 + j]?).getD 0 = (s8.σ.mem[p.toNat + 8 + j]?).getD 0 :=
    post9.frame _ (Or.inl (by rw [sp32]; omega)) (Or.inr (by simp only [BitVec.toNat_ofNat]; omega))
  have fdWord : bytesT s9.σ.mem p.toNat 4 = fd.setWidth 32 := by
    have offOnly : LogInW [⟨p.toNat + 8, p.toNat + 16⟩] [((p + 8#64).toNat, 8, -1#64)] := by
      simp only [LogInW, InsideW, and_true, or_false, e8p]; omega
    rw [bytesT_keep (m := s1.σ.mem) fun j hj => by
      have below : OutW [⟨p.toNat + 8, p.toNat + 16⟩] (p.toNat + j) := by
        simp only [OutW, and_true]; omega
      have apart : OutW (seekCallWindows sp) (p.toNat + j) := by
        simp only [seekCallWindows, OutW, and_true]; omega
      rw [recordByte j (by omega), m8, frameOn_writeLog _ _ _ offOnly (p.toNat + j) below,
        post6.memory, frameOn_writeLog _ _ _ seekInside (p.toNat + j) apart, m5],
      m1, word32_writeLog]
  have offsetWord : bytesT s9.σ.mem (p.toNat + 8) 8 = -1#64 := by
    rw [bytesT_keep (m := s8.σ.mem) offsetByte, m8, ← record_toNat (off := 8) (by omega)]
    exact OCaml.Vm.Gc.word_writeLog_at _ _ 0 _ _ rfl trivial
  have kept (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31)
      (hn : n ∉ [1, 2, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17]) : gprGet s9.σ n = gprGet c.σ n := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    exact (post9.kept n lo hi (by simp; omega)).trans <|
      (call3.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans <|
      (st7.toEffectPost.gpr_frame (by decide) n lo hi (by simp)).trans <|
      (post6.kept n lo hi (by simp [seekWrites]; omega)).trans <|
      (call2.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans <|
      (st4.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans <|
      (q.kept n lo hi (by simp; omega)).trans <|
      (call1.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans <|
      st1.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)
  have gprs : GprsKept c s9 :=
    (GprsKept.of_pins st1 (by decide) (by decide) (by simp [keysG, fd_regs])).trans
    ((GprsKept.of_pins call1 (by decide) (by decide) (by simp [keysG])).trans
    (q.gprs.trans
    ((GprsKept.of_pins st4 (by decide) (by decide) (by simp [keysG, seek_regs])).trans
    ((GprsKept.of_pins call2 (by decide) (by decide) (by simp [keysG])).trans
    (post6.gprs.trans
    ((GprsKept.of_pins st7 (by decide) (by decide) (by simp [keysG, offset_regs])).trans
    ((GprsKept.of_pins call3 (by decide) (by decide) (by simp [keysG])).trans post9.gprs)))))))
  exact ⟨s9, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
      (run8.trans run9))))))),
    { good := post9.good, image := post9.image, minstret := post9.minstret, tick := post9.tick,
      idle := post9.idle, pc := by rw [post9.pc]; rfl, link := post9.raReg, stack := post9.stack,
      record := post9.s0Reg, a0 := ⟨_, post9.result⟩,
      kept := kept, gprs := gprs, fdWord := fdWord, offsetWord := offsetWord, frame := frame }⟩

/-! ### Initialization, linking, epilogue -/

theorem LogWithin.inW {log : List WEntry} {lo hi : Nat} (h : LogWithin log lo hi) :
    LogInW [⟨lo, hi⟩] log := by
  induction log with
  | nil => trivial
  | cons e log ih =>
    exact ⟨Or.inl (h e List.mem_cons_self), ih fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem LogWithin.widen {log : List WEntry} {lo hi lo' hi' : Nat} (h : LogWithin log lo hi)
    (l : lo' ≤ lo) (u : hi ≤ hi') : LogWithin log lo' hi' :=
  fun e he => ⟨Nat.le_trans l (h e he).1, Nat.le_trans (h e he).2 u⟩

theorem LogWithin.append {l1 l2 : List WEntry} {lo hi : Nat} (h1 : LogWithin l1 lo hi)
    (h2 : LogWithin l2 lo hi) : LogWithin (l1 ++ l2) lo hi := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact h1 e h
  · exact h2 e h

/-- The record's `end` field address, `c->buff + IO_BUFFER_SIZE` as `addi` forms it. -/
theorem endAddress (p : BitVec 64) : p + 65536#64 + 72#64 = p + BitVec.ofNat 64 65608 := by
  rw [BitVec.add_assoc]; rfl

/-- `caml_open_descriptor_in`'s initialization of the record: `end`, `curr`,
`max`, `mutex`, `next` (the old head), `prev`, `refcount`/`flags` and `name`. -/
def recordInitLog (p head : BitVec 64) : List WEntry :=
  [((p + 40#64).toNat, 8, 0#64), ((p + 64#64).toNat, 8, 0#64), ((p + 56#64).toNat, 8, 0#64),
   ((p + 16#64).toNat, 8, p + (65536#64 + 72#64)), ((p + 32#64).toNat, 8, p + 72#64),
   ((p + 24#64).toNat, 8, p + 72#64), ((p + 48#64).toNat, 8, head),
   ((p + 65536#64 + 72#64).toNat, 8, 0#64)]

theorem recordInitLog_within {p head : BitVec 64} (high : p.toNat + recordBytes ≤ heapEnd) :
    LogWithin (recordInitLog p head) p.toNat (p.toNat + recordBytes) := by
  unfold recordBytes at high ⊢
  have t (off : Nat) (bound : off ≤ 65608) : (p + BitVec.ofNat 64 off).toNat = p.toNat + off :=
    record_toNat (by omega)
  intro e he
  simp only [recordInitLog, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [endAddress, t 16 (by decide), t 24 (by decide), t 32 (by decide), t 40 (by decide),
    t 48 (by decide), t 56 (by decide), t 64 (by decide), t 65608 (by decide)]
  all_goals omega

/-- The list update: the old head's `prev` (when there is one), then the head. -/
def linkLog (p head : BitVec 64) : List WEntry :=
  (if head = 0#64 then [] else [((head + 56#64).toNat, 8, p)]) ++ [(2147896128, 8, p)]

/-- At `caml_leave_blocking_section`'s return: the record, its old list head
and the prologue's four saves. -/
structure OpenLinkInput (sp ra s0 s1 s2 p head : BitVec 64) (c : Config) : Prop
    extends LeafInput offset_call.link c where
  idle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  stack : gprGet c.σ 2 = some (sp - 32#64)
  record : gprGet c.σ 8 = some p
  a0 : ∃ v, gprGet c.σ 10 = some v
  frame : NativeFrame sp 576
  low : heapStart ≤ p.toNat
  high : p.toNat + recordBytes ≤ heapEnd
  align : p.toNat % 16 = 0
  headWord : bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat) = head
  headRecord : head ≠ 0#64 → heapStart ≤ head.toNat ∧ head.toNat + 64 ≤ heapEnd ∧ head.toNat % 8 = 0
  savedRa : bytesVal .ld (read8 c.σ.mem (sp - 32#64 + 24#64).toNat) = ra
  savedS0 : bytesVal .ld (read8 c.σ.mem (sp - 32#64 + 16#64).toNat) = s0
  savedS1 : bytesVal .ld (read8 c.σ.mem (sp - 32#64 + 8#64).toNat) = s1
  savedS2 : bytesVal .ld (read8 c.σ.mem (sp - 32#64).toNat) = s2
  raAligned : ra.toNat % 4 = 0

/-- The return of `caml_open_descriptor_in` after the stores `log` since `c`. -/
structure OpenLinkPost (sp ra s0 s1 s2 p : BitVec 64) (log : List WEntry) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  idle : d.σ.regs.get? Register.htif_payload_writes = some (0#4)
  pc : pcOf d = some ra
  raReg : gprGet d.σ 1 = some ra
  stack : gprGet d.σ 2 = some sp
  result : gprGet d.σ 10 = some p
  s0Reg : gprGet d.σ 8 = some s0
  s1Reg : gprGet d.σ 9 = some s1
  s2Reg : gprGet d.σ 18 = some s2
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 8, 9, 10, 13, 14, 15, 18] → gprGet d.σ n = gprGet c.σ n
  gprs : GprsKept c d
  memory : d.σ.mem = writeLog c.σ.mem log

theorem stack_above {sp x : BitVec 64} {k : Nat} (lower : heapEnd + 576 ≤ sp.toNat)
    (hx : x.toNat = sp.toNat - 32 + k) : heapEnd ≤ x.toNat := by
  generalize heapEnd = E at *
  omega

/-- The epilogue from `0x800151bc`, once the record is initialized and linked. -/
theorem open_epilogue {sp ra s0 s1 s2 p head : BitVec 64} {c e : Config} (h : OpenLinkInput sp ra s0 s1 s2 p head c)
    (log : List WEntry) (within : LogWithin log heapStart heapEnd)
    (memory : e.σ.mem = writeLog c.σ.mem log) (good : GoodState e.σ) (image : ExecutableImage e)
    (minstret : ∃ v, e.σ.regs.get? Register.minstret = some v) (tick : e.tick < 2)
    (idle : e.σ.regs.get? Register.htif_payload_writes = some (0#4)) (pc : pcOf e = some 0x800151bc#64)
    (link : gprGet e.σ 1 = some offset_call.link) (stack : gprGet e.σ 2 = some (sp - 32#64))
    (record : gprGet e.σ 8 = some p)
    (kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [9, 13, 14, 15] → gprGet e.σ n = gprGet c.σ n)
    (gprs : GprsKept c e) :
    ∃ d, Steps e d ∧ OpenLinkPost sp ra s0 s1 s2 p (log ++ [(2147896128, 8, p)]) c d := by
  have frame := h.frame
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have lower := frame.lower
  have upper := frame.upper
  have spAligned := frame.aligned
  have sp32 : (sp - 32#64).toNat = sp.toNat - 32 := stack_toNat frame (by decide)
  have slot (k : Nat) (bound : k ≤ 24) : (sp - 32#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 32 + k := by
    rw [BitVec.toNat_add, sp32, BitVec.toNat_ofNat]; omega
  have read (x : BitVec 64) (k : Nat) (hx : x.toNat = sp.toNat - 32 + k) (bound : k ≤ 24) :
      ReadWindow x 8 :=
    ⟨by rw [hx]; omega, by rw [hx]; unfold Layout.sym_stack_top at upper; omega,
      Or.inr (by rw [hx]; unfold Layout.sym_tohost; omega)⟩
  have same (x : Nat) (hx : heapEnd ≤ x) : read8 e.σ.mem x = read8 c.σ.mem x := by
    rw [memory]; exact ConsoleWrite.read8_outside within (Or.inr hx)
  let R : Nat → BitVec 64 := fun n => if n = 1 then offset_call.link else if n = 2 then sp - 32#64 else p
  have s24 := slot 24 (by decide)
  have s16 := slot 16 (by decide)
  have s8 := slot 8 (by decide)
  have out (k : Nat) (bound : k ≤ 24) : OutLRange [(2147896128, 8, p)] (sp.toNat - 32 + k) 8 := by
    simp only [OutLRange, and_true]; omega
  have ld (k : Nat) (x : BitVec 64) (hx : x.toNat = sp.toNat - 32 + k) (bound : k ≤ 24) :
      read8 e.σ.mem x.toNat = read8 c.σ.mem x.toNat := by
    have far : heapEnd ≤ x.toNat := stack_above lower hx
    exact same x.toNat far
  have raSlot : bytesVal .ld (read8 e.σ.mem (sp - 32#64 + 24#64).toNat) = ra := by
    rw [ld 24 _ s24 (by decide)]; exact h.savedRa
  obtain ⟨d, run, post⟩ := (done_fast e ra R ⟨good, image, minstret, link,
      show offset_call.link.toNat % 4 = 0 by decide, tick⟩
    ⟨stack, record, trivial⟩
    (read _ 24 s24 (by decide))
    (read _ 16 s16 (by decide)) (by show OutLRange [(2147896128, 8, p)] (sp - 32#64 + 16#64).toNat 8; rw [s16]; exact out 16 (by decide))
    (read _ 8 s8 (by decide)) (by show OutLRange [(2147896128, 8, p)] (sp - 32#64 + 8#64).toNat 8; rw [s8]; exact out 8 (by decide))
    (read _ 0 (by show (sp - 32#64).toNat = sp.toNat - 32 + 0; rw [sp32, Nat.add_zero]) (by decide))
    (by show OutLRange [(2147896128, 8, p)] (sp - 32#64).toNat 8; rw [sp32]; exact out 0 (by decide))
    (by show ImageOutside [(2147896128, 8, p)]
        constructor <;> simp only [OutLRange, Image.textBase, Image.textSize, Image.rodataBase,
          Image.rodataSize] <;> decide)
    raSlot h.raAligned).run e ⟨pc, rfl⟩
  have e2 : sp - 32#64 + 32#64 = sp := BitVec.sub_add_cancel sp 32#64
  refine ⟨d, run, ?_⟩
  exact {
    good := post.good, image := post.image, minstret := post.minstret, tick := post.tick
    idle := post.toEffectPost.htifIdle idle
    pc := post.pc
    raReg := (gholds_lookup (n := 1) _ post.regs (by rfl)).trans (congrArg some (by
      show bytesVal .ld (read8 e.σ.mem (sp - 32#64 + 24#64).toNat) = ra
      exact raSlot))
    stack := (gholds_lookup (n := 2) _ post.regs (by rfl)).trans (congrArg some e2)
    result := gholds_lookup (n := 10) _ post.regs (by rfl)
    s0Reg := (gholds_lookup (n := 8) _ post.regs (by rfl)).trans (congrArg some (by
      show bytesVal .ld (read8 e.σ.mem (sp - 32#64 + 16#64).toNat) = s0
      rw [ld 16 _ s16 (by decide)]; exact h.savedS0))
    s1Reg := (gholds_lookup (n := 9) _ post.regs (by rfl)).trans (congrArg some (by
      show bytesVal .ld (read8 e.σ.mem (sp - 32#64 + 8#64).toNat) = s1
      rw [ld 8 _ s8 (by decide)]; exact h.savedS1))
    s2Reg := (gholds_lookup (n := 18) _ post.regs (by rfl)).trans (congrArg some (by
      show bytesVal .ld (read8 e.σ.mem (sp - 32#64).toNat) = s2
      rw [ld 0 _ (by rw [sp32, Nat.add_zero]) (by decide)]; exact h.savedS2))
    kept := fun n lo hi hn => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      exact (post.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
        (kept n lo hi (by simp; omega))
    gprs := gprs.trans (GprsKept.of_pins post (by decide) (by decide) (by simp [keysG, done_regs]))
    memory := by rw [post.memory, memory, ← writeLog_append]; rfl }

/-- Initialize the record, link it at the head of `caml_all_opened_channels`
(updating the old head's `prev`) and return it. -/
theorem open_link (c : Config) {sp ra s0 s1 s2 p head : BitVec 64}
    (h : OpenLinkInput sp ra s0 s1 s2 p head c) :
    FnSummary 0x80015178#64 (fun d => d = c)
      (fun d => OpenLinkPost sp ra s0 s1 s2 p (recordInitLog p head ++ linkLog p head) c d) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have low := h.low
  have high := h.high
  have align := h.align
  unfold recordBytes at high
  obtain ⟨v, a0⟩ := h.a0
  let R : Nat → BitVec 64 := fun n =>
    if n = 1 then offset_call.link else if n = 2 then sp - 32#64 else if n = 8 then p
    else if n = 14 then head else v
  have word (off : Nat) (bound : off ≤ 64) (aligned : off % 8 = 0) : WriteWindow (p + BitVec.ofNat 64 off) 8 :=
    recordWord (p := p) low (by omega) align aligned
  have endWord : WriteWindow (p + 65536#64 + 72#64) 8 := by
    rw [endAddress]; exact recordWord (p := p) low (by omega) align (by decide)
  have initWithin : LogWithin (recordInitLog p head) heapStart heapEnd :=
    LogWithin.widen (recordInitLog_within (head := head) h.high) low (by unfold recordBytes; omega)
  have initOutside : ImageOutside
      (recordInitLog p (bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat))) :=
    heap_image_outside (LogWithin.inW
      (LogWithin.widen (recordInitLog_within h.high) low (by unfold recordBytes; omega)))
  have initMemory {d : Config}
      (m : d.σ.mem = writeLog c.σ.mem (recordInitLog p (bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat)))) :
      d.σ.mem = writeLog c.σ.mem (recordInitLog p head) := by rw [m, h.headWord]
  by_cases hz : head = 0#64
  · obtain ⟨e, run1, st⟩ := (first_fast c R h.toLeafInput ⟨h.stack, h.record, a0, trivial⟩
      (word 40 (by decide) (by decide)) (word 64 (by decide) (by decide)) (word 56 (by decide) (by decide))
      (word 16 (by decide) (by decide)) (word 32 (by decide) (by decide)) (word 24 (by decide) (by decide))
      (word 48 (by decide) (by decide)) endWord initOutside
      (by show guardB .BEQ (bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat)) 0#64 = true
          rw [h.headWord, hz]; rfl)).run c ⟨pc, rfl⟩
    obtain ⟨d, run2, post⟩ := open_epilogue h (recordInitLog p head) initWithin (initMemory st.memory)
      st.good st.image st.minstret st.tick (st.toEffectPost.htifIdle h.idle) st.pc
      ((st.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans h.raReg)
      (gholds_lookup (n := 2) _ st.regs (by rfl)) (gholds_lookup (n := 8) _ st.regs (by rfl))
      (fun n lo hi hn => st.toEffectPost.gpr_frame (by decide) n lo hi hn)
      (GprsKept.of_pins st (by decide) (by decide) (by simp [keysG, first_regs]))
    have shape : recordInitLog p head ++ linkLog p head = recordInitLog p head ++ [(2147896128, 8, p)] := by
      simp [linkLog, hz]
    exact ⟨d, run1.trans run2, shape ▸ post⟩
  · obtain ⟨e1, run1, st⟩ := (link_fast c R h.toLeafInput ⟨h.stack, h.record, a0, trivial⟩
      (word 40 (by decide) (by decide)) (word 64 (by decide) (by decide)) (word 56 (by decide) (by decide))
      (word 16 (by decide) (by decide)) (word 32 (by decide) (by decide)) (word 24 (by decide) (by decide))
      (word 48 (by decide) (by decide)) endWord initOutside
      (by show guardB .BEQ (bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat)) 0#64 = false
          rw [h.headWord]; exact guard_beq_false hz)).run c ⟨pc, rfl⟩
    obtain ⟨hLow, hHigh, hAlign⟩ := h.headRecord hz
    have prevAddr : (head + 56#64).toNat = head.toNat + 56 := record_toNat (by omega)
    have prevWithin : LogWithin [((head + 56#64).toNat, 8, p)] heapStart heapEnd := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      simp only [prevAddr]
      omega
    have link1 : gprGet e1.σ 1 = some offset_call.link :=
      (st.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans h.raReg
    obtain ⟨e2, run2, st2⟩ := (prev_fast e1 R ⟨st.good, st.image, st.minstret, link1,
        show offset_call.link.toNat % 4 = 0 by decide, st.tick⟩
      ⟨gholds_lookup (n := 2) _ st.regs (by rfl), gholds_lookup (n := 8) _ st.regs (by rfl),
        gholds_lookup (n := 10) _ st.regs (by rfl),
        (gholds_lookup (n := 14) _ st.regs (by rfl)).trans (congrArg some h.headWord), trivial⟩
      (show WriteWindow (head + 56#64) 8 from
        heapWindow (by rw [prevAddr]; omega) (by rw [prevAddr]; omega) (by rw [prevAddr]; omega))
      (heap_image_outside (LogWithin.inW prevWithin))).run e1 ⟨st.pc, rfl⟩
    have memory : e2.σ.mem = writeLog c.σ.mem (recordInitLog p head ++ [((head + 56#64).toNat, 8, p)]) := by
      rw [writeLog_append, ← initMemory st.memory]; exact st2.memory
    obtain ⟨d, run3, post⟩ := open_epilogue h _ (LogWithin.append initWithin prevWithin) memory
      st2.good st2.image st2.minstret st2.tick (st2.toEffectPost.htifIdle (st.toEffectPost.htifIdle h.idle))
      st2.pc ((st2.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans link1)
      (gholds_lookup (n := 2) _ st2.regs (by rfl)) (gholds_lookup (n := 8) _ st2.regs (by rfl))
      (fun n lo hi hn => (st2.toEffectPost.gpr_frame (by decide) n lo hi (by simp)).trans
        (st.toEffectPost.gpr_frame (by decide) n lo hi hn))
      ((GprsKept.of_pins st (by decide) (by decide) (by simp [keysG, link_regs])).trans
        (GprsKept.of_pins st2 (by decide) (by decide) (by simp [keysG, prev_regs])))
    have shape : recordInitLog p head ++ linkLog p head =
        recordInitLog p head ++ [((head + 56#64).toNat, 8, p)] ++ [(2147896128, 8, p)] := by
      simp [linkLog, hz]
    exact ⟨d, run1.trans (run2.trans run3), shape ▸ post⟩

/-! ### The whole call -/

/-- `StatCheckedReturned.framed_byte` beyond the arena: the checked allocation
keeps every byte outside its stack frame that the allocator does not own. -/
theorem _root_.OCaml.Vm.Boot.Startup.StatCheckedReturnedL.kept_byte {H capacity sp ra s0 n before after a}
    (w : StatCheckedReturnedL live H capacity sp ra s0 n before after)
    (frame : NativeFrame sp 544) (apart : a < nativeFrameBase sp 544 ∨ sp.toNat ≤ a)
    (outside : ¬ vsaFoot H a) :
    (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0 := by
  rcases apart with below | above
  · have short := frame.resize (small := 32) (by decide) (by decide)
    have nested : NativeFrame (nativeStack sp 32) 512 := frame.nested (front := 32) (by decide)
    have base := short.stack_nat
    have unowned : ¬ mS H (nativeStack sp 32) a := by
      intro owned
      rcases owned with scratch | heap
      · unfold stackWin InExt allocHeadroom at scratch
        rw [base] at scratch
        unfold nativeFrameBase at below scratch
        omega
      · exact outside heap
    have unchanged := w.allocation.allocation.memory a unowned
    change (w.allocated.σ.mem[a]?).getD 0 = (w.allocation.atMalloc.σ.mem[a]?).getD 0 at unchanged
    have restored : after.σ.mem = w.allocated.σ.mem := w.returned.memory
    have low : a < nativeFrameBase sp 32 := by unfold nativeFrameBase at below ⊢; omega
    rw [restored, unchanged, w.allocation.call.memory, w.allocation.setup.memory,
      frameOn_writeLog _ _ _ (statCheckedLog_inside short) a ⟨Or.inl low, trivial⟩]
  · exact (w.caller_frame frame).byte a above

/-- Where `caml_open_descriptor_in` and its callees store, besides the
allocator: the native stack below the entry sp, newlib's two `errno` words,
the record, `caml_all_opened_channels` and the old head's `prev` word. -/
def openWindows (sp p head : BitVec 64) : List W :=
  [⟨sp.toNat - 576, sp.toNat⟩, ⟨0x80064668, 0x8006466c⟩, ⟨0x80064d48, 0x80064d4c⟩,
   ⟨p.toNat, p.toNat + recordBytes⟩, ⟨0x80064b40, 0x80064b48⟩] ++
  (if head = 0#64 then [] else [⟨head.toNat + 56, head.toNat + 64⟩])

theorem insideW_of_mem {ws : List W} {w : W} {a n : Nat} (member : w ∈ ws) (lo : w.lo ≤ a)
    (hi : a + n ≤ w.hi) : InsideW ws a n := by
  induction ws with
  | nil => cases member
  | cons x ws ih =>
    rcases List.mem_cons.mp member with rfl | rest
    · exact Or.inl ⟨lo, hi⟩
    · exact Or.inr (ih rest)

/-- Eight bytes that read the same give the same `read8`. -/
theorem read8_keep {m m' : Std.ExtHashMap Nat (BitVec 8)} {a : Nat}
    (same : ∀ i, i < 8 → (m'[a + i]?).getD 0 = (m[a + i]?).getD 0) : read8 m' a = read8 m a := by
  simp only [OCaml.Vm.Primitives.read8, List.cons.injEq, and_true]
  exact ⟨by simpa using same 0 (by decide), same 1 (by decide), same 2 (by decide), same 3 (by decide),
    same 4 (by decide), same 5 (by decide), same 6 (by decide), same 7 (by decide)⟩

/-- What `caml_open_descriptor_in(fd)` needs: a ready runtime with room for the
record, a 576-byte native frame, a seekable console descriptor, the console
runtime, and the current list head inside a live block when there is one. -/
structure OpenInput (live : Nat → Prop) (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra s0 s1 s2 fd head : BitVec 64)
    (c : Config) : Prop where
  ready : RuntimeReadyL live H (capacity + charge) sp ra c
  frame : NativeFrame sp 576
  saved0 : gprGet c.σ 8 = some s0
  saved1 : gprGet c.σ 9 = some s1
  saved2 : gprGet c.σ 18 = some s2
  fdReg : gprGet c.σ 10 = some fd
  charged : vsaChg recordBytes charge
  runtime : ConsoleWrite.ConsoleRuntime c
  descriptor : SeekFd fd c
  headWord : bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat) = head
  /-- The old head is a channel record: a live block of `H`, word-aligned. -/
  headLive : head ≠ 0#64 → (∃ e ∈ H, e.1 ≤ head.toNat ∧ head.toNat + 64 ≤ e.1 + e.2) ∧ head.toNat % 8 = 0

/-- `caml_open_descriptor_in(fd)` returned the record `record`: allocated,
`fd` and `offset` stored in the blocking section, initialized and linked. -/
structure OpenedIn (live : Nat → Prop) (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 fd head : BitVec 64)
    (c d : Config) where
  allocated : Config
  linked : Config
  record : BitVec 64
  allocation : OpenAllocated live H capacity sp ra s0 s1 s2 fd c allocated
  recordReg : record = vsaReg allocation.allocation.allocated 10
  seek : OpenSeekPost sp record fd allocated linked
  link : OpenLinkPost sp ra s0 s1 s2 record (recordInitLog record head ++ linkLog record head) linked d
  heap : HeapReady ((record.toNat, recordBytes) :: H) capacity d
  /-- the record is a fresh, 16-byte-aligned block of the arena -/
  low : heapStart ≤ record.toNat
  high : record.toNat + recordBytes ≤ heapEnd
  align : record.toNat % 16 = 0
  fresh : ∀ e ∈ H, ∀ y, VsaIris.InExt (record.toNat, recordBytes) y → ¬ VsaIris.InExt e y
  static : StaticKept c d
  frame : ∀ a, OutW (openWindows sp record head) a → ¬ vsaFoot H a →
    (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0

theorem open_descriptor_in [LibraryLive live] (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 s2 fd head : BitVec 64) (h : OpenInput live H capacity charge sp ra s0 s1 s2 fd head c) :
    FnSummary 0x80015130#64 (fun d => d = c)
      (fun d => Nonempty (OpenedIn live H capacity sp ra s0 s1 s2 fd head c d)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have frame := h.frame
  have lower := frame.lower
  have upper := frame.upper
  have sp32 : (sp - 32#64).toNat = sp.toNat - 32 := stack_toNat frame (by decide)
  have nested : NativeFrame (sp - 32#64) 544 := by
    rw [openStack]; exact frame.nested (front := 32) (by decide)
  have short := frame.resize (small := 32) (by decide) (by decide)
  obtain ⟨allocated, run1, ⟨A⟩⟩ := (open_allocate c H capacity charge sp ra s0 s1 s2 fd h.ready frame
    h.saved0 h.saved1 h.saved2 h.fdReg h.charged).run c ⟨pc, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = A.allocation := ⟨_, rfl⟩
  obtain ⟨_, pLow, pHigh, pFresh⟩ := FreshBlock.destruct w.allocation.allocation.result.fresh
  have pAlign : (vsaReg w.allocated 10).toNat % 16 = 0 := w.allocation.allocation.result.align
  have pReg : gprGet allocated.σ 10 = some (vsaReg w.allocated 10) :=
    gholds_lookup (n := 10) _ w.returned.regs (by rfl)
  change heapStart ≤ (vsaReg w.allocated 10).toNat at pLow
  change (vsaReg w.allocated 10).toNat + 65616 ≤ heapEnd at pHigh
  change ∀ e ∈ H, ∀ a, VsaIris.InExt ((vsaReg w.allocated 10).toNat, 65616) a → ¬ VsaIris.InExt e a at pFresh
  generalize hp : vsaReg w.allocated 10 = p at pLow pHigh pFresh pAlign pReg
  -- the prologue's saves and everything the runtime reads survive the allocation
  have saveInside := openSaveLog_inside (ra := ra) (s0 := s0) (s1 := s1) (s2 := s2) short
  have toAllocated (a : Nat) (apart : a < sp.toNat - 576 ∨ sp.toNat - 32 ≤ a) (notFoot : ¬ vsaFoot H a)
      (notSave : a < sp.toNat - 32 ∨ sp.toNat ≤ a) :
      (allocated.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := by
    have apart' : a < nativeFrameBase (sp - 32#64) 544 ∨ (sp - 32#64).toNat ≤ a := by
      unfold nativeFrameBase; rw [sp32, Nat.sub_sub]; arena_omega
    have save : (a < nativeFrameBase sp 32 ∨ sp.toNat ≤ a) ∧ True := ⟨by unfold nativeFrameBase; arena_omega, trivial⟩
    rw [w.kept_byte nested apart' notFoot, A.call.memory, A.setup.memory,
      frameOn_writeLog _ _ _ saveInside a save]
  have staticAlloc : StaticKept c allocated := fun a ⟨below, notAlloc, _⟩ =>
    toAllocated a (Or.inl (by arena_omega)) (fun foot => by
      rcases foot with g | ⟨l, _, _⟩
      · exact notAlloc g
      · arena_omega) (Or.inl (by arena_omega))
  have fdAt : gprGet allocated.σ 18 = some fd :=
    w.keep_saved (by decide) (gholds_lookup (n := 18) _ A.call.regs (by rfl))
  have seekIn : OpenSeekInput sp p fd allocated := {
    toLeafInput := w.ready.toLeafInput
    idle := w.ready.platform.htifIdle
    stack := w.ready.stack
    record := pReg
    fdReg := fdAt
    frame := frame
    low := pLow
    high := pHigh
    align := pAlign
    runtime := h.runtime.keep staticAlloc
    descriptor := h.descriptor.keep staticAlloc }
  obtain ⟨linked, run2, S⟩ := (open_seek allocated sp p fd seekIn).run allocated ⟨w.returned.pc, rfl⟩
  -- the list head and the prologue's saves at the end of the blocking section
  have notFootHigh (a : Nat) (ha : heapEnd ≤ a) : ¬ vsaFoot H a := by
    rintro (g | ⟨_, l, _⟩)
    · rcases allocGlobal_off_arena a g with x | x
      · unfold heapStart heapEnd at *; omega
      · unfold allocGlobal InRange at g; unfold heapEnd at ha; omega
    · omega
  have outSeek (a : Nat) (below : a < heapStart) (notErr : a < 0x80064668 ∨ 0x8006466c ≤ a)
      (notErr2 : a < 0x80064d48 ∨ 0x80064d4c ≤ a) : OutW (seekWindows sp p) a := by
    simp only [seekWindows, seekCallWindows, List.cons_append, List.nil_append, OutW, and_true]
    refine ⟨Or.inl (by arena_omega), notErr, notErr2, Or.inl (by arena_omega)⟩
  have headBytes : read8 linked.σ.mem (2147896128#64).toNat = read8 c.σ.mem (2147896128#64).toNat := by
    apply read8_keep
    intro i hi
    have g : (2147896128#64).toNat = 0x80064b40 := rfl
    rw [g, S.frame _ (outSeek _ (by unfold heapStart; omega) (Or.inr (by omega)) (Or.inl (by omega)))]
    apply toAllocated _ (Or.inl (by arena_omega)) _ (Or.inl (by arena_omega))
    rintro (x | ⟨l, _, _⟩)
    · unfold allocGlobal InRange at x; omega
    · unfold heapStart at l; omega
  have slotBytes (x : Nat) (lo : sp.toNat - 32 ≤ x) (hi : x + 8 ≤ sp.toNat) :
      read8 linked.σ.mem x = read8 (writeLog c.σ.mem (openSaveLog sp ra s0 s1 s2)) x := by
    apply read8_keep
    intro i hi'
    have out : OutW (seekWindows sp p) (x + i) := by
      simp only [seekWindows, seekCallWindows, List.cons_append, List.nil_append, OutW, and_true]
      refine ⟨Or.inr (by omega), Or.inr (by arena_omega), Or.inr (by arena_omega), Or.inr (by arena_omega)⟩
    rw [S.frame _ out, w.kept_byte nested (Or.inr (by rw [sp32]; omega))
      (notFootHigh _ (by arena_omega)), A.call.memory, A.setup.memory]
  have slotNat (k : Nat) (bound : k ≤ 24) : (sp - 32#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 32 + k := by
    rw [BitVec.toNat_add, sp32, BitVec.toNat_ofNat]; arena_omega
  have s24 := slotNat 24 (by decide)
  have s16 := slotNat 16 (by decide)
  have s8 := slotNat 8 (by decide)
  have saveRead (i : Nat) (x : Nat) (v : BitVec 64) (entry : (openSaveLog sp ra s0 s1 s2)[i]? = some (x, 8, v))
      (later : OutLRange ((openSaveLog sp ra s0 s1 s2).drop (i + 1)) x 8)
      (lo : sp.toNat - 32 ≤ x) (hi : x + 8 ≤ sp.toNat) : bytesVal .ld (read8 linked.σ.mem x) = v := by
    rw [slotBytes x lo hi, read8_value]
    exact OCaml.Vm.Gc.word_writeLog_at _ _ i x v entry later
  have linkIn : OpenLinkInput sp ra s0 s1 s2 p head linked := {
    toLeafInput := ⟨S.good, S.image, S.minstret, S.link, by decide, S.tick⟩
    idle := S.idle
    stack := S.stack
    record := S.record
    a0 := S.a0
    frame := frame
    low := pLow
    high := pHigh
    align := pAlign
    headWord := by rw [headBytes]; exact h.headWord
    headRecord := fun hz => by
      obtain ⟨⟨e, he, lo, hi⟩, aligned⟩ := h.headLive hz
      have bounds := h.ready.heap.block_bounds (q := e.1) (n := e.2) he
      exact ⟨by arena_omega, by arena_omega, aligned⟩
    savedRa := saveRead 1 (sp - 32#64 + 24#64).toNat ra rfl
      (by simp only [openSaveLog, List.drop, OutLRange, and_true, s16, s8, s24]; arena_omega)
      (by rw [s24]; arena_omega) (by rw [s24]; arena_omega)
    savedS0 := saveRead 2 (sp - 32#64 + 16#64).toNat s0 rfl
      (by simp only [openSaveLog, List.drop, OutLRange, and_true, s8, s16]; arena_omega)
      (by rw [s16]; arena_omega) (by rw [s16]; arena_omega)
    savedS1 := saveRead 3 (sp - 32#64 + 8#64).toNat s1 rfl (by simp only [openSaveLog, List.drop, OutLRange])
      (by rw [s8]; arena_omega) (by rw [s8]; arena_omega)
    savedS2 := saveRead 0 (sp - 32#64).toNat s2 rfl
      (by simp only [openSaveLog, List.drop, OutLRange, and_true, s24, s16, s8, sp32]; arena_omega)
      (by rw [sp32]; exact Nat.le_refl _) (by rw [sp32]; arena_omega)
    raAligned := h.ready.aligned }
  obtain ⟨d, run3, L⟩ := (open_link linked linkIn).run linked ⟨S.pc, rfl⟩
  -- readiness, the runtime globals and the frame over the whole call
  have heapA : HeapReady ((p.toNat, recordBytes) :: H) capacity allocated := by
    have r := w.ready.heap
    rw [hp] at r
    exact r
  have mD : d.σ.mem = writeLog linked.σ.mem (recordInitLog p head ++ linkLog p head) := L.memory
  have initW : LogWithin (recordInitLog p head) p.toNat (p.toNat + recordBytes) :=
    recordInitLog_within (by unfold recordBytes; exact pHigh)
  have prevW (hz : head ≠ 0#64) : head.toNat + 64 ≤ heapEnd ∧ heapStart ≤ head.toNat := by
    obtain ⟨hl, hh, _⟩ := linkIn.headRecord hz
    exact ⟨hh, hl⟩
  have prevNat (hz : head ≠ 0#64) : (head + 56#64).toNat = head.toNat + 56 :=
    record_toNat (by have := (prevW hz).1; omega)
  have linkInside : LogInW (openWindows sp p head) (recordInitLog p head ++ linkLog p head) := by
    apply OCaml.Vm.Gc.logInW_of_forall
    intro e he
    rcases List.mem_append.mp he with hi | hl
    · have x := initW e hi
      exact insideW_of_mem (w := ⟨p.toNat, p.toNat + recordBytes⟩) (by simp [openWindows]) x.1 x.2
    · by_cases hz : head = 0#64
      · simp only [linkLog, hz, ite_true, List.nil_append, List.mem_singleton] at hl
        subst hl
        exact insideW_of_mem (w := ⟨0x80064b40, 0x80064b48⟩) (by simp [openWindows]) (Nat.le_refl _) (Nat.le_refl _)
      · simp only [linkLog, hz, ite_false, List.singleton_append, List.mem_cons,
          List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact insideW_of_mem (w := ⟨head.toNat + 56, head.toNat + 64⟩) (by simp [openWindows, hz])
            (by dsimp only; rw [prevNat hz]; exact Nat.le_refl _) (by dsimp only; rw [prevNat hz]; omega)
        · exact insideW_of_mem (w := ⟨0x80064b40, 0x80064b48⟩) (by simp [openWindows]) (Nat.le_refl _) (Nat.le_refl _)
  have staticInside : LogInW [⟨heapStart, heapEnd⟩, ⟨0x80064b40, 0x80064b48⟩]
      (recordInitLog p head ++ linkLog p head) := by
    apply OCaml.Vm.Gc.logInW_of_forall
    intro e he
    rcases List.mem_append.mp he with hi | hl
    · have x := initW e hi
      unfold recordBytes at x
      exact Or.inl ⟨by arena_omega, by arena_omega⟩
    · by_cases hz : head = 0#64
      · simp only [linkLog, hz, ite_true, List.nil_append, List.mem_singleton] at hl
        subst hl
        exact Or.inr (Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩)
      · simp only [linkLog, hz, ite_false, List.singleton_append, List.mem_cons,
          List.not_mem_nil, or_false] at hl
        have b := prevW hz
        rcases hl with rfl | rfl
        · exact Or.inl ⟨by dsimp only; rw [prevNat hz]; arena_omega, by dsimp only; rw [prevNat hz]; arena_omega⟩
        · exact Or.inr (Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩)
  have staticD : StaticKept linked d :=
    StaticKept.of_log staticInside (fun a ⟨below, _, global⟩ => by
      unfold Layout.sym_caml_all_opened_channels at global
      exact ⟨Or.inl below, global, trivial⟩) d mD
  have seekOfOpen (a : Nat) (o : OutW (openWindows sp p head) a) : OutW (seekWindows sp p) a := by
    have base := ((outW_append _ _ a).mp o).1
    simp only [OutW, and_true] at base
    obtain ⟨o1, o2, o3, o4, _⟩ := base
    unfold recordBytes at o4
    simp only [seekWindows, seekCallWindows, List.cons_append, List.nil_append, OutW, and_true]
    exact ⟨by arena_omega, o2, o3, by arena_omega⟩
  have heap : HeapReady ((p.toNat, recordBytes) :: H) capacity d := by
    apply OCaml.Vm.Gc.HeapReady.keep_windows heapA (ws := openWindows sp p head)
    · intro x hx
      unfold openWindows at hx
      rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl (by dsimp only; arena_omega))
        · exact Or.inr (Or.inr (Or.inl fun a lo hi => errnoBytes_mem.mpr (Or.inl ⟨lo, hi⟩)))
        · exact Or.inr (Or.inr (Or.inl fun a lo hi => errnoBytes_mem.mpr (Or.inr ⟨lo, hi⟩)))
        · exact Or.inl ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
        · refine Or.inr (Or.inr (Or.inr ⟨by decide, fun a lo hi => ⟨?_, ?_⟩⟩))
          · dsimp only at lo hi; unfold allocGlobal InRange; omega
          · dsimp only at lo hi
            unfold OCaml.Vm.Gc.HeapPinned Image.textBase Image.textSize allocatorImpureAddr Layout.sym_Caml_state
              Layout.sym_pool
            omega
      · by_cases hz : head = 0#64
        · simp [hz] at hx
        · simp only [hz, ite_false, List.mem_singleton] at hx
          subst hx
          obtain ⟨⟨e, he, lo, hi⟩, _⟩ := h.headLive hz
          exact Or.inl ⟨e, List.mem_cons_of_mem _ he, by dsimp only; omega, by dsimp only; omega⟩
    · intro a out
      have o := OCaml.Vm.Gc.outW_all out
      rw [mD, frameOn_writeLog _ _ _ linkInside a o]
      exact S.frame a (seekOfOpen a o)
  have frameP : ∀ a, OutW (openWindows sp p head) a → ¬ vsaFoot H a →
      (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := by
    intro a o notFoot
    have base := ((outW_append _ _ a).mp o).1
    simp only [OutW, and_true] at base
    obtain ⟨o1, _⟩ := base
    rw [mD, frameOn_writeLog _ _ _ linkInside a o, S.frame a (seekOfOpen a o)]
    exact toAllocated a (by arena_omega) notFoot (by arena_omega)
  exact ⟨d, run1.trans (run2.trans run3),
    ⟨{ allocated := allocated, linked := linked, record := p, allocation := A
       recordReg := by rw [← hw]; exact hp.symm
       seek := S, link := L, heap := heap
       low := pLow, high := pHigh, align := pAlign, fresh := pFresh
       static := staticAlloc.trans ((StaticKept.of_frame S.frame (seekWindows_static frame pLow)).trans staticD)
       frame := frameP }⟩⟩

end OCaml.Vm.Primitives.Channel
