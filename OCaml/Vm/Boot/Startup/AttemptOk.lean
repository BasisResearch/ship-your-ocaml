import OCaml.Vm.Boot.Startup.AttemptOkSteps
import OCaml.Vm.Boot.Startup.AttemptOpenOpenCallInterface
import OCaml.Vm.Boot.Startup.AttemptOpenSeekCallInterface
import OCaml.Vm.Boot.Startup.AttemptOpenReadCallInterface
import OCaml.Vm.Boot.Startup.LseekFile
import OCaml.Vm.Boot.Startup.ReadFile
import OCaml.Vm.Boot.Startup.StrncmpWord
import OCaml.Vm.Boot.Startup.AttemptOpenPrefix
import OCaml.Vm.Boot.WhileMinEmbedFiles
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_attempt_open after `open` returned descriptor 3 for "/prog": seek to
the trailer, read it, fix its byte order, check the magic, record the name
and return the descriptor. -/

/-- What caml_attempt_open writes in place: the trailer slot and `magicstr`. -/
def attemptWindows : List W :=
  [⟨WhileMinElfParse.trailSlot.toNat, WhileMinElfParse.trailSlot.toNat + 16⟩,
    ⟨Layout.sym_magicstr, Layout.sym_magicstr + 13⟩,
    ⟨WhileMinElfParse.exeNameSlot.toNat, WhileMinElfParse.exeNameSlot.toNat + 8⟩]

theorem attemptWindows_out_pins (pin : Nat × BitVec 8) (member : pin ∈ VsaIris.Sym.allocText) :
    OutW attemptWindows pin.1 := by
  have source := allocator_sources pin member
  unfold AllocatorByteSource at source
  have trail : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
  have exe : WhileMinElfParse.exeNameSlot.toNat = 0x87ffffa0 := by decide
  simp only [OutW, attemptWindows, trail, exe, and_true]
  split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr, Layout.sym_magicstr] at * <;>
    omega

theorem attemptWindows_out_foot {H : List (Nat × Nat)} {a : Nat} (foot : vsaFoot H a) : OutW attemptWindows a := by
  have trail : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
  have exe : WhileMinElfParse.exeNameSlot.toNat = 0x87ffffa0 := by decide
  simp only [OutW, attemptWindows, trail, exe, and_true]
  rcases foot with global | ⟨lo, hi, _⟩
  · unfold allocGlobal InRange at global; unfold Layout.sym_magicstr; omega
  · unfold heapStart heapEnd at *; unfold Layout.sym_magicstr; omega

/-- The exec magic in rodata: "Caml1999X031" at 0x800557f0. -/
theorem exec_magic_rodata (k : Nat) (hk : k < 12) : Image.rodataByte (0x800557f0 - Image.rodataBase + k) =
    execMagicByte k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
    k = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem exec_magic_trailer (k : Nat) (hk : k < 12) :
    (WhileMinImage.initialMem[trailerSource + (k + 4)]?).getD 0 = execMagicByte k := by
  have e : trailerSource + (k + 4) = WhileMinImage.embedEnd0 - 16 + (k + 4) := by
    unfold trailerSource WhileMinImage.embedEnd0; omega
  rw [e]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
    k = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [WhileMinImage.embedTrailer0_byte_4]; rfl
  · rw [WhileMinImage.embedTrailer0_byte_5]; rfl
  · rw [WhileMinImage.embedTrailer0_byte_6]; rfl
  · rw [WhileMinImage.embedTrailer0_byte_7]; rfl
  · rw [WhileMinImage.embedTrailer0_byte_8]; rfl
  · rw [WhileMinImage.embedTrailer0_byte_9]; rfl
  · rw [WhileMinImage.embedTrailer0_byte_10]; rfl
  · rw [WhileMinImage.embedTrailer0_byte_11]; rfl
  · rw [WhileMinImage.embedTrailer0_byte_12]; rfl
  · rw [WhileMinImage.embedTrailer0_byte_13]; rfl
  · rw [WhileMinImage.embedTrailer0_byte_14]; rfl
  · rw [WhileMinImage.embedTrailer0_byte_15]; rfl

/-- caml_attempt_open's state when `open` returns descriptor 3. -/
structure AttemptOpened (H : List (Nat × Nat)) (capacity : Nat) (name : BitVec 64) (node : BitVec 64)
    (ra s0 s1 s2 s3 s4 : BitVec 64) (c : Config) : Prop where
  /-- caml_attempt_open's saved words. -/
  slots : ∀ off value, (off, value) ∈ attemptOpenSlots ra s0 s1 s2 s3 s4 →
    bytesT c.σ.mem (nativeFrameBase parameterStack 64 + off) 8 = value
  raAligned : ra.toNat % 4 = 0
  pc : PCAt 0x80004924#64 c
  regs : GHolds c.σ [(2, WhileMinElfParse.attemptStack), (10, 3#64), (8, WhileMinElfParse.trailSlot), (18, name),
    (19, WhileMinElfParse.exeNameSlot), (20, 1#64)]
  ready : RuntimeReady H capacity WhileMinElfParse.attemptStack jal_80004920_call.link c
  late : LateImage c
  words : FsWords c.σ.mem
  slot : FsSlotOne c.σ.mem node
  /-- Slot 1's name block is on the heap. -/
  nodeHeap : heapStart ≤ node.toNat ∧ node.toNat + 5 ≤ heapEnd
  kind : read4 c.σ.mem (Layout.sym_fds + 72) = [4#8, 0#8, 0#8, 0#8]
  nodeWord : read4 c.σ.mem (Layout.sym_fds + 76) = [1#8, 0#8, 0#8, 0#8]
  flags : read4 c.σ.mem (Layout.sym_fds + 88) = [0#8, 0#8, 0#8, 0#8]

/-- The trailer as caml_attempt_open leaves it: the section count's bytes
reversed, then the magic. -/
def swappedTrailer (k : Nat) : BitVec 8 :=
  (WhileMinImage.initialMem[trailerSource + (if k < 4 then 3 - k else k)]?).getD 0

theorem sb_lbu (b : BitVec 8) : sbData (lbuWord b) = b := by
  revert b; decide

/-- caml_attempt_open returned descriptor 3 for "/prog". -/
structure AttemptOk (H : List (Nat × Nat)) (capacity : Nat) (name ra s0 s1 s2 s3 s4 : BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, parameterStack), (9, s1), (10, 3#64), (20, s4), (19, s3), (18, s2), (8, s0), (1, ra)]
  ready : RuntimeReady H capacity parameterStack ra after
  trailer : ∀ k, k < 16 → (after.σ.mem[WhileMinElfParse.trailSlot.toNat + k]?).getD 0 = swappedTrailer k
  name : bytesT after.σ.mem WhileMinElfParse.exeNameSlot.toNat 8 = name
  position : bytesT after.σ.mem (Layout.sym_fds + 80) 8 = 0x24ac#64
  /-- Everything else outside the 64 bytes of stack below caml_attempt_open's
  frame and the `errno` words is the entry's. -/
  kept : ∀ x, x < WhileMinElfParse.attemptStack.toNat - 64 ∨ WhileMinElfParse.attemptStack.toNat ≤ x →
    OutW errnoWindows x → (x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x) → OutW attemptWindows x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem attempt_ok (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (name node ra s0 s1 s2 s3 s4 : BitVec 64)
    (A : AttemptOpened H capacity name node ra s0 s1 s2 s3 s4 c) :
    ∃ after, Steps c after ∧ AttemptOk H capacity name ra s0 s1 s2 s3 s4 c after := by
  have leaf := A.ready.toLeafInput
  have regs := A.regs
  -- lseek(3, -16, SEEK_END)
  obtain ⟨d1, run1, p1⟩ := (attempt_seek_call c _ 3#64 1#64 leaf
    ⟨gholds_lookup (n := 10) _ regs rfl, gholds_lookup (n := 20) _ regs rfl, trivial⟩ (by decide) (by decide)).run c
    ⟨A.pc, rfl⟩
  have keep1 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [10, 11, 12, 9, 15] ++ [1])
      (hv : gprGet c.σ n = some v) : gprGet d1.σ n = some v :=
    (p1.toEffectPost.gpr_frame (by decide) n lo hi out).trans hv
  have ready1 := A.ready.stack_log p1 (by decide) (by simp only [attemptSeekRegs, keysG]; decide) (by decide)
    (keep1 2 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ regs rfl))
    (gholds_lookup (n := 1) _ p1.regs rfl) (by decide) (show NativeFrame WhileMinElfParse.attemptStack 64 by
      constructor <;> decide) (by simp only [LogInW])
  have mem1 : d1.σ.mem = c.σ.mem := p1.memory
  obtain ⟨d2, run2, L⟩ := (lseek_file d1 H capacity WhileMinElfParse.attemptStack jal_80004940_call.link
    WhileMinElfParse.trailSlot ready1 (by constructor <;> decide)
    ⟨ready1.stack, gholds_lookup (n := 1) _ p1.regs rfl,
      keep1 8 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ regs rfl),
      gholds_lookup (n := 10) _ p1.regs rfl, gholds_lookup (n := 11) _ p1.regs rfl,
      gholds_lookup (n := 12) _ p1.regs rfl, trivial⟩
    (by rw [mem1]; exact A.words) node (by rw [mem1]; exact A.slot) (by rw [mem1]; exact A.kind)
    (by rw [mem1]; exact A.nodeWord)).run d1 ⟨p1.pc, rfl⟩
  have stackLow : heapEnd + 64 ≤ WhileMinElfParse.attemptStack.toNat := by decide
  -- memory after lseek: the position store over the entry's, away from its stack and errno
  have glob2 (x : Nat) (hx : x < heapEnd) (errno : OutW errnoWindows x)
      (outPos : x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x) :
      (d2.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [L.mem x (Or.inl (by omega)) errno, writeLog_out _ _ _ (by simp only [lseekLog, OutL, and_true]; omega), mem1]
  have pos2 : bytesT d2.σ.mem (Layout.sym_fds + 80) 8 = 0x249c#64 := by
    rw [word_observed (m := writeLog d1.σ.mem lseekLog) _ fun i hi => L.mem _ (Or.inl (by unfold Layout.sym_fds heapEnd at *; omega))
      (by simp only [OutW, errnoWindows, and_true, Layout.sym_fds]; omega)]
    exact word_writeLog_at _ _ 0 _ _ rfl trivial
  -- read(3, trail, 16)
  have keepL (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ lseekWrites)
      (hv : gprGet d1.σ n = some v) : gprGet d2.σ n = some v := (L.kept n lo hi out).trans hv
  obtain ⟨d3, run3, p3⟩ := (attempt_read_call d2 jal_80004940_call.link 0x249c#64 3#64 WhileMinElfParse.trailSlot
    L.ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ L.regs rfl, gholds_lookup (n := 8) _ L.regs rfl,
      keepL 9 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ p1.regs rfl), trivial⟩
    (by decide)).run d2 ⟨L.pc, rfl⟩
  have ready3 := L.ready.stack_log p3 (by decide) (by simp only [attemptReadRegs, keysG]; decide) (by decide)
    ((p3.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans L.ready.stack)
    (gholds_lookup (n := 1) _ p3.regs rfl) (by decide) (show NativeFrame WhileMinElfParse.attemptStack 64 by
      constructor <;> decide) (by simp only [LogInW])
  have mem3 : d3.σ.mem = d2.σ.mem := p3.memory
  have fdsG (x : Nat) (lo : Layout.sym_fds ≤ x) (hi : x < Layout.sym_fds + 80) :
      (d3.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [mem3]; exact glob2 x (by unfold Layout.sym_fds heapEnd at *; omega)
      (by simp only [OutW, errnoWindows, and_true, Layout.sym_fds] at *; omega) (Or.inl hi)
  obtain ⟨d4, run4, R⟩ := (read_file d3 H capacity WhileMinElfParse.attemptStack jal_80004958_call.link
    WhileMinElfParse.trailSlot WhileMinElfParse.trailSlot ready3 (by constructor <;> decide)
    ⟨ready3.stack, gholds_lookup (n := 1) _ p3.regs rfl, gholds_lookup (n := 8) _ p3.regs rfl,
      gholds_lookup (n := 10) _ p3.regs rfl, gholds_lookup (n := 11) _ p3.regs rfl,
      gholds_lookup (n := 12) _ p3.regs rfl, trivial⟩
    (by decide) (by decide) (by decide)
    (A.words.transport fun x hx => by
      rw [mem3]; exact glob2 x (by have := hx.htif.bounds; unfold Layout.sym_files heapEnd at *; omega) hx.htif.out_errno
        (by rcases hx with ⟨_, h⟩ | ⟨_, h⟩ <;> simp only [Layout.sym_fs_ready, Layout.sym_fds] at * <;> omega))
    node (A.slot.transport (fun x lo hi => by
        rw [mem3]; exact glob2 x (by unfold slotOne Layout.sym_files heapEnd at *; omega)
          (HtifByte.out_errno (slotOne_htif lo hi)) (by unfold slotOne Layout.sym_files Layout.sym_fds at *; omega))
      (fun j hj => by
        have := A.nodeHeap
        rw [mem3]; exact glob2 _ (by omega) (by simp only [OutW, errnoWindows, and_true]; unfold heapStart at *; omega)
          (Or.inr (by unfold heapStart Layout.sym_fds at *; omega))))
    (by rw [read4_observed (m := c.σ.mem) _ fun k hk => fdsG _ (by omega) (by omega)]; exact A.kind)
    (by rw [read4_observed (m := c.σ.mem) _ fun k hk => fdsG _ (by omega) (by omega)]; exact A.nodeWord)
    (by rw [read4_observed (m := c.σ.mem) _ fun k hk => by
          rw [mem3]; exact glob2 _ (by unfold Layout.sym_fds heapEnd; omega)
            (by simp only [OutW, errnoWindows, and_true, Layout.sym_fds]; omega) (Or.inr (by omega))]
        exact A.flags)
    (by rw [mem3]; exact pos2)).run d3 ⟨p3.pc, rfl⟩
  -- the trailer, as read
  let T : Nat → BitVec 8 := fun k => (WhileMinImage.initialMem[trailerSource + k]?).getD 0
  have hsp : WhileMinElfParse.attemptStack.toNat = 0x87ffff40 := by decide
  have trail4 (k : Nat) (hk : k < 16) :
      (d4.σ.mem[WhileMinElfParse.trailSlot.toNat + k]?).getD 0 = T k := by
    rw [R.trailer k hk, mem3, L.mem _ (Or.inl (by rw [hsp]; unfold trailerSource; omega))
        (by simp only [OutW, errnoWindows, and_true, trailerSource]; omega),
      writeLog_out _ _ _ (by simp only [lseekLog, OutL, and_true, trailerSource, Layout.sym_fds]; omega), mem1]
    exact A.late.embed.byte _ ⟨by unfold trailerSource heapEnd; omega, by
      unfold trailerSource embedLimit Layout.sym_stack_top Layout.sym_stack_size; omega⟩
  have windowReady {d e : Config} {sp ra ra' writes log pc value regs} (ready : RuntimeReady H capacity sp ra d)
      (post : WriteRegistersPost writes log d pc value regs e) (keys : KeysOK writes)
      (cover : ∀ n ∈ writes, n ∈ keysG regs) (gp : 3 ∉ writes) (stack : gprGet e.σ 2 = some sp)
      (link : gprGet e.σ 1 = some ra') (aligned : ra'.toNat % 4 = 0) (inside : LogInW attemptWindows log) :
      RuntimeReady H capacity sp ra' e :=
    ready.window_log post keys cover gp stack link aligned inside attemptWindows_out_pins
      ⟨Or.inl (by decide), Or.inl (by decide), Or.inl (by decide), trivial⟩
      ⟨Or.inl (by decide), Or.inl (by decide), Or.inl (by decide), trivial⟩ (fun a foot => attemptWindows_out_foot foot)
  -- fix the section count's byte order
  obtain ⟨d5, run5, p5⟩ := (attempt_swap d4 jal_80004958_call.link T R.ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ R.regs rfl, gholds_lookup (n := 8) _ R.regs rfl, trivial⟩ trail4).run d4 ⟨R.pc, rfl⟩
  have ready5 := windowReady R.ready p5 (by decide) (by simp only [trailerSwapRegs, keysG]; decide) (by decide)
    ((p5.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans R.ready.stack)
    ((p5.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans R.ready.raReg) R.ready.aligned
    (by simp only [trailerSwapLog, LogInW, InsideW, attemptWindows]; refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> omega)
  -- copy the magic to magicstr
  obtain ⟨d6, run6, p6⟩ := (magicPtr d5 jal_80004958_call.link T ready5.toLeafInput
    ⟨gholds_lookup (n := 10) _ p5.regs rfl, trivial⟩).run d5 ⟨p5.pc, rfl⟩
  have ready6 := ready5.stack_log p6 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p6.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready5.stack)
    ((p6.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready5.raReg) R.ready.aligned
    (show NativeFrame WhileMinElfParse.attemptStack 64 by constructor <;> decide) (by simp only [magicPtrLog, LogInW])
  have keep6 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [15])
      (hv : gprGet d5.σ n = some v) : gprGet d6.σ n = some v :=
    (p6.toEffectPost.gpr_frame (by decide) n lo hi out).trans hv
  obtain ⟨d7, run7, p7⟩ := (magicA d6 jal_80004958_call.link T ready6.toLeafInput
    ⟨gholds_lookup (n := 15) _ p6.regs rfl, gholds_lookup (n := 10) _ p6.regs rfl,
      keep6 30 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 30) _ p5.regs rfl),
      keep6 29 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 29) _ p5.regs rfl),
      keep6 28 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 28) _ p5.regs rfl), trivial⟩).run d6
    ⟨p6.pc, rfl⟩
  have ready7 := windowReady ready6 p7 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p7.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready6.stack)
    ((p7.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready6.raReg) R.ready.aligned
    (by simp only [magicALog, LogInW, InsideW, attemptWindows]; refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> simp only [Layout.sym_magicstr] <;> omega)
  have keep7 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [15])
      (hv : gprGet d5.σ n = some v) : gprGet d7.σ n = some v :=
    (p7.toEffectPost.gpr_frame (by decide) n lo hi (by simp)).trans (keep6 n v lo hi out hv)
  obtain ⟨d8, run8, p8⟩ := (magicB d7 jal_80004958_call.link T ready7.toLeafInput
    ⟨gholds_lookup (n := 15) _ p7.regs rfl, gholds_lookup (n := 10) _ p7.regs rfl,
      keep7 6 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 6) _ p5.regs rfl),
      keep7 17 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 17) _ p5.regs rfl),
      keep7 16 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 16) _ p5.regs rfl),
      keep7 11 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 11) _ p5.regs rfl),
      keep7 12 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 12) _ p5.regs rfl),
      keep7 13 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 13) _ p5.regs rfl), trivial⟩).run d7
    ⟨p7.pc, rfl⟩
  have ready8 := windowReady ready7 p8 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p8.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready7.stack)
    ((p8.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready7.raReg) R.ready.aligned
    (by simp only [magicBLog, LogInW, InsideW, attemptWindows]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> simp only [Layout.sym_magicstr] <;> omega)
  have b15 : (d8.σ.mem[WhileMinElfParse.trailSlot.toNat + 15]?).getD 0 = T 15 := by
    have trail : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
    rw [p8.memory, writeLog_out _ _ _ (by simp only [magicBLog, OutL, and_true, trail, Layout.sym_magicstr]; omega),
      p7.memory, writeLog_out _ _ _ (by simp only [magicALog, OutL, and_true, trail, Layout.sym_magicstr]; omega),
      p6.memory, show writeLog d5.σ.mem (magicPtrLog T) = d5.σ.mem from rfl, p5.memory,
      writeLog_out _ _ _ (by simp only [trailerSwapLog, OutL, and_true]; omega)]
    exact trail4 15 (by decide)
  have keep8 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [15])
      (hv : gprGet d5.σ n = some v) : gprGet d8.σ n = some v :=
    (p8.toEffectPost.gpr_frame (by decide) n lo hi (by simp)).trans (keep7 n v lo hi out hv)
  obtain ⟨d9, run9, p9⟩ := (magicC d8 jal_80004958_call.link T ready8.toLeafInput
    ⟨(p8.toEffectPost.gpr_frame (by decide) 15 (by decide) (by decide) (by simp)).trans
        (gholds_lookup (n := 15) _ p7.regs rfl),
      keep8 14 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 14) _ p5.regs rfl),
      keep8 8 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ p5.regs rfl), trivial⟩ b15).run d8
    ⟨p8.pc, rfl⟩
  have ready9 := windowReady ready8 p9 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p9.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready8.stack)
    ((p9.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready8.raReg) R.ready.aligned
    (by simp only [magicCLog, LogInW, InsideW, attemptWindows]
        refine ⟨?_, ?_, trivial⟩ <;> simp only [Layout.sym_magicstr] <;> omega)
  obtain ⟨d10, run10, p10⟩ := (magicNul d9 jal_80004958_call.link T ready9.toLeafInput
    ⟨gholds_lookup (n := 10) _ p9.regs rfl, trivial⟩).run d9 ⟨p9.pc, rfl⟩
  have ready10 := windowReady ready9 p10 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p10.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready9.stack)
    ((p10.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready9.raReg) R.ready.aligned
    (by simp only [magicNulLog, LogInW, InsideW, attemptWindows]
        refine ⟨?_, trivial⟩; simp only [Layout.sym_magicstr]; omega)
  -- memory away from the stack, errno, the position and caml_attempt_open's windows: the entry's
  have toCs (x : Nat) (stack : x < WhileMinElfParse.attemptStack.toNat - 64 ∨ WhileMinElfParse.attemptStack.toNat ≤ x)
      (errno : OutW errnoWindows x)
      (fdsOut : x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x) (win : OutW attemptWindows x) :
      (d10.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    have trail : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
    have exe : WhileMinElfParse.exeNameSlot.toNat = 0x87ffffa0 := by decide
    simp only [OutW, attemptWindows, trail, exe, and_true] at win
    rw [p10.memory, writeLog_out _ _ _ (by simp only [magicNulLog, OutL, and_true, Layout.sym_magicstr] at *; omega),
      p9.memory, writeLog_out _ _ _ (by simp only [magicCLog, OutL, and_true, Layout.sym_magicstr] at *; omega),
      p8.memory, writeLog_out _ _ _ (by simp only [magicBLog, OutL, and_true, Layout.sym_magicstr] at *; omega),
      p7.memory, writeLog_out _ _ _ (by simp only [magicALog, OutL, and_true, Layout.sym_magicstr] at *; omega),
      p6.memory, show writeLog d5.σ.mem (magicPtrLog T) = d5.σ.mem from rfl, p5.memory,
      writeLog_out _ _ _ (by simp only [trailerSwapLog, OutL, and_true, trail] at *; omega),
      R.mem x stack errno (by rw [trail]; omega),
      writeLog_out _ _ _ (by simp only [readLog, OutL, and_true]; omega), mem3,
      L.mem x stack errno, writeLog_out _ _ _ (by simp only [lseekLog, OutL, and_true]; omega), mem1]
  have toC (x : Nat) (hx : x < heapEnd) (errno : OutW errnoWindows x)
      (fdsOut : x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x) (win : OutW attemptWindows x) :
      (d10.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 :=
    toCs x (Or.inl (by rw [hsp]; unfold heapEnd at hx; omega)) errno fdsOut win
  -- print_magic is clear
  obtain ⟨d11, run11, p11⟩ := (attempt_quiet d10 jal_80004958_call.link (WhileMinElfParse.trailSlot + 4#64)
    ready10.toLeafInput ⟨gholds_lookup (n := 10) _ p10.regs rfl, trivial⟩ (by
      have pm (i : Nat) (hi : i < 4) : (d10.σ.mem[Layout.sym_print_magic + i]?).getD 0 = 0#8 := by
        rw [toC _ (by unfold Layout.sym_print_magic heapEnd; omega)
          (by simp only [OutW, errnoWindows, and_true, Layout.sym_print_magic]; omega)
          (Or.inl (by unfold Layout.sym_print_magic Layout.sym_fds; omega))
          (by have : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
              have : WhileMinElfParse.exeNameSlot.toNat = 0x87ffffa0 := by decide
              simp only [OutW, attemptWindows, and_true, Layout.sym_print_magic, Layout.sym_magicstr, *]
              omega)]
        have := A.late.printFlags (i + 4) (by omega)
        rwa [show Layout.sym_print_config + (i + 4) = Layout.sym_print_magic + i by
          unfold Layout.sym_print_config Layout.sym_print_magic; omega] at this
      unfold read4
      rw [show Layout.sym_print_magic = Layout.sym_print_magic + 0 from rfl, pm 0 (by decide), pm 1 (by decide),
        pm 2 (by decide), pm 3 (by decide)])).run d10 ⟨p10.pc, rfl⟩
  have ready11 := ready10.stack_log p11 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p11.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready10.stack)
    ((p11.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready10.raReg)
    R.ready.aligned (show NativeFrame WhileMinElfParse.attemptStack 64 by constructor <;> decide)
    (by simp only [LogInW])
  -- strncmp(trail + 4, EXEC_MAGIC, 12) = 0
  obtain ⟨d12, run12, p12⟩ := (attempt_magic_call d11 jal_80004958_call.link (WhileMinElfParse.trailSlot + 4#64)
    ready11.toLeafInput ⟨gholds_lookup (n := 10) _ p11.regs rfl, trivial⟩).run d11 ⟨p11.pc, rfl⟩
  have ready12 := ready11.stack_log p12 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p12.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready11.stack)
    (gholds_lookup (n := 1) _ p12.regs rfl) (by decide)
    (show NativeFrame WhileMinElfParse.attemptStack 64 by constructor <;> decide) (by simp only [LogInW])
  have mem12 : d12.σ.mem = d10.σ.mem := p12.memory.trans p11.memory
  have trailNat : (WhileMinElfParse.trailSlot + 4#64).toNat = WhileMinElfParse.trailSlot.toNat + 4 := by decide
  have magicL (k : Nat) (hk : k ≤ 11) :
      (d12.σ.mem[(WhileMinElfParse.trailSlot + 4#64).toNat + k]?).getD 0 = execMagicByte k := by
    have trail : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
    rw [mem12, trailNat, p10.memory, writeLog_out _ _ _ (by simp only [magicNulLog, OutL, and_true, trail, Layout.sym_magicstr]; omega),
      p9.memory, writeLog_out _ _ _ (by simp only [magicCLog, OutL, and_true, trail, Layout.sym_magicstr]; omega),
      p8.memory, writeLog_out _ _ _ (by simp only [magicBLog, OutL, and_true, trail, Layout.sym_magicstr]; omega),
      p7.memory, writeLog_out _ _ _ (by simp only [magicALog, OutL, and_true, trail, Layout.sym_magicstr]; omega),
      p6.memory, show writeLog d5.σ.mem (magicPtrLog T) = d5.σ.mem from rfl, p5.memory,
      writeLog_out _ _ _ (by simp only [trailerSwapLog, OutL, and_true, trail]; omega),
      show WhileMinElfParse.trailSlot.toNat + 4 + k = WhileMinElfParse.trailSlot.toNat + (k + 4) by omega,
      trail4 (k + 4) (by omega)]
    exact exec_magic_trailer k (by omega)
  have magicR (k : Nat) (hk : k ≤ 11) : (d12.σ.mem[(0x800557f0#64).toNat + k]?).getD 0 = execMagicByte k := by
    rw [mem12, show (0x800557f0#64).toNat = 0x800557f0 by decide, toC _ (by unfold heapEnd; omega)
      (by simp only [OutW, errnoWindows, and_true]; omega) (Or.inl (by unfold Layout.sym_fds; omega))
      (by have : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
          have : WhileMinElfParse.exeNameSlot.toNat = 0x87ffffa0 := by decide
          simp only [OutW, attemptWindows, and_true, Layout.sym_magicstr, *]; omega),
      show 0x800557f0 + k = Image.rodataBase + (0x800557f0 - Image.rodataBase + k) by unfold Image.rodataBase; omega,
      A.ready.image.rodata _ (by unfold Image.rodataBase Image.rodataSize; omega), Option.getD_some]
    exact exec_magic_rodata k (by omega)
  obtain ⟨d13, run13, p13⟩ := (strncmp_equal d12 (WhileMinElfParse.trailSlot + 4#64) 0x800557f0#64
    jal_80004a10_call.link 11 execMagicByte ready12.toLeafInput
    { left := ⟨by rw [trailNat]; decide, by rw [trailNat]; decide, Or.inr (by rw [trailNat]; decide)⟩
      right := ⟨by decide, by decide, Or.inl (by decide)⟩
      leftByte := magicL
      rightByte := magicR
      nonzero := fun k hk => by
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
          k = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide }
    ⟨gholds_lookup (n := 10) _ p12.regs rfl, gholds_lookup (n := 11) _ p12.regs rfl,
      gholds_lookup (n := 12) _ p12.regs rfl, trivial⟩ (by decide)).run d12 ⟨p12.pc, rfl⟩
  have ready13 := ready12.stack_log p13 (by decide) (by simp only [strncmpEqualRegs, keysG]; decide) (by decide)
    ((p13.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready12.stack)
    (gholds_lookup (n := 1) _ p13.regs rfl) (by decide)
    (show NativeFrame WhileMinElfParse.attemptStack 64 by constructor <;> decide) (by simp only [LogInW])
  -- registers kept since the entry
  have after1 (n : Nat) (v : BitVec 64) (hn : n ∈ [18, 19, 20, 9]) (hv : gprGet d1.σ n = some v) :
      gprGet d13.σ n = some v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    have lo : 1 ≤ n := by omega
    have hi : n ≤ 31 := by omega
    exact (p13.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((p12.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((p11.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((p10.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((p9.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((p8.toEffectPost.gpr_frame (by decide) n lo hi (by simp)).trans
      ((p7.toEffectPost.gpr_frame (by decide) n lo hi (by simp)).trans
      ((p6.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((p5.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((R.kept n lo hi (by simp [readWrites]; omega)).trans
      ((p3.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((L.kept n lo hi (by simp [lseekWrites]; omega)).trans hv)))))))))))
  have since (n : Nat) (v : BitVec 64) (hn : n ∈ [18, 19, 20]) (hv : gprGet c.σ n = some v) :
      gprGet d13.σ n = some v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    exact after1 n v (by simp; omega) (keep1 n v (by omega) (by omega) (by simp; omega) hv)
  -- *name = truename
  obtain ⟨d14, run14, p14⟩ := (attempt_name_store d13 jal_80004a10_call.link name ready13.toLeafInput
    ⟨gholds_lookup (n := 10) _ p13.regs rfl, since 18 _ (by decide) (gholds_lookup (n := 18) _ regs rfl),
      since 19 _ (by decide) (gholds_lookup (n := 19) _ regs rfl), trivial⟩).run d13 ⟨p13.pc, rfl⟩
  have ready14 := windowReady ready13 p14 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p14.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready13.stack)
    ((p14.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready13.raReg)
    R.ready.aligned
    (by have : WhileMinElfParse.exeNameSlot.toNat = 0x87ffffa0 := by decide
        simp only [LogInW, InsideW, attemptWindows, this]; refine ⟨?_, trivial⟩; omega)
  have mem14 (x : Nat) (out : x < WhileMinElfParse.exeNameSlot.toNat ∨ WhileMinElfParse.exeNameSlot.toNat + 8 ≤ x) :
      (d14.σ.mem[x]?).getD 0 = (d10.σ.mem[x]?).getD 0 := by
    rw [p14.memory, writeLog_out _ _ _ (by simp only [OutL, and_true]; omega), p13.memory, mem12]
    rfl
  -- restore and return descriptor 3
  have base : nativeFrameBase parameterStack 64 = 0x87ffff40 := by decide
  obtain ⟨d15, run15, p15⟩ := (attempt_open_return d14 parameterStack ra s0 s1 s2 s3 s4 3#64 jal_80004a10_call.link
    ready14.toLeafInput (by constructor <;> decide)
    ⟨(p14.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready13.stack,
      (p14.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
        (after1 9 _ (by decide) (gholds_lookup (n := 9) _ p1.regs rfl)), trivial⟩
    (fun off value member => by
      have range : 16 ≤ off ∧ off + 8 ≤ 64 := by
        simp only [attemptOpenSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega
      have exe : WhileMinElfParse.exeNameSlot.toNat = 0x87ffffa0 := by decide
      have trail : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
      have same (i : Nat) (hi : i < 8) :
          (d14.σ.mem[nativeFrameBase parameterStack 64 + off + i]?).getD 0 =
            (c.σ.mem[nativeFrameBase parameterStack 64 + off + i]?).getD 0 := by
        rw [mem14 _ (Or.inl (by rw [base]; omega)),
          toCs _ (Or.inr (by rw [hsp, base]; omega)) (by simp only [OutW, errnoWindows, and_true]; rw [base]; omega)
            (Or.inr (by rw [base]; unfold Layout.sym_fds; omega))
            (by simp only [OutW, attemptWindows, and_true, Layout.sym_magicstr, exe, trail]; rw [base]; omega)]
      rw [word_observed (m := c.σ.mem) _ same]
      exact A.slots off value member)
    A.raAligned).run d14 ⟨p14.pc, rfl⟩
  have mem15 : d15.σ.mem = d14.σ.mem := p15.memory
  refine ⟨d15, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
    (run9.trans (run10.trans (run11.trans (run12.trans (run13.trans (run14.trans run15))))))))))))), {
    pc := p15.pc
    regs := p15.regs
    ready := ready14.stack_log p15 (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ p15.regs rfl) (gholds_lookup (n := 1) _ p15.regs rfl) A.raAligned
      (show NativeFrame WhileMinElfParse.attemptStack 64 by constructor <;> decide) (by simp only [LogInW])
    trailer := fun k hk => ?_
    name := ?_
    position := ?_
    kept := fun x stack errno fdsOut win => ?_ }⟩
  · have trail : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
    have exe : WhileMinElfParse.exeNameSlot.toNat = 0x87ffffa0 := by decide
    rw [mem15, mem14 _ (Or.inr (by omega)), p10.memory,
      writeLog_out _ _ _ (by simp only [magicNulLog, OutL, and_true, trail, Layout.sym_magicstr]; omega),
      p9.memory, writeLog_out _ _ _ (by simp only [magicCLog, OutL, and_true, trail, Layout.sym_magicstr]; omega),
      p8.memory, writeLog_out _ _ _ (by simp only [magicBLog, OutL, and_true, trail, Layout.sym_magicstr]; omega),
      p7.memory, writeLog_out _ _ _ (by simp only [magicALog, OutL, and_true, trail, Layout.sym_magicstr]; omega),
      p6.memory, show writeLog d5.σ.mem (magicPtrLog T) = d5.σ.mem from rfl, p5.memory]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | rfl | rfl | big
    · rw [byte_writeLog_at _ _ 0 _ _ rfl (by simp only [trailerSwapLog, List.drop, OutL, and_true]; omega), sb_lbu]; rfl
    · rw [byte_writeLog_at _ _ 3 _ _ rfl (by simp only [trailerSwapLog, List.drop, OutL]), sb_lbu]; rfl
    · rw [byte_writeLog_at _ _ 2 _ _ rfl (by simp only [trailerSwapLog, List.drop, OutL, and_true]; omega), sb_lbu]; rfl
    · rw [byte_writeLog_at _ _ 1 _ _ rfl (by simp only [trailerSwapLog, List.drop, OutL, and_true]; omega), sb_lbu]; rfl
    · rw [writeLog_out _ _ _ (by simp only [trailerSwapLog, OutL, and_true, trail]; omega), trail4 k hk]
      simp only [swappedTrailer, show ¬ k < 4 by omega, ite_false]
      rfl
  · rw [mem15, p14.memory]
    exact word_writeLog_at _ _ 0 _ _ rfl trivial
  · rw [mem15, word_observed (m := d10.σ.mem) _ fun i hi => mem14 _ (Or.inl (by
        have : WhileMinElfParse.exeNameSlot.toNat = 0x87ffffa0 := by decide
        unfold Layout.sym_fds; omega)),
      word_observed (m := writeLog d3.σ.mem readLog) _ fun i hi => by
        have trail : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
        rw [p10.memory, writeLog_out _ _ _ (by simp only [magicNulLog, OutL, and_true, Layout.sym_magicstr, Layout.sym_fds]; omega),
          p9.memory, writeLog_out _ _ _ (by simp only [magicCLog, OutL, and_true, Layout.sym_magicstr, Layout.sym_fds]; omega),
          p8.memory, writeLog_out _ _ _ (by simp only [magicBLog, OutL, and_true, Layout.sym_magicstr, Layout.sym_fds]; omega),
          p7.memory, writeLog_out _ _ _ (by simp only [magicALog, OutL, and_true, Layout.sym_magicstr, Layout.sym_fds]; omega),
          p6.memory, show writeLog d5.σ.mem (magicPtrLog T) = d5.σ.mem from rfl, p5.memory,
          writeLog_out _ _ _ (by simp only [trailerSwapLog, OutL, and_true, trail, Layout.sym_fds]; omega),
          R.mem _ (Or.inl (by rw [hsp]; unfold Layout.sym_fds; omega)) (by simp only [OutW, errnoWindows, and_true, Layout.sym_fds]; omega)
            (Or.inl (by rw [trail]; unfold Layout.sym_fds; omega))]]
    exact word_writeLog_at _ _ 0 _ _ rfl trivial
  · have exe : WhileMinElfParse.exeNameSlot.toNat = 0x87ffffa0 := by decide
    have w := win
    simp only [OutW, attemptWindows, exe, and_true] at w
    rw [mem15, mem14 x (by omega)]
    exact toCs x stack errno fdsOut win
end OCaml.Vm.Boot.Startup
