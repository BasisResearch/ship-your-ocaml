import OCaml.Vm.Boot.Startup.ReadFileSteps
import OCaml.Vm.Boot.Startup.ReentWrappers
import OCaml.Vm.Boot.Startup.ReadREntryCallInterface
import OCaml.Vm.Boot.Startup.MemcpyFresh
import OCaml.Vm.Boot.Startup.LseekFile
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable VsaIris.Memcpy

/-! `read(3, buf, n)` on "/prog" at position `p`:
newlib's `read` → `_read_r` → htif.c's `_read`, which copies the trailer
out of the embedded file with `memcpy` and advances the position. -/

/-- The registers `read` may change besides the ones it restores. -/
def readWrites : List Nat := [1, 2, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- The position store. -/
abbrev readLog (p : BitVec 64) (count : Nat) : List WEntry :=
  [(Layout.sym_fds + 80, 8, p + BitVec.ofNat 64 count)]

/-- Where the file's last 16 bytes are: slot 1's data plus 0x249c. -/
abbrev trailerSource : Nat := 0x8680252c

/-- `read(3, buf, n)` returned `count` with that many of the file's bytes from
position `p` in `buf`. -/
structure ReadFile (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 buf p : BitVec 64) (count : Nat)
    (before after : Config) :
    Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (8, s0), (1, ra), (10, BitVec.ofNat 64 count)]
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ readWrites → gprGet after.σ n = gprGet before.σ n
  ready : RuntimeReady H capacity sp ra after
  trailer : ∀ k, k < count → (after.σ.mem[buf.toNat + k]?).getD 0 =
    (before.σ.mem[(0x86800090#64 + p).toNat + k]?).getD 0
  /-- Outside its 64 bytes of stack, `buf` and the `errno` words, memory is
  the position store over the caller's. -/
  mem : ∀ x, x < sp.toNat - 64 ∨ sp.toNat ≤ x → OutW errnoWindows x → (x < buf.toNat ∨ buf.toNat + count ≤ x) →
    (after.σ.mem[x]?).getD 0 = ((writeLog before.σ.mem (readLog p count))[x]?).getD 0

theorem read_file (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 buf p n : BitVec 64) (count : Nat)
    (ready : RuntimeReady H capacity sp ra c) (frame : NativeFrame sp (16 + 48))
    (regs : GHolds c.σ [(2, sp), (1, ra), (8, s0), (10, 3#64), (11, buf), (12, n)])
    (srcEmbed : heapEnd ≤ (0x86800090#64 + p).toNat) (deep : (0x86800090#64 + p).toNat + count ≤ sp.toNat - 64)
    (bufAbove : sp.toNat ≤ buf.toNat) (bufTop : buf.toNat + count ≤ 0x100000000)
    (fs : FsWords c.σ.mem) (node : BitVec 64) (slot : FsSlotOne c.σ.mem node)
    (kind : read4 c.σ.mem (Layout.sym_fds + 72) = [4#8, 0#8, 0#8, 0#8])
    (nodeWord : read4 c.σ.mem (Layout.sym_fds + 76) = [1#8, 0#8, 0#8, 0#8])
    (flags : read4 c.σ.mem (Layout.sym_fds + 88) = [0#8, 0#8, 0#8, 0#8])
    (pos : bytesT c.σ.mem (Layout.sym_fds + 80) 8 = p) (inFile : guardB bop.BLTU p 0x24ac#64 = true)
    (clamp : (guardB bop.BLTU n (0x24ac#64 - p) = false ∧ BitVec.ofNat 64 count = 0x24ac#64 - p) ∨
      (guardB bop.BLTU n (0x24ac#64 - p) = true ∧ BitVec.ofNat 64 count = n))
    (ok : BitVec.ofNat 64 count ≠ -1#64) :
    FnSummary 0x800425e4#64 (fun d => d = c) (ReadFile H capacity sp ra s0 buf p count c) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have f1 : NativeFrame sp 16 := frame.resize (by decide) (by decide)
  have f2 : NativeFrame (nativeStack sp 16) 48 := frame.nested (front := 16) (by decide)
  have lower : heapEnd + 64 ≤ sp.toNat := frame.lower
  have h1 : (nativeStack sp 16).toNat = sp.toNat - 16 := by rw [f1.stack_nat]; rfl
  -- read: load _impure_ptr, tail-jump to _read_r
  obtain ⟨d1, run1, p1⟩ := (lib_read c 3#64 buf n ra ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ regs rfl, gholds_lookup (n := 11) _ regs rfl, gholds_lookup (n := 12) _ regs rfl,
      trivial⟩).run c ⟨pc, rfl⟩
  have keep1 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [14, 10, 13, 12, 11])
      (hv : gprGet c.σ n = some v) : gprGet d1.σ n = some v :=
    (p1.toEffectPost.gpr_frame (by decide) n lo hi out).trans hv
  have ready1 := ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    (keep1 2 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ regs rfl))
    (keep1 1 _ (by decide) (by decide) (by decide) ready.raReg) ready.aligned f1 (by simp only [LogInW])
  -- _read_r: save, clear errno, call _read
  obtain ⟨d2, run2, p2⟩ := (read_r_entry d1 sp ra s0 (getenvReent c) 3#64 buf n ready1.toLeafInput f1
    ⟨keep1 2 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ regs rfl), ready1.raReg,
      keep1 8 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ regs rfl),
      gholds_lookup (n := 10) _ p1.regs rfl, gholds_lookup (n := 11) _ p1.regs rfl,
      gholds_lookup (n := 12) _ p1.regs rfl, gholds_lookup (n := 13) _ p1.regs rfl, trivial⟩).run d1 ⟨p1.pc, rfl⟩
  have ready2 := ready1.errno_log p2 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p2.regs rfl) (gholds_lookup (n := 1) _ p2.regs rfl) ready.aligned f1
    (openRLog_inside f1)
  obtain ⟨d3, run3, p3⟩ := (call_registers_summary jal_800423b4_call_shape jal_800423b4_call_decode d2
    (jal_800423b4_call_pins ready2.image) p2.good ready2.image p2.tick p2.minstret
    [(2, nativeStack sp 16), (10, 3#64), (11, buf), (12, n), (8, getenvReent c)]
    ⟨gholds_lookup (n := 2) _ p2.regs rfl, gholds_lookup (n := 10) _ p2.regs rfl,
      gholds_lookup (n := 11) _ p2.regs rfl, gholds_lookup (n := 12) _ p2.regs rfl,
      gholds_lookup (n := 8) _ p2.regs rfl, trivial⟩
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl).run d2 ⟨p2.pc, rfl⟩
  have p3' : WriteRegistersPost [1] [] d2 jal_800423b4_call.target 3#64
      ((1, jal_800423b4_call.link) :: [(2, nativeStack sp 16), (10, 3#64), (11, buf), (12, n),
        (8, getenvReent c)]) d3 := p3
  have ready3 := ready2.stack_log p3' (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p3'.regs rfl) (gholds_lookup (n := 1) _ p3'.regs rfl) (by decide) f2
    (by simp only [LogInW])
  -- memory up to _read's entry
  have mem3 (x : Nat) (stack : x < sp.toNat - 16 ∨ sp.toNat ≤ x) (errno : OutW errnoWindows x) :
      (d3.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p3'.memory, show writeLog d2.σ.mem [] = d2.σ.mem from rfl, p2.memory,
      frameOn_writeLog _ _ _ (openRLog_inside f1) x ⟨by simp only [nativeFrameBase] at *; omega, errno⟩, p1.memory]
    rfl
  have glob3 (x : Nat) (hi : x < heapEnd) (errno : OutW errnoWindows x) :
      (d3.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := mem3 x (Or.inl (by omega)) errno
  -- _read: fs_ready set, save s0 and ra
  obtain ⟨d4, run4, p4⟩ := (htif_read_entry d3 (nativeStack sp 16) jal_800423b4_call.link (getenvReent c) 3#64 buf
    n ready3.toLeafInput f2
    ⟨gholds_lookup (n := 2) _ p3'.regs rfl, gholds_lookup (n := 1) _ p3'.regs rfl,
      gholds_lookup (n := 8) _ p3'.regs rfl, gholds_lookup (n := 10) _ p3'.regs rfl,
      gholds_lookup (n := 11) _ p3'.regs rfl, gholds_lookup (n := 12) _ p3'.regs rfl, trivial⟩
    (by
      rw [read4_observed (m := c.σ.mem) _ fun k hk => glob3 _ (by unfold Layout.sym_fs_ready heapEnd; omega)
        (by simp only [OutW, errnoWindows, and_true, Layout.sym_fs_ready]; omega)]
      exact fs.ready)).run d3 ⟨p3'.pc, rfl⟩
  have ready4 := ready3.stack_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p4.regs rfl) (gholds_lookup (n := 1) _ p4.regs rfl) (by decide) f2
    (htifReadLog_inside f2)
  have glob4 (x : Nat) (hi : x < heapEnd) (errno : OutW errnoWindows x) :
      (d4.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p4.memory, frameOn_writeLog _ _ _ (htifReadLog_inside f2) x ⟨by
      simp only [nativeFrameBase, h1] at *; omega, trivial⟩]
    exact glob3 x hi errno
  have slotG (x : Nat) (lo : slotOne ≤ x) (hi : x < slotOne + 56) :
      (d4.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 :=
    glob4 x (by unfold slotOne Layout.sym_files heapEnd at *; omega) (HtifByte.out_errno (slotOne_htif lo hi))
  have fdsG (x : Nat) (lo : Layout.sym_fds ≤ x) (hi : x < Layout.sym_fds + 24 * 32) :
      (d4.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 :=
    glob4 x (by unfold Layout.sym_fds heapEnd at *; omega) (by
      simp only [OutW, errnoWindows, and_true, Layout.sym_fds] at *; omega)
  -- _read: the descriptor checks and the clamp
  obtain ⟨d5f, run5f, p5f⟩ := (htif_read_front d4 (nativeStack sp 16) jal_800423b4_call.link buf p n ready4.toLeafInput f2
    ⟨gholds_lookup (n := 2) _ p4.regs rfl, gholds_lookup (n := 8) _ p4.regs rfl,
      gholds_lookup (n := 10) _ p4.regs rfl, gholds_lookup (n := 11) _ p4.regs rfl,
      gholds_lookup (n := 12) _ p4.regs rfl, trivial⟩
    (by rw [read4_observed (m := c.σ.mem) _ fun k hk => fdsG _ (by omega) (by omega)]; exact kind)
    (by rw [read4_observed (m := c.σ.mem) _ fun k hk => fdsG _ (by omega) (by omega)]; exact flags)
    (by rw [read4_observed (m := c.σ.mem) _ fun k hk => fdsG _ (by omega) (by omega)]; exact nodeWord)
    (by rw [slotG _ (by unfold slotOne; omega) (by unfold slotOne; omega)]; exact slot.dirByte)
    (by rw [word_observed (m := c.σ.mem) _ fun i hi => fdsG _ (by omega) (by omega)]; exact pos)
    (by
      rw [word_observed (m := c.σ.mem) _ fun i hi => slotG _ (by unfold slotOne; omega)
        (by unfold slotOne; omega)]
      exact slot.size) inFile).run d4 ⟨p4.pc, rfl⟩
  have ready5f := ready4.stack_log p5f (by decide) (by simp only [htifReadFrontRegs, keysG]; decide) (by decide)
    ((p5f.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready4.stack)
    ((p5f.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready4.raReg) (by decide) f2
    (by simp only [LogInW])
  obtain ⟨d5, run5c, p5⟩ := (htif_read_clamp d5f (nativeStack sp 16) jal_800423b4_call.link buf p n
    (BitVec.ofNat 64 count) ready5f.toLeafInput p5f.regs clamp).run d5f ⟨p5f.pc, rfl⟩
  have run5 := run5f.trans run5c
  have ready5 := ready5f.stack_log p5 (by decide) (by simp only [htifReadChecked, keysG]; decide) (by decide)
    ((p5.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready5f.stack)
    ((p5.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready5f.raReg) (by decide) f2
    (by simp only [LogInW])
  have mem5 : d5.σ.mem = d4.σ.mem := p5.memory.trans p5f.memory
  -- _read: spill, call memcpy
  obtain ⟨d6, run6, p6⟩ := (htif_read_copy_call d5 (nativeStack sp 16) jal_800423b4_call.link buf p n (BitVec.ofNat 64 count) ready5.toLeafInput
    f2 p5.regs
    (by
      rw [mem5, word_observed (m := c.σ.mem) _ fun i hi => slotG _ (by unfold slotOne; omega)
        (by unfold slotOne; omega)]
      exact slot.data)).run d5 ⟨p5.pc, rfl⟩
  have ready6 := ready5.stack_log p6 (by decide) (by simp only [htifReadCopying, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p6.regs rfl) (gholds_lookup (n := 1) _ p6.regs rfl) (by decide) f2
    (htifReadSpillLog_inside f2)
  -- memcpy(buf, 0x8680252c, 16)
  have bufLow : heapEnd ≤ buf.toNat := by omega
  obtain ⟨d7, run7, M⟩ := (memcpy_window d6 H capacity (nativeStack (nativeStack sp 16) 48) jal_80000ccc_call.link
    buf (0x86800090#64 + p) count ready6 (by unfold heapStart heapEnd at *; omega) bufTop
    (fun a foot => by
      rcases foot with global | ⟨_, hi, _⟩
      · unfold allocGlobal InRange heapEnd at *; omega
      · omega)
    ⟨gholds_lookup (n := 10) _ p6.regs rfl, gholds_lookup (n := 11) _ p6.regs rfl,
      gholds_lookup (n := 12) _ p6.regs rfl, trivial⟩
    (fun k hk inside => by unfold InExt at inside; omega)
    (by unfold heapEnd at srcEmbed; omega) (by have := lower; omega)
    (Or.inr (by unfold heapEnd at srcEmbed; unfold Layout.sym_tohost; omega))).run d6 ⟨p6.pc, rfl⟩
  have keepM (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ mRegs)
      (hv : gprGet d6.σ n = some v) : gprGet d7.σ n = some v := (M.registers n lo hi out).trans hv
  -- _read: advance the position, restore, return 16
  have frameBase : nativeFrameBase (nativeStack sp 16) 48 = sp.toNat - 64 := by
    unfold nativeFrameBase; rw [h1]; omega
  have fromD6 (x : Nat) (out : x < buf.toNat ∨ buf.toNat + count ≤ x) :
      (d7.σ.mem[x]?).getD 0 = (d6.σ.mem[x]?).getD 0 :=
    M.kept x (fun inside => by unfold InExt at inside; omega)
  have spill7 (off : Nat) (value : BitVec 64)
      (member : (off, value) ∈ [(24, 6#64), (16, BitVec.ofNat 64 count), (8, BitVec.ofNat 64 count), (40, jal_800423b4_call.link),
        (32, getenvReent c)]) :
      bytesT d7.σ.mem (nativeFrameBase (nativeStack sp 16) 48 + off) 8 = value := by
    have range : off + 8 ≤ 48 := by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega
    rw [word_observed (m := d6.σ.mem) (nativeFrameBase (nativeStack sp 16) 48 + off)
      (fun i hi => fromD6 _ (Or.inl (by rw [frameBase]; omega))), p6.memory]
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact f2.word_log_read (by intro k v hk; simp at hk; omega) (by simp) _ (by simp)
    · exact f2.word_log_read (by intro k v hk; simp at hk; omega) (by simp) _ (by simp)
    · exact f2.word_log_read (by intro k v hk; simp at hk; omega) (by simp) _ (by simp)
    all_goals
      rw [bytesT_writeLog_out _ (by
        rw [htifReadSpillLog, f2.word_log_slots (fun off value member => by simp at member; omega)]
        simp only [List.map, OutLRange, and_true]; omega), mem5, p4.memory]
      exact f2.word_log_read (by intro k v hk; simp at hk; omega) (by simp) _ (by simp)
  have pos7 : bytesT d7.σ.mem (Layout.sym_fds + 80) 8 = p := by
    rw [word_observed (m := c.σ.mem) _ fun i hi => by
      rw [fromD6 _ (Or.inl (by unfold Layout.sym_fds heapEnd at *; omega)), p6.memory,
        frameOn_writeLog _ _ _ (htifReadSpillLog_inside f2) _ ⟨Or.inl (by
          dsimp only; rw [frameBase]; unfold Layout.sym_fds heapEnd at *; omega), trivial⟩, mem5]
      exact fdsG _ (by omega) (by omega)]
    exact pos
  obtain ⟨d8, run8, p8⟩ := (htif_read_advance d7 (nativeStack sp 16) jal_800423b4_call.link (getenvReent c)
    jal_80000ccc_call.link p (BitVec.ofNat 64 count) M.ready.toLeafInput f2
    ⟨keepM 2 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ p6.regs rfl),
      keepM 8 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ p6.regs rfl), trivial⟩
    spill7 pos7 (by decide)).run d7 ⟨M.pc, rfl⟩
  have readLogIn : LogInW takeWindows (readLog p count) := by
    simp only [readLog, LogInW, InsideW, takeWindows]; refine ⟨?_, trivial⟩; omega
  have ready8 := M.ready.window_log p8 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p8.regs rfl) (gholds_lookup (n := 1) _ p8.regs rfl) (by decide)
    readLogIn takeWindows_out_pins ⟨Or.inl (by decide), Or.inl (by decide), trivial⟩
    ⟨Or.inl (by decide), Or.inl (by decide), trivial⟩ (fun a foot => takeWindows_out_foot foot)
  -- _read_r: restore and return 16
  have toD2 (x : Nat) (lo : sp.toNat - 16 ≤ x) (hi : x < sp.toNat) :
      (d8.σ.mem[x]?).getD 0 = (d2.σ.mem[x]?).getD 0 := by
    rw [p8.memory, frameOn_writeLog _ _ _ readLogIn x
        (by simp only [OutW, takeWindows, and_true, Layout.sym_files, Layout.sym_fds, heapEnd] at *; omega),
      fromD6 x (Or.inl (by omega)), p6.memory,
      frameOn_writeLog _ _ _ (htifReadSpillLog_inside f2) x ⟨Or.inr (by rw [h1]; omega), trivial⟩, mem5,
      p4.memory, frameOn_writeLog _ _ _ (htifReadLog_inside f2) x ⟨Or.inr (by rw [h1]; omega), trivial⟩,
      p3'.memory]
    rfl
  obtain ⟨d9, run9, p9⟩ := (read_r_succeed d8 sp ra s0 (BitVec.ofNat 64 count) jal_800423b4_call.link ready8.toLeafInput f1
    ⟨gholds_lookup (n := 10) _ p8.regs rfl, gholds_lookup (n := 2) _ p8.regs rfl, trivial⟩ ok
    (fun off value member => by
      have range : off + 8 ≤ 16 := by
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega
      rw [word_observed (m := d2.σ.mem) _ fun i hi => toD2 _ (by simp only [nativeFrameBase]; omega)
        (by simp only [nativeFrameBase]; omega), p2.memory, openRLog, writeLog_append,
        bytesT_writeLog_out _ (by
          have l := lower; unfold heapEnd at l; simp only [OutLRange, and_true, nativeFrameBase]; omega)]
      exact f1.word_log_read (by
        intro k v hk; simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk; omega)
        (by simp) _ (by
          simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member ⊢
          rcases member with h | h <;> simp [h]))
    ready.aligned).run d8 ⟨p8.pc, rfl⟩
  have keepAll (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ readWrites) : gprGet d9.σ n = gprGet c.σ n := by
    simp only [readWrites, List.mem_cons, List.not_mem_nil, or_false] at out
    exact (p9.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((p8.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
        ((M.registers n lo hi (by simp [VsaIris.PC]; omega)).trans
          ((p6.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
            ((p5.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
              ((p5f.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
              ((p4.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
                ((p3'.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
                  ((p2.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
                    (p1.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega))))))))))
  -- memory away from the stack, buf and errno, back to the caller's
  have back (x : Nat) (stack : x < sp.toNat - 64 ∨ sp.toNat ≤ x) (errno : OutW errnoWindows x)
      (outBuf : x < buf.toNat ∨ buf.toNat + count ≤ x) :
      (d6.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p6.memory, frameOn_writeLog _ _ _ (htifReadSpillLog_inside f2) x ⟨by
        simp only [nativeFrameBase, h1] at *; omega, trivial⟩, mem5,
      p4.memory, frameOn_writeLog _ _ _ (htifReadLog_inside f2) x ⟨by
        simp only [nativeFrameBase, h1] at *; omega, trivial⟩]
    exact mem3 x (by omega) errno
  refine ⟨d9, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans run9))))))), {
    pc := p9.pc
    regs := ⟨gholds_lookup (n := 2) _ p9.regs rfl, gholds_lookup (n := 8) _ p9.regs rfl,
      gholds_lookup (n := 1) _ p9.regs rfl, gholds_lookup (n := 10) _ p9.regs rfl, trivial⟩
    kept := keepAll
    ready := ready8.errno_log p9 (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ p9.regs rfl) (gholds_lookup (n := 1) _ p9.regs rfl) ready.aligned f1
      (by simp only [LogInW])
    trailer := fun k hk => ?_
    mem := fun x stack errno outBuf => ?_ }⟩
  · rw [show d9.σ.mem = d8.σ.mem from p9.memory, p8.memory, frameOn_writeLog _ _ _ readLogIn _
      (by simp only [OutW, takeWindows, and_true, Layout.sym_files, Layout.sym_fds, heapEnd] at *; omega),
      M.bytes k hk]
    exact back _ (Or.inl (by omega)) (by simp only [OutW, errnoWindows, and_true]; unfold heapEnd at srcEmbed; omega)
      (Or.inl (by omega))
  · rw [show d9.σ.mem = d8.σ.mem from p9.memory, p8.memory]
    apply writeLog_getD_congr
    rw [fromD6 x outBuf]
    exact back x stack errno outBuf
end OCaml.Vm.Boot.Startup
