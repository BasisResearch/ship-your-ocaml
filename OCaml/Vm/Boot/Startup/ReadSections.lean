import OCaml.Vm.Boot.Startup.DomainRecord
import OCaml.Vm.Boot.Startup.ReadSectionsSwap
import OCaml.Vm.Boot.Startup.OpenFile
import OCaml.Vm.Boot.Startup.LseekFile
import OCaml.Vm.Boot.Startup.ReadFile
import OCaml.Vm.Boot.Startup.StatChecked
import OCaml.Vm.Boot.Startup.CallerFrame
import OCaml.Vm.Boot.Startup.StatCheckedFrame
import OCaml.Vm.Boot.Startup.MainArgv
import OCaml.Vm.Boot.Startup.ReadyPerm
import OCaml.Vm.Boot.Startup.AttemptOk
import OCaml.Vm.Boot.Startup.ClearReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! `caml_read_section_descriptors(3, &trail)` from caml_main: allocate the
section table, seek to it, read it, and reverse each length's bytes. -/

/-- caml_read_section_descriptors' stack pointer. -/
abbrev sectionsStack : BitVec 64 := nativeStack parameterStack 32

/-- The section table: the 56 bytes before the trailer. -/
def sectionSource : Nat := trailerSource - 56

theorem StatCheckedReturned.fresh {H capacity sp ra s0 n before after}
    (w : StatCheckedReturned H capacity sp ra s0 n before after) :
    FreshBlock vsaLayoutP H (vsaReg w.allocated 10).toNat n.toNat :=
  w.allocation.allocation.result.fresh

/-- caml_main calls `caml_read_section_descriptors(3, &trail)` on "/prog". -/
structure ReadSectionsCall (H : List (Nat × Nat)) (capacity charge : Nat) (node ra s0 s1 s2 : BitVec 64)
    (c : Config) : Prop where
  pc : PCAt 0x80004b0c#64 c
  regs : GHolds c.σ [(2, parameterStack), (1, ra), (10, 3#64), (11, WhileMinElfParse.trailSlot), (8, s0), (9, s1),
    (18, s2)]
  ready : RuntimeReady H (capacity + charge) parameterStack ra c
  charged : vsaChg 56 charge
  embed : EmbedImage c
  file : OpenFile c.σ.mem node
  /-- "/prog"'s name block is live. -/
  nodeOwned : ∀ j, j ≤ 4 → ∃ e ∈ H, InExt e (node.toNat + j)
  numWord : read4 c.σ.mem WhileMinElfParse.trailSlot.toNat = sectionsWord

/-- The open file's bytes are low memory outside the allocator's footprint. -/
theorem ReadSectionsCall.file_kept {H capacity charge node ra s0 s1 s2 c}
    (A : ReadSectionsCall H capacity charge node ra s0 s1 s2 c) {x : Nat} (hx : OpenFileByte node x) :
    x < heapEnd ∧ ¬ vsaFoot H x := by
  rcases hx with ⟨htif, _⟩ | ⟨lo, hi⟩
  · have := htif.bounds
    exact ⟨by unfold Layout.sym_files heapEnd at *; omega, KeptByte.not_foot (Or.inr (Or.inr (Or.inr (Or.inl htif))))⟩
  · obtain ⟨e, he, inside⟩ := A.nodeOwned (x - node.toNat) (by omega)
    have bounds := A.ready.block_bounds (q := e.1) (n := e.2) he
    rw [show node.toNat + (x - node.toNat) = x by omega] at inside
    exact ⟨by unfold InExt at inside; omega, owned_not_foot (by unfold InExt at inside; omega) ⟨e, he, inside⟩⟩

/-- The section table read into the fresh block `blk`, before its lengths are
swapped. -/
structure ReadSectionsLoaded (H : List (Nat × Nat)) (capacity : Nat) (node ra s0 s1 s2 blk : BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt 0x80004b70#64 after
  regs : GHolds after.σ [(8, WhileMinElfParse.trailSlot), (14, 0#64), (2, sectionsStack), (10, 56#64)]
  ready : RuntimeReady ((blk.toNat, 56) :: H) capacity sectionsStack jal_80004b5c_call.link after
  fresh : FreshBlock vsaLayoutP H blk.toNat 56
  blkWord : bytesT after.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat 8 = blk
  numWord : read4 after.σ.mem WhileMinElfParse.trailSlot.toNat = sectionsWord
  table : ∀ k, k < 56 → (after.σ.mem[blk.toNat + k]?).getD 0 = (WhileMinImage.initialMem[sectionSource + k]?).getD 0
  pos : bytesT after.σ.mem (Layout.sym_fds + 80) 8 = 0x249c#64
  file : OpenFile after.σ.mem node
  embed : EmbedImage after
  saved : ∀ off value, (off, value) ∈ readSectionsSlots ra s0 s1 s2 →
    bytesT after.σ.mem (nativeFrameBase parameterStack 32 + off) 8 = value
  /-- The caller's frame, apart from `trail.section`. -/
  caller : ∀ x, parameterStack.toNat ≤ x →
    (x < WhileMinElfParse.trailSlot.toNat + 16 ∨ WhileMinElfParse.trailSlot.toNat + 24 ≤ x) →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  /-- Low memory outside the allocator, `errno` and the file position. -/
  globals : ∀ x, x < heapEnd → ¬ vsaFoot H x → OutW errnoWindows x →
    (x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x) → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem read_sections_load (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat) (node ra s0 s1 s2 : BitVec 64)
    (A : ReadSectionsCall H capacity charge node ra s0 s1 s2 c) :
    ∃ blk after, Steps c after ∧ ReadSectionsLoaded H capacity node ra s0 s1 s2 blk c after := by
  have frame32 : NativeFrame parameterStack 32 := by constructor <;> decide
  have hsp : parameterStack.toNat = 0x87ffff80 := by decide
  have htr : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
  have regs := A.regs
  -- save ra, s0, s2, s1
  obtain ⟨d1, run1, p1⟩ := (read_sections_save c parameterStack ra 3#64 s0 s1 s2 A.ready.toLeafInput frame32
    ⟨gholds_lookup (n := 2) _ regs rfl, gholds_lookup (n := 1) _ regs rfl, gholds_lookup (n := 8) _ regs rfl,
      gholds_lookup (n := 18) _ regs rfl, gholds_lookup (n := 9) _ regs rfl, gholds_lookup (n := 10) _ regs rfl,
      trivial⟩).run c ⟨A.pc, rfl⟩
  have ready1 := A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) A.ready.aligned frame32
    (readSectionsLog_inside frame32)
  have mem1 (x : Nat) (out : x < parameterStack.toNat - 32 ∨ parameterStack.toNat ≤ x) :
      (d1.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p1.memory, frameOn_writeLog _ _ _ (readSectionsLog_inside frame32) x ⟨by unfold nativeFrameBase; omega, trivial⟩]
  -- num_sections * 8; caml_stat_alloc(56)
  obtain ⟨d2, run2, p2⟩ := (read_sections_num_call d1 ra 3#64 WhileMinElfParse.trailSlot ready1.toLeafInput
    ⟨gholds_lookup (n := 10) _ p1.regs rfl,
      (p1.toEffectPost.gpr_frame (by decide) 11 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 11) _ regs rfl), trivial⟩ (by constructor <;> decide)
    (by rw [read4_observed (m := c.σ.mem) _ fun k hk => mem1 _ (Or.inr (by omega))]; exact A.numWord)).run d1
    ⟨p1.pc, rfl⟩
  have ready2 := ready1.stack_log p2 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p2.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready1.stack)
    (gholds_lookup (n := 1) _ p2.regs rfl) (by decide) frame32 (by simp only [LogInW])
  have frame544 : NativeFrame sectionsStack 544 := by constructor <;> decide
  obtain ⟨d3, run3, ⟨w⟩⟩ := (stat_checked d2 H capacity charge sectionsStack jal_80004b34_call.link
    WhileMinElfParse.trailSlot 56#64 ready2 frame544 (gholds_lookup (n := 8) _ p2.regs rfl)
    (gholds_lookup (n := 10) _ p2.regs rfl) A.charged).run d2 ⟨p2.pc, rfl⟩
  have fresh : FreshBlock vsaLayoutP H (vsaReg w.allocated 10).toNat 56 := w.fresh
  generalize hblk : vsaReg w.allocated 10 = blk at fresh
  have regs3 : GHolds d3.σ [(2, sectionsStack), (8, WhileMinElfParse.trailSlot), (1, jal_80004b34_call.link),
      (10, blk)] := by rw [← hblk]; exact w.returned.regs
  have ready3 : RuntimeReady ((blk.toNat, 56) :: H) capacity sectionsStack jal_80004b34_call.link d3 := by
    rw [← hblk]; exact w.ready
  have blkLo : heapStart ≤ blk.toNat := fresh.2.1
  have blkHi : blk.toNat + 56 ≤ heapEnd := fresh.2.2.1
  have mem2 : d2.σ.mem = d1.σ.mem := p2.memory
  -- memory after the allocation: low memory outside the footprint, the caller's frame, the embedded image
  have low3 (x : Nat) (hx : x < heapEnd) (kept : ¬ vsaFoot H x) : (d3.σ.mem[x]?).getD 0 = (d2.σ.mem[x]?).getD 0 :=
    w.framed_byte frame544 hx kept
  have high3 (x : Nat) (hx : sectionsStack.toNat ≤ x) : (d3.σ.mem[x]?).getD 0 = (d2.σ.mem[x]?).getD 0 :=
    (w.caller_frame frame544).byte x hx
  have embed3 : EmbedFrame d2 d3 := w.embed_frame frame544 (by decide)
  -- trail.section = blk; lseek(3, -72, SEEK_END)
  have frameHi : NativeFrame (parameterStack + 64#64) 64 := by constructor <;> decide
  have seekIn : LogInW [⟨nativeFrameBase (parameterStack + 64#64) 64, (parameterStack + 64#64).toNat⟩]
      [((WhileMinElfParse.trailSlot + 16#64).toNat, 8, blk)] := by
    simp only [LogInW, InsideW, nativeFrameBase]; decide
  obtain ⟨d4, run4, p4⟩ := (read_sections_seek_call d3 jal_80004b34_call.link 3#64 WhileMinElfParse.trailSlot blk
    ready3.toLeafInput
    ⟨w.keep9 (gholds_lookup (n := 9) _ p2.regs rfl), gholds_lookup (n := 10) _ regs3 rfl,
      gholds_lookup (n := 8) _ regs3 rfl, w.keep_saved (by decide) (gholds_lookup (n := 18) _ p2.regs rfl), trivial⟩
    (by constructor <;> decide) (frameHi.image_outside seekIn)).run d3 ⟨by rw [← hblk] at *; exact w.returned.pc, rfl⟩
  have ready4 := ready3.stack_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p4.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready3.stack)
    (gholds_lookup (n := 1) _ p4.regs rfl) (by decide) frameHi seekIn
  have mem4 (x : Nat) (out : x < WhileMinElfParse.trailSlot.toNat + 16 ∨ WhileMinElfParse.trailSlot.toNat + 24 ≤ x) :
      (d4.σ.mem[x]?).getD 0 = (d3.σ.mem[x]?).getD 0 := by
    rw [p4.memory, writeLog_out _ _ _ (by
      rw [show (WhileMinElfParse.trailSlot + 16#64).toNat = WhileMinElfParse.trailSlot.toNat + 16 by decide]
      simp only [OutL, and_true]; omega)]
  -- low memory outside the footprint is the entry's
  have low4 (x : Nat) (hx : x < heapEnd) (kept : ¬ vsaFoot H x) : (d4.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [mem4 x (Or.inl (by unfold heapEnd at hx; omega)), low3 x hx kept, mem2, mem1 x (Or.inl (by
      unfold heapEnd at hx; omega))]
  have fileSame (x : Nat) (hx : OpenFileByte node x) : x < heapEnd ∧ ¬ vsaFoot H x := A.file_kept hx
  have file4 : OpenFile d4.σ.mem node := A.file.transport fun x hx => low4 x (fileSame x hx).1 (fileSame x hx).2
  have frame64 : NativeFrame sectionsStack (16 + 48) := by constructor <;> decide
  obtain ⟨d5, run5, L⟩ := (lseek_file d4 ((blk.toNat, 56) :: H) capacity sectionsStack jal_80004b4c_call.link
    WhileMinElfParse.trailSlot (-72#64) ready4 frame64
    ⟨ready4.stack, gholds_lookup (n := 1) _ p4.regs rfl, gholds_lookup (n := 8) _ p4.regs rfl,
      gholds_lookup (n := 10) _ p4.regs rfl, gholds_lookup (n := 11) _ p4.regs rfl,
      gholds_lookup (n := 12) _ p4.regs rfl, trivial⟩
    file4.words node file4.slot file4.kind file4.nodeWord (by decide) (by decide) (by decide)).run d4 ⟨p4.pc, rfl⟩
  have hss : sectionsStack.toNat = 0x87ffff60 := by decide
  have mem5 (x : Nat) (stack : x < sectionsStack.toNat - 64 ∨ sectionsStack.toNat ≤ x) (errno : OutW errnoWindows x)
      (outPos : x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x) :
      (d5.σ.mem[x]?).getD 0 = (d4.σ.mem[x]?).getD 0 := by
    rw [L.mem x stack errno, writeLog_out _ _ _ (by simp only [lseekLog, OutL, and_true]; omega)]
  have pos5 : bytesT d5.σ.mem (Layout.sym_fds + 80) 8 = 0x2464#64 := by
    rw [word_observed (m := writeLog d4.σ.mem (lseekLog (-72#64))) _ fun i hi => L.mem _
      (Or.inl (by unfold Layout.sym_fds; omega)) (by simp only [OutW, errnoWindows, and_true, Layout.sym_fds]; omega)]
    exact (word_writeLog_at d4.σ.mem (lseekLog (-72#64)) 0 (Layout.sym_fds + 80) _ rfl trivial).trans (by decide)
  have htr16 : (WhileMinElfParse.trailSlot + 16#64).toNat = WhileMinElfParse.trailSlot.toNat + 16 := by decide
  have trailErrno (x : Nat) (hx : WhileMinElfParse.trailSlot.toNat ≤ x) : OutW errnoWindows x := by
    simp only [OutW, errnoWindows, and_true]; omega
  have blk5 : bytesT d5.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat 8 = blk := by
    rw [word_observed (m := writeLog d3.σ.mem [((WhileMinElfParse.trailSlot + 16#64).toNat, 8, blk)]) _ fun i hi => by
      rw [mem5 _ (Or.inr (by omega)) (trailErrno _ (by omega)) (Or.inr (by unfold Layout.sym_fds; omega)), p4.memory]]
    exact word_writeLog _ _ _
  -- read(3, blk, 56)
  have keepL (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ lseekWrites)
      (hv : gprGet d4.σ n = some v) : gprGet d5.σ n = some v := (L.kept n lo hi out).trans hv
  obtain ⟨d6, run6, p6⟩ := (read_sections_read_call d5 jal_80004b4c_call.link 3#64 WhileMinElfParse.trailSlot blk
    L.ready.toLeafInput
    ⟨gholds_lookup (n := 8) _ L.regs rfl,
      keepL 9 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ p4.regs rfl),
      keepL 18 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ p4.regs rfl), trivial⟩
    (by constructor <;> decide) blk5).run d5 ⟨L.pc, rfl⟩
  have ready6 := L.ready.stack_log p6 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p6.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans L.ready.stack)
    (gholds_lookup (n := 1) _ p6.regs rfl) (by decide) frame32 (by simp only [LogInW])
  have mem6 : d6.σ.mem = d5.σ.mem := p6.memory
  have fileLow (x : Nat) (hx : OpenFileByte node x) : x < heapEnd ∧ OutW errnoWindows x ∧
      (x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x) := by
    rcases hx with ⟨htif, pos⟩ | ⟨lo, hi⟩
    · exact ⟨(fileSame x (Or.inl ⟨htif, pos⟩)).1, htif.out_errno, pos⟩
    · have low := fileSame x (Or.inr ⟨lo, hi⟩)
      obtain ⟨e, he, inside⟩ := A.nodeOwned (x - node.toNat) (by omega)
      have bounds := A.ready.block_bounds (q := e.1) (n := e.2) he
      rw [show node.toNat + (x - node.toNat) = x by omega] at inside
      unfold InExt at inside
      exact ⟨low.1, by simp only [OutW, errnoWindows, and_true]; unfold heapStart at bounds; omega,
        Or.inr (by unfold heapStart Layout.sym_fds at *; omega)⟩
  have file6 : OpenFile d6.σ.mem node := file4.transport fun x hx => by
    have f := fileLow x hx
    rw [mem6, mem5 x (Or.inl (by unfold heapEnd at f; omega)) f.2.1 f.2.2]
  have bufFoot (a : Nat) (foot : vsaFoot ((blk.toNat, 56) :: H) a) : a < blk.toNat ∨ blk.toNat + 56 ≤ a := by
    rcases foot with global | ⟨_, _, out⟩
    · left; unfold allocGlobal InRange heapStart at *; omega
    · have := out (blk.toNat, 56) (List.mem_cons_self ..)
      unfold InExt at this; omega
  obtain ⟨d7, run7, R⟩ := (read_file d6 ((blk.toNat, 56) :: H) capacity sectionsStack jal_80004b5c_call.link
    WhileMinElfParse.trailSlot blk 0x2464#64 56#64 56 ready6 frame64
    ⟨ready6.stack, gholds_lookup (n := 1) _ p6.regs rfl, gholds_lookup (n := 8) _ p6.regs rfl,
      gholds_lookup (n := 10) _ p6.regs rfl, gholds_lookup (n := 11) _ p6.regs rfl,
      gholds_lookup (n := 12) _ p6.regs rfl, trivial⟩
    (by decide) (by decide) blkLo (by unfold heapEnd at blkHi; omega) bufFoot
    (Or.inl (by unfold heapEnd at blkHi; omega)) (Or.inr (by rw [show (0x86800090#64 + 0x2464#64).toNat = 0x868024f4 by decide]; unfold heapEnd at blkHi; omega))
    file6.words node file6.slot file6.kind file6.nodeWord file6.flags (by rw [mem6]; exact pos5) (by decide)
    (Or.inr ⟨by decide, by decide⟩) (by decide)).run d6 ⟨p6.pc, rfl⟩
  -- memory after the read: back to the entry's
  have read7 (x : Nat) (stack : x < sectionsStack.toNat - 64 ∨ sectionsStack.toNat ≤ x) (errno : OutW errnoWindows x)
      (outBuf : x < blk.toNat ∨ blk.toNat + 56 ≤ x) (outPos : x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x) :
      (d7.σ.mem[x]?).getD 0 = (d4.σ.mem[x]?).getD 0 := by
    rw [R.mem x stack errno outBuf, writeLog_out _ _ _ (by simp only [readLog, OutL, and_true]; omega), mem6,
      mem5 x stack errno outPos]
  have high7 (x : Nat) (hx : sectionsStack.toNat ≤ x)
      (out : x < WhileMinElfParse.trailSlot.toNat + 16 ∨ WhileMinElfParse.trailSlot.toNat + 24 ≤ x) :
      (d7.σ.mem[x]?).getD 0 = (d1.σ.mem[x]?).getD 0 := by
    rw [read7 x (Or.inr hx) (by simp only [OutW, errnoWindows, and_true]; omega)
      (Or.inr (by unfold heapEnd at blkHi; omega)) (Or.inr (by unfold Layout.sym_fds; omega)), mem4 x out,
      high3 x hx, mem2]
  have embed7 (a : Nat) (ha : EmbedByte a) : (d7.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := by
    have lt := (show KeptByte a from Or.inl ha).lt
    unfold EmbedByte at ha
    rw [read7 a (Or.inl (by unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size at lt; omega))
      (by simp only [OutW, errnoWindows, and_true]; unfold heapEnd at ha; omega) (Or.inr (by omega))
      (Or.inr (by unfold heapEnd Layout.sym_fds at *; omega)),
      mem4 a (Or.inl (by unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size at lt; omega)),
      embed3.byte a (Or.inl ⟨ha.1, ha.2⟩), mem2,
      mem1 a (Or.inl (by unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size at lt; omega))]
  have num7 : read4 d7.σ.mem WhileMinElfParse.trailSlot.toNat = sectionsWord := by
    rw [read4_observed (m := c.σ.mem) _ fun k hk => by
      rw [high7 _ (by omega) (Or.inl (by omega)), mem1 _ (Or.inr (by omega))]]
    exact A.numWord
  -- the read returned 56: into the loop
  have keepR (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ readWrites)
      (hv : gprGet d6.σ n = some v) : gprGet d7.σ n = some v := (R.kept n lo hi out).trans hv
  obtain ⟨d8, run8, p8⟩ := (read_sections_test d7 jal_80004b5c_call.link WhileMinElfParse.trailSlot
    R.ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ R.regs rfl, keepR 9 _ (by decide) (by decide) (by decide)
      (gholds_lookup (n := 9) _ p6.regs rfl), gholds_lookup (n := 8) _ R.regs rfl, trivial⟩
    (by constructor <;> decide) num7).run d7 ⟨R.pc, rfl⟩
  have mem8 : d8.σ.mem = d7.σ.mem := p8.memory
  have stack8 : gprGet d8.σ 2 = some sectionsStack :=
    (p8.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans R.ready.stack
  refine ⟨blk, d8, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans run8)))))), {
    pc := p8.pc
    regs := ⟨gholds_lookup (n := 8) _ p8.regs rfl, gholds_lookup (n := 14) _ p8.regs rfl, stack8,
      gholds_lookup (n := 10) _ p8.regs rfl, trivial⟩
    ready := R.ready.stack_log p8 (by decide) (by simp only [keysG]; decide) (by decide) stack8
      ((p8.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans R.ready.raReg)
      R.ready.aligned frame32 (by simp only [LogInW])
    fresh := fresh
    blkWord := ?_
    numWord := by rw [mem8]; exact num7
    table := fun k hk => ?_
    pos := ?_
    file := file6.transport fun x hx => ?_
    embed := ⟨fun a ha => by rw [mem8, embed7 a ha]; exact A.embed.byte a ha⟩
    saved := fun off value member => ?_
    caller := fun x hx out => by
      rw [mem8, high7 x (by omega) out, mem1 x (Or.inr hx)]
    globals := fun x hx kept errno outPos => by
      rw [mem8, read7 x (Or.inl (by unfold heapEnd at hx; omega)) errno (FreshBlock.out_kept fresh hx kept) outPos, low4 x hx kept] }⟩
  · rw [mem8, word_observed (m := d5.σ.mem) _ fun i hi => by
      rw [R.mem _ (Or.inr (by omega)) (trailErrno _ (by omega)) (Or.inr (by unfold heapEnd at blkHi; omega)),
        writeLog_out _ _ _ (by simp only [readLog, OutL, and_true]; unfold Layout.sym_fds; omega), mem6]]
    exact blk5
  · rw [mem8, R.trailer k hk, show (0x86800090#64 + 0x2464#64).toNat = sectionSource by decide, mem6]
    have src : EmbedByte (sectionSource + k) := ⟨by unfold sectionSource trailerSource heapEnd; omega, by
      unfold sectionSource trailerSource embedLimit Layout.sym_stack_top Layout.sym_stack_size; omega⟩
    rw [mem5 _ (Or.inl (by unfold sectionSource trailerSource; omega))
      (by simp only [OutW, errnoWindows, and_true]; unfold sectionSource trailerSource; omega)
      (Or.inr (by unfold sectionSource trailerSource Layout.sym_fds; omega)),
      mem4 _ (Or.inl (by unfold sectionSource trailerSource; omega)), embed3.byte _ (Or.inl src), mem2,
      mem1 _ (Or.inl (by unfold sectionSource trailerSource; omega))]
    exact A.embed.byte _ src
  · rw [mem8, word_observed (m := writeLog d6.σ.mem (readLog 0x2464#64 56)) _ fun i hi => R.mem _
      (Or.inl (by unfold Layout.sym_fds; omega)) (by simp only [OutW, errnoWindows, and_true, Layout.sym_fds]; omega)
      (Or.inl (by unfold heapStart Layout.sym_fds at *; omega))]
    exact (word_writeLog_at d6.σ.mem (readLog 0x2464#64 56) 0 (Layout.sym_fds + 80) _ rfl trivial).trans (by decide)
  · have f := fileLow x hx
    rw [mem8, read7 x (Or.inl (by unfold heapEnd at f; omega)) f.2.1
      (FreshBlock.out_kept fresh f.1 (fileSame x hx).2) f.2.2, mem6,
      mem5 x (Or.inl (by unfold heapEnd at f; omega)) f.2.1 f.2.2]
  · have range : off + 8 ≤ 32 := by
      simp only [readSectionsSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega
    rw [mem8, word_observed (m := d1.σ.mem) _ fun i hi => high7 _ (by unfold nativeFrameBase; omega)
      (Or.inl (by unfold nativeFrameBase; omega)), p1.memory]
    exact frame32.word_log_read (fun off value member => by
        simp only [readSectionsSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega)
      (by simp [readSectionsSlots]) _ member
end OCaml.Vm.Boot.Startup
