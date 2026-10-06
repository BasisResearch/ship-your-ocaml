import OCaml.Vm.Boot.Startup.FsInitSteps
import OCaml.Vm.Boot.Startup.FsInitPath
import OCaml.Vm.Sim.AllocInput
import OCaml.Vm.Sim.FreshLog
import OCaml.Vm.Boot.Startup.ChildScan
import OCaml.Vm.Boot.Startup.RuntimeStack
import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.NewNode
import OCaml.Vm.Boot.Startup.HeapFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-! htif.c's `fs_init()` over the embedded table: the windows it writes outside
`new_node` (its frame, the `files` table, the three descriptors, `fs_ready`),
and the run from its entry to the `strchr` call. -/

def fsFilesWindow : W := ⟨Layout.sym_files, Layout.sym_files + 56 * 64⟩

def fsWindows (sp : BitVec 64) : List W :=
  [⟨nativeFrameBase sp 96, sp.toNat⟩, ⟨Layout.sym_files, Layout.sym_files + 2⟩, ⟨Layout.sym_fds, Layout.sym_fds + 52⟩,
    ⟨Layout.sym_fs_ready, Layout.sym_fs_ready + 4⟩]

theorem fsWindows_stack {sp : BitVec 64} {log : List WEntry}
    (inside : LogInW [⟨nativeFrameBase sp 96, sp.toNat⟩] log) : LogInW (fsWindows sp) log :=
  OCaml.Vm.Sim.logInW_mono inside fun w hw => by simp at hw; simp [fsWindows, hw]

/-- `fs_init`'s writes outside its frame: `files[0]`, the descriptors and `fs_ready`. -/
def fsGlobalLog : List WEntry := [(Layout.sym_files, 2, 257#64)] ++ fdsLog ++ fsReadyLog

theorem fsPrefixLog_split (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64) :
    fsInitLog sp ra s0 s3 s6 s7 ++ [] ++ fdsLog ++ fsReadyLog ++ fsLoopLog sp s1 s2 s4 s5 s8 s9 ++ [] =
      nativeWordLog sp 96 (fsInitSlots ra s0 s3 s6 s7) ++ fsGlobalLog ++ fsLoopLog sp s1 s2 s4 s5 s8 s9 := by
  simp only [fsInitLog, fsGlobalLog, List.append_nil, List.append_assoc]

private theorem logReadNewest_congr {i1 i2 : Nat → Option (BitVec 8)} {x : Nat} (h : i1 x = i2 x) :
    ∀ l : List WEntry, logReadNewest i1 l x = logReadNewest i2 l x
  | [] => h
  | e :: rest => by
    simp only [logReadNewest]
    split
    · rfl
    · exact logReadNewest_congr h rest

/-- A write log reads the same at `x` from any memories that agree there. -/
theorem writeLog_point {m1 m2 : Std.ExtHashMap Nat (BitVec 8)} {x : Nat} (h : m1[x]? = m2[x]?) (log : List WEntry) :
    (writeLog m1 log)[x]? = (writeLog m2 log)[x]? := by
  rw [writeLog_getElem?_logRead, writeLog_getElem?_logRead]
  exact logReadNewest_congr h _

/-- Writes elsewhere in the middle of a log do not change a byte. -/
theorem writeLog_skip (m : Std.ExtHashMap Nat (BitVec 8)) (a g b : List WEntry) {x : Nat} (out : OutL g x) :
    (writeLog m (a ++ g ++ b))[x]? = (writeLog m (a ++ b))[x]? := by
  rw [writeLog_append, writeLog_append, writeLog_append]
  exact writeLog_point (writeLog_out _ _ _ out) b

theorem fsWindows_kept {sp : BitVec 64} (deep : embedLimit + 96 ≤ sp.toNat) (a : Nat) (kept : KeptByte a) :
    OutW (fsWindows sp) a := by
  have := kept.lt
  simp only [fsWindows, fsFilesWindow, OutW, and_true]
  refine ⟨Or.inl (by unfold nativeFrameBase; omega), ?_⟩
  rcases kept with ⟨lo, _⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
    simp only [EmbedByte, EnvironByte, VerbGcByte, heapEnd, Layout.sym_environ, Layout.sym_caml_verb_gc,
      Layout.sym_files, Layout.sym_fds, Layout.sym_fs_ready] at * <;> omega

/-- A state reached by writes inside `fsWindows` keeps the embedded image. -/
theorem EmbedImage.of_fs {c d : Config} {sp : BitVec 64} {log : List WEntry} (image : EmbedImage c)
    (deep : embedLimit + 96 ≤ sp.toNat) (memory : d.σ.mem = writeLog c.σ.mem log)
    (inside : LogInW (fsWindows sp) log) : EmbedImage d :=
  image.frame ⟨fun a ha => by rw [memory, frameOn_writeLog _ _ _ inside a (fsWindows_kept deep a ha)]⟩

theorem fsInitLog_inside {sp ra s0 s3 s6 s7} (frame : NativeFrame sp 96) :
    LogInW (fsWindows sp) (fsInitLog sp ra s0 s3 s6 s7) :=
  OCaml.Vm.Sim.logInW_append' (fsWindows_stack (frame.word_log_inside fun off value member => by
    simp only [fsInitSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    omega)) (by
      simp only [LogInW, InsideW, fsWindows, fsFilesWindow]
      exact ⟨Or.inr (Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩), trivial⟩)

theorem fdsLog_inside {sp : BitVec 64} : LogInW (fsWindows sp) fdsLog := by
  simp only [fdsLog, LogInW, InsideW, fsWindows, fsFilesWindow, Layout.sym_fds]
  refine ⟨?_, ?_, ?_, trivial⟩ <;> omega

theorem fsReadyLog_inside {sp : BitVec 64} : LogInW (fsWindows sp) fsReadyLog := by
  simp only [fsReadyLog, LogInW, InsideW, fsWindows, fsFilesWindow, Layout.sym_fs_ready]
  refine ⟨?_, trivial⟩ <;> omega

theorem fs_prefix_embed {c d : Config} {sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64} (image : EmbedImage c)
    (deep : embedLimit + 96 ≤ sp.toNat) (frame : NativeFrame sp 96)
    (memory : d.σ.mem = writeLog c.σ.mem (fsInitLog sp ra s0 s3 s6 s7 ++ [] ++ fdsLog ++ fsReadyLog ++
      fsLoopLog sp s1 s2 s4 s5 s8 s9)) : EmbedImage d :=
  EmbedImage.of_fs image deep memory (OCaml.Vm.Sim.logInW_append' (OCaml.Vm.Sim.logInW_append'
    (OCaml.Vm.Sim.logInW_append' (OCaml.Vm.Sim.logInW_append' (fsInitLog_inside frame) trivial) fdsLog_inside)
    fsReadyLog_inside) (fsWindows_stack (fsLoopLog_inside frame)))

def fsPrefixWrites : List Nat :=
  [2, 15, 19] ++ [22, 15] ++ [23, 14, 15] ++ [8, 15] ++ [20, 21, 18] ++ ([15, 9, 11, 10, 24, 8] ++ [1])

def fsPrefixLog (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64) : List WEntry :=
  fsInitLog sp ra s0 s3 s6 s7 ++ [] ++ fdsLog ++ fsReadyLog ++ fsLoopLog sp s1 s2 s4 s5 s8 s9 ++ []

def fsInitEntry (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 a0 : BitVec 64) : GRegs :=
  fsInitInput sp ra s0 s3 s6 s7 a0 ++ [(9, s1), (18, s2), (20, s4), (21, s5), (24, s8), (25, s9)]

/-- From `fs_init`'s entry to its `strchr("prog", '/')` call. -/
theorem fs_init_prefix (c : Config) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 a0 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 96) (deep : embedLimit + 96 ≤ sp.toNat) (image : EmbedImage c)
    (regs : GHolds c.σ (fsInitEntry sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 a0)) :
    FnSummary 0x80000350#64 (fun d => d = c)
      (WriteRegistersPost fsPrefixWrites (fsPrefixLog sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) c
        jal_800003ec_call.target (progPath + 1#64)
        ((1, jal_800003ec_call.link) :: fsSkipped sp 0x86800018#64 progPath s9 112#8)) := by
  have entry (n : Nat) (v : BitVec 64) (hv : lookupG n (fsInitEntry sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 a0) = some v) :
      gprGet c.σ n = some v := gholds_lookup _ regs hv
  refine blocks_then c (blocks_then c (blocks_then c (blocks_then c (blocks_then c
    (fs_init_save c sp ra s0 s3 s6 s7 a0 leaf frame (gholds_select regs _ fun n v member => by
      simp only [fsInitInput, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rfl))
    fun d1 p1 => fs_init_header d1 sp ra s0 s6 s7 a0 0x86800018#64 (p1.leaf rfl leaf.aligned) p1.regs
      (EmbedImage.of_fs image deep p1.memory (fsInitLog_inside frame)).fs_header)
    fun d2 p2 => fs_init_fds d2 sp ra s0 s7 a0 0x86800018#64 (p2.leaf rfl leaf.aligned) p2.regs)
    fun d3 p3 => fs_init_first d3 sp ra s0 a0 0x86800018#64 progPath (p3.leaf rfl leaf.aligned) p3.regs
      ⟨by decide, by decide, Or.inr (by decide)⟩
      (EmbedImage.of_fs image deep p3.memory (OCaml.Vm.Sim.logInW_append' (OCaml.Vm.Sim.logInW_append'
        (fsInitLog_inside frame) trivial) fdsLog_inside)).fs_path (by decide))
    fun d4 p4 => fs_init_loop_save d4 sp ra a0 0x86800018#64 progPath s1 s2 s4 s5 s8 s9 (p4.leaf rfl leaf.aligned)
      frame (by
        have keep (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31)
            (unwritten : n ∉ [2, 15, 19] ++ [22, 15] ++ [23, 14, 15] ++ [8, 15])
            (hv : lookupG n (fsInitEntry sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 a0) = some v) :
            gprGet d4.σ n = some v :=
          (p4.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans (entry n v hv)
        exact (gholds_append _ _).2 ⟨p4.regs, keep 9 s1 (by decide) (by decide) (by decide) rfl,
          keep 18 s2 (by decide) (by decide) (by decide) rfl, keep 20 s4 (by decide) (by decide) (by decide) rfl,
          keep 21 s5 (by decide) (by decide) (by decide) rfl, keep 24 s8 (by decide) (by decide) (by decide) rfl,
          keep 25 s9 (by decide) (by decide) (by decide) rfl, trivial⟩))
    fun d5 p5 => fs_init_strchr_call d5 sp ra 0x86800018#64 progPath s1 s8 s9 112#8 (p5.leaf rfl leaf.aligned)
      (fsSkipInput_of_saved p5.regs) ⟨by decide, by decide, Or.inr (by decide)⟩
      ((fs_prefix_embed image deep frame p5.memory).fs_byte 0 (by decide))
      ((fs_prefix_embed image deep frame p5.memory).fs_byte 1 (by decide)) (by decide)

/-- `strchr` keeps every GPR outside its writes. -/
theorem StrchrFrame.gpr {before after : Config} (f : StrchrFrame before after) (n : Nat) (lower : 1 ≤ n)
    (upper : n ≤ 31) (unwritten : n ∉ strchrWrites) : gpr after n = gpr before n := by
  apply gprGet_of_frame n lower upper (VsaIris.Inst.gpr_avoids_noise n (by omega) lower)
  · intro m hm
    have bounds : 1 ≤ m ∧ m ≤ 31 := by
      have h : m ∈ [10, 11, 12, 13, 14, 15, 16, 17, 6, 28] := hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega
    exact gprReg_beq_false m (by omega) n (by omega) bounds.1 lower (fun e => unwritten (e ▸ hm))
  · intro r noise outside
    exact f.regs r (fun m hm => by
      have ne := outside m hm
      exact fun eq => by rw [eq, beq_self_eq_true] at ne; contradiction) noise

/-- A register bundle carried across a step that keeps every GPR outside `writes`. -/
theorem gholds_carry {before after : Config} {writes : List Nat} :
    ∀ {L : GRegs}, GHolds before.σ L →
      (∀ n, 1 ≤ n → n ≤ 31 → n ∉ writes → gpr after n = gpr before n) →
      (∀ n ∈ keysG L, 1 ≤ n ∧ n ≤ 31 ∧ n ∉ writes) → GHolds after.σ L
  | [], _, _, _ => trivial
  | (n, v) :: rest, holds, keep, bounds => by
    have b := bounds n (List.mem_cons_self ..)
    exact ⟨(keep n b.1 b.2.1 b.2.2).trans holds.1,
      gholds_carry holds.2 keep fun m hm => bounds m (List.mem_cons_of_mem _ hm)⟩

theorem prog_name_eq : progPath + 1#64 = progName := by decide

/-- The registers `fs_init` keeps across its scan of "prog". -/
def fsCarried (sp s9 : BitVec 64) : GRegs :=
  [(2, nativeStack sp 96), (8, progName), (9, 0#64), (18, 47#64), (19, BitVec.ofNat 64 Layout.sym_files),
    (20, 0x86800018#64), (21, 0#64), (22, 0x86800018#64), (23, 1#64), (25, s9)]

/-- `fs_init` at its `new_node(0, "prog", 4, 0)` call. -/
structure FsScanned (H : List (Nat × Nat)) (capacity : Nat) (sp s9 : BitVec 64) (d e : Config) : Prop where
  ready : RuntimeReady H capacity (nativeStack sp 96) jal_80000544_call.link e
  pc : PCAt 0x800000f0#64 e
  regs : GHolds e.σ (newNodeInput (nativeStack sp 96) jal_80000544_call.link progName 0#64 progName 4#64 0#64 ++
    [(9, 0#64), (18, 47#64), (19, BitVec.ofNat 64 Layout.sym_files)])
  carried : GHolds e.σ [(20, 0x86800018#64), (21, 0#64), (22, 0x86800018#64), (23, 1#64), (24, 4#64), (25, s9)]
  kept : ∀ x, x < nativeFrameBase (nativeStack sp 96) 64 ∨ (nativeStack sp 96).toNat ≤ x →
    (e.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0
  high : ∀ n, 26 ≤ n → n ≤ 27 → gpr e n = gpr d n

/-- From the `strchr` call to the `new_node` call: "prog" has no '/', its
length is 4, and `child(0, "prog", 4)` misses every (unused) slot. -/
theorem fs_init_scan (d : Config) (H : List (Nat × Nat)) (capacity : Nat) (sp s9 : BitVec 64)
    (ready : RuntimeReady H capacity (nativeStack sp 96) jal_800003ec_call.link d)
    (inner : NativeFrame (nativeStack sp 96) 64)
    (regs : GHolds d.σ ((1, jal_800003ec_call.link) :: fsSkipped sp 0x86800018#64 progPath s9 112#8))
    (embed : EmbedImage d)
    (clear : ∀ j, 1 ≤ j → j < 64 → slotUsed d.σ.mem (Layout.sym_files + 56 * j) = 0#8) :
    FnSummary 0x80040704#64 (fun e => e = d) (FsScanned H capacity sp s9 d) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  simp only [fsSkipped, prog_name_eq] at regs
  have carried0 : GHolds d.σ (fsCarried sp s9) := gholds_select regs _ fun n v member => by
    simp only [fsCarried, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  -- strchr("prog", '/') = NULL
  obtain ⟨e1, run1, ⟨done1, ready1⟩⟩ := (strchr_ready d H capacity (nativeStack sp 96) _ progName 4 ready
    ⟨gholds_lookup (n := 11) _ regs rfl, gholds_lookup (n := 10) _ regs rfl, trivial⟩ embed.prog_slash
    embed.prog_plan).run d ⟨pc, rfl⟩
  have carried1 := gholds_carry carried0 done1.frame.gpr (by simp only [fsCarried, keysG]; decide)
  -- strlen("prog") = 4
  obtain ⟨e2, run2, p2⟩ := (fs_init_strlen_call e1 _ progName 0#64 ready1.toLeafInput
    ⟨gholds_lookup (n := 10) _ done1.regs rfl, gholds_lookup (n := 8) _ carried1 rfl,
      gholds_lookup (n := 9) _ carried1 rfl, trivial⟩).run e1 ⟨done1.pc, rfl⟩
  have carried2 := gholds_carry carried1 (p2.toEffectPost.gpr_frame (by decide))
    (by simp only [fsCarried, keysG]; decide)
  have ready2 := ready1.stack_log p2 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ carried2 rfl) (gholds_lookup (n := 1) _ p2.regs rfl) (by decide) inner
    (by simp only [LogInW])
  have mem2 : e2.σ.mem = d.σ.mem := p2.memory.trans done1.memory
  have embed2 : EmbedImage e2 := embed.frame ⟨fun a _ => by rw [mem2]⟩
  obtain ⟨e3, run3, R3⟩ := (strlen_ready e2 H capacity (nativeStack sp 96) _ progName 4 ready2 embed2.prog_cbytes
    (gholds_lookup (n := 10) _ p2.regs rfl)).run e2 ⟨p2.pc, rfl⟩
  have carried3 := gholds_carry carried2 R3.post.registers (by simp only [fsCarried, keysG]; decide)
  -- child(0, "prog", 4) = -1
  obtain ⟨e4, run4, p4⟩ := (fs_init_child_call e3 _ 4#64 progName 0#64 R3.ready.toLeafInput
    ⟨R3.post.result, gholds_lookup (n := 8) _ carried3 rfl, gholds_lookup (n := 9) _ carried3 rfl, trivial⟩
    (by decide)).run e3 ⟨R3.post.pc, rfl⟩
  have carried4 := gholds_carry carried3 (p4.toEffectPost.gpr_frame (by decide))
    (by simp only [fsCarried, keysG]; decide)
  have ready4 := R3.ready.stack_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ carried4 rfl) (gholds_lookup (n := 1) _ p4.regs rfl) (by decide) inner
    (by simp only [LogInW])
  have same4 (x : Nat) : (e4.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0 := by
    rw [p4.memory, show writeLog e3.σ.mem [] = e3.σ.mem from rfl]
    have := R3.post.memory x
    simp only [Std.ExtHashMap.get?_eq_getElem?] at this
    rw [this, mem2]
  obtain ⟨a5, ha5⟩ := Option.isSome_iff_exists.mp (ready4.platform.gpr 15 (by decide) (by decide))
  obtain ⟨e5, run5, p5⟩ := (child_miss e4 (nativeStack sp 96) _ progName 0#64 47#64
    (BitVec.ofNat 64 Layout.sym_files) 0x86800018#64 0#64 0#64 progName 4#64 a5 ready4.toLeafInput inner
    ⟨gholds_lookup (n := 2) _ carried4 rfl, gholds_lookup (n := 8) _ carried4 rfl,
      gholds_lookup (n := 9) _ carried4 rfl, gholds_lookup (n := 18) _ carried4 rfl,
      gholds_lookup (n := 19) _ carried4 rfl, gholds_lookup (n := 20) _ carried4 rfl,
      gholds_lookup (n := 21) _ carried4 rfl, gholds_lookup (n := 1) _ p4.regs rfl,
      gholds_lookup (n := 10) _ p4.regs rfl, gholds_lookup (n := 11) _ p4.regs rfl,
      gholds_lookup (n := 12) _ p4.regs rfl, ha5, trivial⟩
    (fun j lo hi => .unused (by unfold slotUsed; rw [same4]; exact clear j lo hi))).run e4 ⟨p4.pc, rfl⟩
  have keep5 (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31)
      (unwritten : n ∉ [2, 19, 21, 20, 8, 9, 18, 15, 1, 10]) (hv : gprGet e4.σ n = some v) : gprGet e5.σ n = some v :=
    (p5.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans hv
  have ready5 := ready4.stack_log p5 (by decide) (by simp only [childResult, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p5.regs rfl) (gholds_lookup (n := 1) _ p5.regs rfl) (by decide) inner
    (childLog_inside inner)
  -- new_node(0, "prog", 4, 0)
  obtain ⟨e6, run6, p6⟩ := (fs_init_new_call e5 _ progName 0#64 4#64 ready5.toLeafInput
    ⟨gholds_lookup (n := 10) _ p5.regs rfl,
      keep5 24 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 24) _ p4.regs rfl),
      gholds_lookup (n := 8) _ p5.regs rfl, gholds_lookup (n := 9) _ p5.regs rfl, trivial⟩).run e5 ⟨p5.pc, rfl⟩
  have keep6 (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31)
      (unwritten : n ∉ [12, 11, 10, 13] ++ [1]) (hv : gprGet e5.σ n = some v) : gprGet e6.σ n = some v :=
    (p6.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans hv
  refine ⟨e6, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))), ?_⟩
  refine ⟨ready5.stack_log p6 (by decide) (by simp only [keysG]; decide) (by decide)
      (keep6 2 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ p5.regs rfl))
      (gholds_lookup (n := 1) _ p6.regs rfl) (by decide) inner (by simp only [LogInW]), p6.pc,
    ⟨keep6 2 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ p5.regs rfl),
      gholds_lookup (n := 8) _ p6.regs rfl, gholds_lookup (n := 1) _ p6.regs rfl,
      gholds_lookup (n := 10) _ p6.regs rfl, gholds_lookup (n := 11) _ p6.regs rfl,
      gholds_lookup (n := 12) _ p6.regs rfl, gholds_lookup (n := 13) _ p6.regs rfl,
      gholds_lookup (n := 9) _ p6.regs rfl,
      keep6 18 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ p5.regs rfl),
      keep6 19 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ p5.regs rfl), trivial⟩,
    ⟨keep6 20 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 20) _ p5.regs rfl),
      keep6 21 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 21) _ p5.regs rfl),
      keep6 22 _ (by decide) (by decide) (by decide)
        (keep5 22 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 22) _ carried4 rfl)),
      keep6 23 _ (by decide) (by decide) (by decide)
        (keep5 23 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 23) _ carried4 rfl)),
      gholds_lookup (n := 24) _ p6.regs rfl,
      keep6 25 _ (by decide) (by decide) (by decide)
        (keep5 25 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 25) _ carried4 rfl)), trivial⟩,
    fun x out => ?_, fun n lo hi =>
      (p6.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega)).trans
      ((p5.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega)).trans
      ((p4.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega)).trans
      ((R3.post.registers n (by omega) (by omega) (by simp; omega)).trans
      ((p2.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega)).trans
      (done1.frame.gpr n (by omega) (by omega) (by simp [strchrWrites]; omega))))))⟩
  rw [p6.memory, show writeLog e5.σ.mem [] = e5.σ.mem from rfl, p5.memory,
    frameOn_writeLog _ _ _ (childLog_inside inner) x ⟨out, trivial⟩, same4]

/-- The `files` table misses the allocator's footprint and protected words. -/
theorem fsFiles_out_foot {H : List (Nat × Nat)} {a : Nat} (foot : vsaFoot H a) : OutW [fsFilesWindow] a := by
  simp only [OutW, fsFilesWindow, and_true]
  rcases foot with global | ⟨lo, _⟩
  · unfold allocGlobal InRange at global; unfold Layout.sym_files; omega
  · unfold heapStart at lo; unfold Layout.sym_files; omega

theorem fsFiles_out_pins (pin : Nat × BitVec 8) (member : pin ∈ VsaIris.Sym.allocText) :
    OutW [fsFilesWindow] pin.1 := by
  have source := allocator_sources pin member
  unfold AllocatorByteSource at source
  simp only [OutW, fsFilesWindow, and_true]
  left
  split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr, Layout.sym_files] at * <;> omega

theorem fsFileLog_inside (start stop : BitVec 64) : LogInW [fsFilesWindow] (fsFileLog start stop) := by
  simp only [fsFileLog, LogInW, InsideW, fsFilesWindow, slotOne, Layout.sym_files]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> omega

/-- Slot 1 of `files` as `fs_init` leaves it: the file "prog" in the root,
named by the block at `node`, with the embedded extent, read-only. -/
structure FsSlotOne (m : Std.ExtHashMap Nat (BitVec 8)) (node : BitVec 64) : Prop where
  used : (m[slotOne]?).getD 0 = 1#8
  dirByte : (m[slotOne + 1]?).getD 0 = 0#8
  linked : (m[slotOne + 2]?).getD 0 = 1#8
  parent : slotParent m slotOne = 0#64
  namePtr : bytesT m (slotOne + 8) 8 = node
  length : slotLength m slotOne = 4#64
  data : bytesT m (slotOne + 24) 8 = 0x86800090#64
  size : bytesT m (slotOne + 32) 8 = 0x24ac#64
  cap : bytesT m (slotOne + 40) 8 = 0x24ac#64
  ro : (m[slotOne + 52]?).getD 0 = 1#8
  name : ∀ j, j < 4 → (m[node.toNat + j]?).getD 0 = progByte (j + 1)
  nul : (m[node.toNat + 4]?).getD 0 = 0#8

local macro "file_out" : tactic =>
  `(tactic| (simp only [fsFileLog, OutL, OutLRange, slotOne, Layout.sym_files, List.drop, and_true]; omega))

/-- `fs_init` after slot 1 is set up: back at its caller. -/
structure FsTail (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64)
    (before after : Config) where
  node : BitVec 64
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (23, s7), (22, s6), (19, s3), (8, s0), (1, ra), (25, s9), (24, s8), (21, s5),
    (20, s4), (18, s2), (9, s1), (10, 1#64)]
  ready : RuntimeReady ((node.toNat, 5) :: H) capacity sp ra after
  embed : EmbedImage after
  slot : FsSlotOne after.σ.mem node
  low : ∀ x, x < heapStart → ¬ allocGlobal x → (x < slotOne ∨ slotOne + 56 ≤ x) →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  live : ∀ e ∈ H, ∀ x, InExt e x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  high : ∀ n, 26 ≤ n → n ≤ 27 → gprGet after.σ n = gprGet before.σ n

/-- `new_node(0, "prog", 4, 0)` takes slot 1; `fs_init` records the file's
extent there, finds the table's end and returns. -/
theorem fs_init_tail (e : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64)
    (ready : RuntimeReady H (capacity + charge) (nativeStack sp 96) jal_80000544_call.link e)
    (frame : NativeFrame sp (96 + (64 + allocHeadroom))) (deep : embedLimit + 96 + (64 + allocHeadroom) ≤ sp.toNat)
    (regs : GHolds e.σ (newNodeInput (nativeStack sp 96) jal_80000544_call.link progName 0#64 progName 4#64 0#64 ++
      [(9, 0#64), (18, 47#64), (19, BitVec.ofNat 64 Layout.sym_files)]))
    (carried : GHolds e.σ [(20, 0x86800018#64), (21, 0#64), (22, 0x86800018#64), (23, 1#64), (24, 4#64), (25, s9)])
    (embed : EmbedImage e) (free : (e.σ.mem[slotOne]?).getD 0 = 0#8)
    (saved : ∀ off value, (off, value) ∈ fsInitRestored ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 →
      bytesT e.σ.mem (nativeFrameBase sp 96 + off) 8 = value) (aligned : ra.toNat % 4 = 0)
    (charged : vsaChg 5 charge) :
    FnSummary 0x800000f0#64 (fun d => d = e) (fun after => Nonempty (FsTail H capacity sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 e after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have frame96 := frame.resize (small := 96) (by unfold allocHeadroom; omega) (by decide)
  have inner : NativeFrame (nativeStack sp 96) (64 + allocHeadroom) := frame.nested (front := 96) (by decide)
  have spNat := frame96.stack_nat
  have upper := frame.upper
  -- new_node(0, "prog", 4, 0) = 1
  obtain ⟨f, run1, ⟨N⟩⟩ := (new_node_slot1 e H capacity charge (nativeStack sp 96) _ progName 0#64 47#64
    (BitVec.ofNat 64 Layout.sym_files) 0#64 progName 4#64 0#64 ready inner regs free
    ⟨by decide, by
      have : progName.toNat = 0x8680253e := by decide
      rw [this, show (4#64).toNat = 4 by decide]
      unfold nativeFrameBase; rw [spNat]; unfold nativeFrameBase embedLimit Layout.sym_stack_top Layout.sym_stack_size
        allocHeadroom at *; omega⟩
    (by decide) charged).run e ⟨pc, rfl⟩
  have fresh := N.fresh
  have keptF (a : Nat) (ka : KeptByte a) : (f.σ.mem[a]?).getD 0 = (e.σ.mem[a]?).getD 0 := by
    have lt := ka.lt
    apply N.kept
    refine ⟨Or.inl ?_, ka.not_foot, ?_, fun inside => ?_⟩
    · unfold nativeFrameBase; rw [spNat]; unfold nativeFrameBase allocHeadroom at *; omega
    · rcases ka with ⟨lo, _⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
        simp only [heapEnd, slotOne, Layout.sym_files, Layout.sym_environ, Layout.sym_caml_verb_gc] at * <;> omega
    · unfold InExt at inside
      rcases ka with ⟨lo, _⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
        simp only [heapEnd, heapStart, Layout.sym_environ, Layout.sym_caml_verb_gc] at * <;> omega
  have embedF : EmbedImage f := embed.frame ⟨keptF⟩
  have upperF (n : Nat) (v : BitVec 64) (lo : 20 ≤ n) (hi : n ≤ 27) (hv : gprGet e.σ n = some v) :
      gprGet f.σ n = some v := (N.upper n lo hi).trans hv
  -- the file's extent
  obtain ⟨g, run2, p2⟩ := (fs_init_file f _ 0x86800018#64 N.ready.toLeafInput
    ⟨N.result, gholds_lookup (n := 19) _ N.regs rfl,
      upperF 20 _ (by decide) (by decide) (gholds_lookup (n := 20) _ carried rfl),
      upperF 23 _ (by decide) (by decide) (gholds_lookup (n := 23) _ carried rfl), trivial⟩
    (N.dirByte.trans (by decide)) ⟨by decide, by decide, Or.inr (by decide)⟩ ⟨by decide, by decide, Or.inr (by decide)⟩
    (by decide)).run f ⟨N.pc, rfl⟩
  have keepG (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [15, 14, 13])
      (hv : gprGet f.σ n = some v) : gprGet g.σ n = some v :=
    (p2.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans hv
  have readyG := N.ready.window_log p2 (by decide) (by simp only [fsFiled, keysG]; decide) (by decide)
    (keepG 2 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ N.regs rfl))
    (keepG 1 _ (by decide) (by decide) (by decide) N.ready.raReg) (by decide) (fsFileLog_inside _ _)
    fsFiles_out_pins
    ⟨Or.inl (by decide), trivial⟩ ⟨Or.inl (by decide), trivial⟩
    (fun a foot => fsFiles_out_foot foot)
  have filesOut (a : Nat) (out : OutW [fsFilesWindow] a) : (g.σ.mem[a]?).getD 0 = (f.σ.mem[a]?).getD 0 := by
    rw [p2.memory, frameOn_writeLog _ _ _ (fsFileLog_inside _ _) a out]
  have embedG : EmbedImage g := embedF.frame ⟨fun a ka => filesOut a (by
    have := ka.lt
    simp only [OutW, fsFilesWindow, and_true]
    rcases ka with ⟨lo, _⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
      simp only [heapEnd, Layout.sym_files, Layout.sym_environ, Layout.sym_caml_verb_gc] at * <;> omega)⟩
  -- the table ends: restore and return
  obtain ⟨h, run3, p3⟩ := (fs_init_return g sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 0x86800018#64 _ readyG.toLeafInput
    frame96
    ⟨keepG 21 _ (by decide) (by decide) (by decide)
        (upperF 21 _ (by decide) (by decide) (gholds_lookup (n := 21) _ carried rfl)),
      keepG 22 _ (by decide) (by decide) (by decide)
        (upperF 22 _ (by decide) (by decide) (gholds_lookup (n := 22) _ carried rfl)),
      keepG 2 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ N.regs rfl),
      gholds_lookup (n := 10) _ p2.regs rfl, trivial⟩
    ⟨by decide, by decide, Or.inr (by decide)⟩ embedG.fs_end
    (fun off value member => by
      have range : 8 ≤ off ∧ off + 8 ≤ 96 := by
        simp only [fsInitRestored, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
        omega
      rw [word_observed (m := e.σ.mem) _ (fun i hi => by
        rw [filesOut _ (by
          simp only [OutW, fsFilesWindow, and_true]
          right; have := frame.lower; unfold nativeFrameBase heapEnd Layout.sym_files at *; omega)]
        apply N.kept
        refine ⟨Or.inr ?_, fun foot => ?_, Or.inr ?_, fun inside => ?_⟩
        · rw [spNat]; unfold nativeFrameBase; omega
        · have := allocator_foot_below foot; have := frame.lower; unfold nativeFrameBase heapEnd at *; omega
        · have := frame.lower; unfold nativeFrameBase heapEnd slotOne Layout.sym_files at *; omega
        · unfold InExt at inside; have := frame.lower; unfold nativeFrameBase at *; omega)]
      exact saved off value member) aligned).run g ⟨p2.pc, rfl⟩
  have readyH := readyG.stack_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p3.regs rfl) (gholds_lookup (n := 1) _ p3.regs rfl) aligned frame96
    (by simp only [LogInW])
  -- slot 1 and the name, at g (= h)
  have memH : h.σ.mem = g.σ.mem := p3.memory
  have memG : g.σ.mem = writeLog f.σ.mem (fsFileLog 0x86800090#64 0x8680253c#64) := by
    rw [p2.memory, embedF.fs_start, embedF.fs_stop]
  have fileOut (x : Nat) (out : OutL (fsFileLog 0x86800090#64 0x8680253c#64) x) :
      (g.σ.mem[x]?).getD 0 = (f.σ.mem[x]?).getD 0 := by
    rw [memG, writeLog_out _ _ _ out]
  have nodeLo := fresh.1
  obtain ⟨par0, par1, par2, par3⟩ := N.parent
  have slot : FsSlotOne g.σ.mem N.node := {
    used := (fileOut slotOne (by file_out)).trans N.used
    dirByte := (fileOut (slotOne + 1) (by file_out)).trans (N.dirByte.trans (by decide))
    linked := (fileOut (slotOne + 2) (by file_out)).trans N.linked
    parent := by
      unfold slotParent read4
      rw [fileOut (slotOne + 4) (by file_out), fileOut (slotOne + 4 + 1) (by file_out),
        fileOut (slotOne + 4 + 2) (by file_out), fileOut (slotOne + 4 + 3) (by file_out), par0, par1, par2, par3]
      decide
    namePtr := by rw [memG, bytesT_writeLog_out _ (by file_out)]; exact N.namePtr
    length := by unfold slotLength; rw [memG, bytesT_writeLog_out _ (by file_out)]; exact N.length
    data := by rw [memG]; exact word_writeLog_at _ _ 0 _ _ rfl (by file_out)
    size := by rw [memG]; exact word_writeLog_at _ _ 3 _ _ rfl trivial
    cap := by rw [memG]; exact word_writeLog_at _ _ 2 _ _ rfl (by file_out)
    ro := by rw [memG]; exact (byte_writeLog_at _ _ 1 _ _ rfl (by file_out)).trans (by decide)
    name := fun j hj => by
      rw [fileOut (N.node.toNat + j) (by unfold heapStart at nodeLo; file_out), N.copied j (by rw [show (4#64).toNat = 4 from rfl]; exact hj)]
      have := embed.fs_byte (j + 1) (by omega)
      rw [show WhileMinImage.embedPath0 + (j + 1) = progName.toNat + j by
        unfold WhileMinImage.embedPath0; simp only [progName]; rw [BitVec.toNat_ofNat]; omega] at this
      exact this
    nul := by
      rw [fileOut (N.node.toNat + 4) (by unfold heapStart at nodeLo; file_out)]
      exact N.terminated }
  refine ⟨h, run1.trans (run2.trans run3), ⟨{
    node := N.node
    pc := p3.pc
    regs := p3.regs
    ready := readyH
    embed := embedG.frame ⟨fun a _ => by rw [memH]⟩
    slot := memH ▸ slot
    low := fun x below global apart => by
      rw [memH, fileOut x (by unfold heapStart at below; unfold slotOne Layout.sym_files at apart; file_out)]
      apply N.kept
      refine ⟨Or.inl ?_, fun foot => ?_, apart, fun inside => ?_⟩
      · unfold nativeFrameBase; rw [spNat]
        unfold nativeFrameBase heapStart allocHeadroom embedLimit Layout.sym_stack_top Layout.sym_stack_size at *; omega
      · rcases foot with g' | ⟨lo, _⟩
        · exact global g'
        · omega
      · unfold InExt at inside; omega
    live := fun e he x inside => by
      have bounds := ready.heap.block_bounds (q := e.1) (n := e.2) he
      unfold InExt at inside
      rw [memH, fileOut x (by unfold heapStart at bounds; file_out)]
      apply N.kept
      refine ⟨Or.inl ?_, fun foot => ?_, Or.inr (by unfold slotOne Layout.sym_files heapStart at *; omega),
        fun block => N.disjoint e he x block (by unfold InExt; omega)⟩
      · unfold nativeFrameBase; rw [spNat]
        unfold nativeFrameBase heapEnd allocHeadroom embedLimit Layout.sym_stack_top Layout.sym_stack_size at *; omega
      · rcases foot with g' | ⟨_, _, apart⟩
        · rcases allocGlobal_off_arena x g' with l | r <;> omega
        · exact apart e he (by unfold InExt; omega)
    high := fun n lo hi =>
      (p3.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega)).trans
      ((p2.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega)).trans
      (N.upper n (by omega) (by omega))) }⟩⟩

theorem fsPrefixLog_inside {sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64} (frame : NativeFrame sp 96) :
    LogInW (fsWindows sp) (fsPrefixLog sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) :=
  OCaml.Vm.Sim.logInW_append' (OCaml.Vm.Sim.logInW_append' (OCaml.Vm.Sim.logInW_append'
    (OCaml.Vm.Sim.logInW_append' (OCaml.Vm.Sim.logInW_append' (fsInitLog_inside frame) trivial) fdsLog_inside)
    fsReadyLog_inside) (fsWindows_stack (fsLoopLog_inside frame))) trivial

/-- `fs_init`'s windows miss the allocator's text pins, footprint and protected words. -/
structure FsWindowsApart (sp : BitVec 64) : Prop where
  pins : ∀ pin ∈ VsaIris.Sym.allocText, OutW (fsWindows sp) pin.1
  domain : OutWRange (fsWindows sp) Layout.sym_Caml_state 8
  pool : OutWRange (fsWindows sp) Layout.sym_pool 8
  heap : ∀ H a, vsaFoot H a → OutW (fsWindows sp) a

theorem fsWindows_apart {sp : BitVec 64} (frame : NativeFrame sp 96) : FsWindowsApart sp where
  pins := fun pin member => by
    have lower := frame.lower
    have source := allocator_sources pin member
    unfold AllocatorByteSource at source
    simp only [OutW, fsWindows, and_true]
    split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr, Layout.sym_files,
      Layout.sym_fds, Layout.sym_fs_ready, nativeFrameBase, heapEnd] at * <;> omega
  domain := by
    have lower := frame.lower
    simp only [OutWRange, fsWindows, and_true, nativeFrameBase, Layout.sym_Caml_state, Layout.sym_files,
      Layout.sym_fds, Layout.sym_fs_ready, heapEnd] at *
    omega
  pool := by
    have lower := frame.lower
    simp only [OutWRange, fsWindows, and_true, nativeFrameBase, Layout.sym_pool, Layout.sym_files,
      Layout.sym_fds, Layout.sym_fs_ready, heapEnd] at *
    omega
  heap := fun H a foot => by
    have lower := frame.lower
    have below := allocator_foot_below foot
    simp only [OutW, fsWindows, and_true]
    rcases foot with global | ⟨lo, _⟩
    · unfold allocGlobal InRange at global
      simp only [Layout.sym_files, Layout.sym_fds, Layout.sym_fs_ready, nativeFrameBase, heapEnd] at *
      omega
    · simp only [Layout.sym_files, Layout.sym_fds, Layout.sym_fs_ready, nativeFrameBase, heapEnd, heapStart] at *
      omega

/-- What `fs_init()` leaves: slot 1 = "prog", the other slots unused, every
other low byte outside its windows unchanged, readiness with the name live. -/
structure FsInitDone (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64)
    (before after : Config) where
  node : BitVec 64
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (23, s7), (22, s6), (19, s3), (8, s0), (1, ra), (25, s9), (24, s8), (21, s5),
    (20, s4), (18, s2), (9, s1), (10, 1#64)]
  ready : RuntimeReady ((node.toNat, 5) :: H) capacity sp ra after
  embed : EmbedImage after
  slot : FsSlotOne after.σ.mem node
  rest : ∀ j, 2 ≤ j → j < 64 → slotUsed after.σ.mem (Layout.sym_files + 56 * j) = 0#8
  low : ∀ x, x < heapStart → ¬ allocGlobal x → OutW (fsWindows sp) x → (x < slotOne ∨ slotOne + 56 ≤ x) →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  live : ∀ e ∈ H, ∀ x, InExt e x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  high : ∀ n, 26 ≤ n → n ≤ 27 → gprGet after.σ n = gprGet before.σ n

/-- **`fs_init()` over the embedded table "/prog"**: slot 1 becomes the file
`prog` under the root, the descriptors and `fs_ready` are set, and the
caller's registers are restored. -/
theorem fs_init (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 a0 : BitVec 64)
    (ready : RuntimeReady H (capacity + charge) sp ra c)
    (frame : NativeFrame sp (96 + (64 + allocHeadroom))) (deep : embedLimit + 96 + (64 + allocHeadroom) ≤ sp.toNat)
    (image : EmbedImage c) (regs : GHolds c.σ (fsInitEntry sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 a0))
    (clear : ∀ j, 1 ≤ j → j < 64 → slotUsed c.σ.mem (Layout.sym_files + 56 * j) = 0#8)
    (charged : vsaChg 5 charge) :
    FnSummary 0x80000350#64 (fun d => d = c)
      (fun after => Nonempty (FsInitDone H capacity sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have frame96 := frame.resize (small := 96) (by unfold allocHeadroom; omega) (by decide)
  have inner : NativeFrame (nativeStack sp 96) (64 + allocHeadroom) := frame.nested (front := 96) (by decide)
  have inner64 := inner.resize (small := 64) (by unfold allocHeadroom; omega) (by decide)
  have spNat := frame96.stack_nat
  have deep96 : embedLimit + 96 ≤ sp.toNat := by omega
  have lower := frame.lower
  -- entry to the strchr call
  obtain ⟨d, run1, p1⟩ := (fs_init_prefix c sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 a0 ready.toLeafInput frame96 deep96
    image regs).run c ⟨pc, rfl⟩
  have inside := fsPrefixLog_inside (ra := ra) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (s5 := s5)
    (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) frame96
  have apart := fsWindows_apart frame96
  have readyD := ready.window_log p1 (by decide) (by simp only [fsPrefixWrites, fsSkipped, keysG]; decide)
    (by decide) (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) (by decide) inside
    apart.pins apart.domain apart.pool (apart.heap H)
  have embedD : EmbedImage d := EmbedImage.of_fs image deep96 p1.memory inside
  have keepD (x : Nat) (out : OutW (fsWindows sp) x) : (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p1.memory, frameOn_writeLog _ _ _ inside x out]
  have clearD (j : Nat) (lo : 1 ≤ j) (hi : j < 64) : slotUsed d.σ.mem (Layout.sym_files + 56 * j) = 0#8 := by
    unfold slotUsed
    rw [keepD _ (by
      simp only [OutW, fsWindows, and_true, nativeFrameBase, Layout.sym_files, Layout.sym_fds, Layout.sym_fs_ready,
        heapEnd] at *
      omega)]
    exact clear j lo hi
  -- the scan to new_node
  obtain ⟨e, run2, S⟩ := (fs_init_scan d H (capacity + charge) sp s9 readyD inner64 p1.regs embedD clearD).run d
    ⟨p1.pc, rfl⟩
  have keptE (x : Nat) (high : nativeFrameBase sp 96 ≤ x) : (e.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0 :=
    S.kept x (Or.inr (by rw [spNat]; exact high))
  have embedE : EmbedImage e := embedD.frame ⟨fun a ka => S.kept a (Or.inl (by
    have := ka.lt
    unfold nativeFrameBase; rw [spNat]; unfold nativeFrameBase allocHeadroom at *; omega))⟩
  have freeE : (e.σ.mem[slotOne]?).getD 0 = 0#8 := by
    rw [S.kept _ (Or.inl (by
      unfold nativeFrameBase; rw [spNat]; unfold nativeFrameBase slotOne Layout.sym_files heapEnd at *; omega))]
    exact clearD 1 (by decide) (by decide)
  have savedE (off : Nat) (value : BitVec 64) (member : (off, value) ∈ fsInitRestored ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) :
      bytesT e.σ.mem (nativeFrameBase sp 96 + off) 8 = value := by
    have range : 8 ≤ off ∧ off + 8 ≤ 96 := by
      simp only [fsInitRestored, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      omega
    rw [word_observed (m := writeLog c.σ.mem (nativeWordLog sp 96 (fsInitSlots ra s0 s3 s6 s7) ++
        fsLoopLog sp s1 s2 s4 s5 s8 s9)) _ (fun i hi => by
      rw [keptE _ (by omega), p1.memory, fsPrefixLog, fsPrefixLog_split, writeLog_skip]
      simp only [fsGlobalLog, fdsLog, fsReadyLog, List.cons_append, List.nil_append, OutL]
      unfold nativeFrameBase heapEnd Layout.sym_files Layout.sym_fds Layout.sym_fs_ready at *
      refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega),
      fsLoopLog, nativeWordLog, nativeWordLog, ← List.map_append, ← nativeWordLog]
    apply frame96.word_log_read
    · intro k v hk
      simp only [fsInitSlots, fsLoopSlots, List.cons_append, List.nil_append, List.mem_cons, Prod.mk.injEq,
        List.not_mem_nil, or_false] at hk
      omega
    · simp [fsInitSlots, fsLoopSlots]
    · simp only [fsInitRestored, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [fsInitSlots, fsLoopSlots]
  obtain ⟨after, run3, ⟨T⟩⟩ := (fs_init_tail e H capacity charge sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 S.ready frame
    deep S.regs S.carried embedE freeE savedE ready.aligned charged).run e ⟨S.pc, rfl⟩
  have lowE (x : Nat) (below : x < heapStart) (out : OutW (fsWindows sp) x) :
      (e.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [S.kept x (Or.inl (by
      unfold nativeFrameBase; rw [spNat]
      unfold nativeFrameBase heapStart heapEnd at *; omega)), keepD x out]
  refine ⟨after, run1.trans (run2.trans run3), ⟨{
    node := T.node
    pc := T.pc
    regs := T.regs
    ready := T.ready
    embed := T.embed
    slot := T.slot
    rest := fun j lo hi => ?_
    low := fun x below global out apart => (T.low x below global apart).trans (lowE x below out)
    live := fun e he x inside => by
      have bounds := ready.heap.block_bounds (q := e.1) (n := e.2) he
      unfold InExt at inside
      rw [T.live e he x (by unfold InExt; omega), S.kept x (Or.inl (by
        unfold nativeFrameBase; rw [spNat]; unfold nativeFrameBase heapEnd at *; omega)), keepD x (by
        simp only [OutW, fsWindows, and_true, nativeFrameBase, Layout.sym_files, Layout.sym_fds, Layout.sym_fs_ready,
          heapEnd, heapStart] at *
        omega)]
    high := fun n lo hi => (T.high n lo hi).trans ((S.high n lo hi).trans
      (p1.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp [fsPrefixWrites]; omega))) }⟩⟩
  have lowJ : Layout.sym_files + 56 * j < heapStart := by unfold heapStart Layout.sym_files; omega
  unfold slotUsed
  rw [T.low _ lowJ (by unfold allocGlobal InRange Layout.sym_files; omega)
    (Or.inr (by unfold slotOne; omega)), S.kept _ (Or.inl (by
      unfold nativeFrameBase; rw [spNat]
      unfold nativeFrameBase heapStart heapEnd at *; omega))]
  exact clearD j (by omega) hi
end OCaml.Vm.Boot.Startup
