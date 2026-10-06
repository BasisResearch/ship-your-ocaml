import OCaml.Vm.Boot.Startup.FsInitSteps
import OCaml.Vm.Boot.Startup.FsInitPath
import OCaml.Vm.Sim.AllocInput
import OCaml.Vm.Sim.FreshLog
import OCaml.Vm.Boot.Startup.ChildScan
import OCaml.Vm.Boot.Startup.RuntimeStack
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris OCaml.Vm.Primitives

/-! htif.c's `fs_init()` over the embedded table: the windows it writes outside
`new_node` (its frame, the `files` table, the three descriptors, `fs_ready`),
and the run from its entry to the `strchr` call. -/

def fsFilesWindow : W := ⟨Layout.sym_files, Layout.sym_files + 56 * 64⟩

def fsWindows (sp : BitVec 64) : List W :=
  [⟨nativeFrameBase sp 96, sp.toNat⟩, fsFilesWindow, ⟨Layout.sym_fds, Layout.sym_fds + 52⟩,
    ⟨Layout.sym_fs_ready, Layout.sym_fs_ready + 4⟩]

theorem fsWindows_stack {sp : BitVec 64} {log : List WEntry}
    (inside : LogInW [⟨nativeFrameBase sp 96, sp.toNat⟩] log) : LogInW (fsWindows sp) log :=
  OCaml.Vm.Sim.logInW_mono inside fun w hw => by simp at hw; simp [fsWindows, hw]

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
      exact ⟨Or.inr (Or.inl ⟨Nat.le_refl _, by unfold Layout.sym_files; omega⟩), trivial⟩)

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
    fun x out => ?_⟩
  rw [p6.memory, show writeLog e5.σ.mem [] = e5.σ.mem from rfl, p5.memory,
    frameOn_writeLog _ _ _ (childLog_inside inner) x ⟨out, trivial⟩, same4]
end OCaml.Vm.Boot.Startup
