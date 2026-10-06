import OCaml.Vm.Boot.Startup.FsInitSteps
import OCaml.Vm.Boot.Startup.FsInitPath
import OCaml.Vm.Sim.AllocInput
import OCaml.Vm.Sim.FreshLog
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
end OCaml.Vm.Boot.Startup
