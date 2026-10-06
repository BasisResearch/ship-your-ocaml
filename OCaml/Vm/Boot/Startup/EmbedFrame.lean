import OCaml.Vm.Boot.Startup.MainArgv
import OCaml.Vm.Boot.Startup.EnvironmentInitial
import OCaml.Vm.Boot.Startup.CustomCaller
import OCaml.Vm.Boot.WhileMinArgv
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-! The `.embed` region (argv, environment and the embedded files, including
the bytecode executable) lies between the allocator arena and the native
stack: [`__embed_start` = `__heap_end`, `__stack_top - __stack_size`).
Startup never writes it, so every byte keeps its loader value. The frame also
keeps the `environ` word, which main sets once to the embedded environment,
and `caml_verb_gc`, which stays zero without OCAMLRUNPARAM. -/

def embedLimit : Nat := Layout.sym_stack_top - Layout.sym_stack_size

def EmbedByte (a : Nat) : Prop := heapEnd ≤ a ∧ a < embedLimit

def EnvironByte (a : Nat) : Prop := Layout.sym_environ ≤ a ∧ a < Layout.sym_environ + 8

def VerbGcByte (a : Nat) : Prop := Layout.sym_caml_verb_gc ≤ a ∧ a < Layout.sym_caml_verb_gc + 8

/-- htif.c's file-system state that startup leaves untouched until the first
`open`: `fs_ready`, slots 1–63 of `files`, and newlib's `_impure_ptr`. -/
def HtifByte (a : Nat) : Prop :=
  (Layout.sym_fs_ready ≤ a ∧ a < Layout.sym_fs_ready + 4) ∨
    (Layout.sym_impure_ptr ≤ a ∧ a < Layout.sym_impure_ptr + 8) ∨
    (Layout.sym_files + 56 ≤ a ∧ a < Layout.sym_files + 56 * 64)

/-- Bytes no startup function writes after main. -/
def KeptByte (a : Nat) : Prop := EmbedByte a ∨ EnvironByte a ∨ VerbGcByte a ∨ HtifByte a

theorem HtifByte.bounds {a} (h : HtifByte a) : Layout.sym_impure_ptr ≤ a ∧ a < Layout.sym_files + 56 * 64 := by
  rcases h with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
    simp only [Layout.sym_fs_ready, Layout.sym_impure_ptr, Layout.sym_files] at * <;> omega

theorem HtifByte.not_alloc {a} (h : HtifByte a) : ¬ allocGlobal a := by
  unfold allocGlobal InRange
  rcases h with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
    simp only [Layout.sym_fs_ready, Layout.sym_impure_ptr, Layout.sym_files] at * <;> omega

theorem KeptByte.lt {a} (ha : KeptByte a) : a < embedLimit := by
  rcases ha with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | htif
  · exact h
  · unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size Layout.sym_environ at *; omega
  · unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size Layout.sym_caml_verb_gc at *; omega
  · have := htif.bounds; unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size Layout.sym_files at *; omega

/-- The kept low globals lie below the arena, outside the allocator's globals. -/
theorem KeptByte.low {a} (ha : KeptByte a) (below : a < heapEnd) : a < heapStart ∧ ¬ allocGlobal a := by
  rcases ha with ⟨low, _⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | htif
  · omega
  · unfold allocGlobal InRange heapStart
    unfold Layout.sym_environ at lo hi
    omega
  · unfold allocGlobal InRange heapStart
    unfold Layout.sym_caml_verb_gc at lo hi
    omega
  · exact ⟨by have := htif.bounds; unfold heapStart Layout.sym_files at *; omega, htif.not_alloc⟩

theorem KeptByte.not_foot {a H} (ha : KeptByte a) : ¬ vsaFoot H a := by
  intro owned
  by_cases below : a < heapEnd
  · have low := ha.low below
    rcases owned with global | ⟨lo, _⟩
    · exact low.2 global
    · unfold heapStart at *; omega
  · rcases ha with ⟨_, _⟩ | ⟨_, hi⟩ | ⟨_, hi⟩ | htif
    · have := allocator_foot_below owned; omega
    · unfold Layout.sym_environ heapEnd at *; omega
    · unfold Layout.sym_caml_verb_gc heapEnd at *; omega
    · have := htif.bounds; unfold Layout.sym_files heapEnd at *; omega

/-- Kept bytes avoid every low global from `startup_count` up to the arena
that also avoids htif.c's `files` table. -/
theorem KeptByte.out_low {a g n} (ha : KeptByte a) (lo : Layout.sym_startup_count ≤ g) (hi : g + n ≤ heapEnd)
    (files : g + n ≤ Layout.sym_files + 56 ∨ Layout.sym_files + 56 * 64 ≤ g) :
    a < g ∨ g + n ≤ a := by
  rcases ha with ⟨low, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ | htif
  · right; omega
  · left; unfold Layout.sym_environ Layout.sym_startup_count at *; omega
  · left; unfold Layout.sym_caml_verb_gc Layout.sym_startup_count at *; omega
  · rcases htif with ⟨l, h⟩ | ⟨l, h⟩ | ⟨l, h⟩ <;>
      simp only [Layout.sym_fs_ready, Layout.sym_impure_ptr, Layout.sym_files, Layout.sym_startup_count] at * <;> omega

structure EmbedFrame (before after : Config) : Prop where
  byte : ∀ a, KeptByte a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0

theorem EmbedFrame.trans {before middle after} (h : EmbedFrame before middle)
    (g : EmbedFrame middle after) : EmbedFrame before after :=
  ⟨fun a ha => (g.byte a ha).trans (h.byte a ha)⟩

theorem EmbedFrame.of_memory {before after} (memory : after.σ.mem = before.σ.mem) :
    EmbedFrame before after := ⟨fun _ _ => by rw [memory]⟩

theorem EmbedFrame.of_out {before after log} (memory : after.σ.mem = writeLog before.σ.mem log)
    (out : ∀ a, KeptByte a → OutL log a) : EmbedFrame before after :=
  ⟨fun a ha => by rw [memory, writeLog_out _ _ _ (out a ha)]⟩

/-- Every native frame of the startup path lies above the embed region. -/
theorem EmbedFrame.stack {before after log} {sp : BitVec 64} {size : Nat}
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (inside : LogInW [⟨nativeFrameBase sp size, sp.toNat⟩] log)
    (deep : embedLimit + size ≤ sp.toNat) : EmbedFrame before after := by
  constructor
  intro a ha
  rw [memory, frameOn_writeLog _ _ _ inside a ⟨Or.inl ?_, trivial⟩]
  have := ha.lt
  show a < nativeFrameBase sp size
  unfold nativeFrameBase
  omega

theorem StatCheckedReturned.embed_frame {H capacity sp ra s0 n before after}
    (w : StatCheckedReturned H capacity sp ra s0 n before after)
    (frame : NativeFrame sp 544) (deep : embedLimit + 544 ≤ sp.toNat) : EmbedFrame before after := by
  constructor
  intro a ha
  have short := frame.resize (small := 32) (by decide) (by decide)
  have unowned : ¬ mS H (nativeStack sp 32) a := by
    intro owned
    rcases owned with scratch | heap
    · have := ha.lt
      unfold stackWin InExt allocHeadroom at scratch
      rw [short.stack_nat] at scratch
      unfold nativeFrameBase at scratch
      omega
    · exact ha.not_foot heap
  have unchanged := w.allocation.allocation.memory a unowned
  change (w.allocated.σ.mem[a]?).getD 0 = (w.allocation.atMalloc.σ.mem[a]?).getD 0 at unchanged
  have restored : after.σ.mem = w.allocated.σ.mem := w.returned.memory
  rw [restored, unchanged, w.allocation.call.memory, w.allocation.setup.memory]
  have low : a < nativeFrameBase sp 32 := by
    have := ha.lt
    unfold nativeFrameBase
    omega
  rw [frameOn_writeLog _ _ _ (statCheckedLog_inside short) a ⟨Or.inl low, trivial⟩]

theorem CustomRegistered.embed_frame {H capacity kind sp s0 head before after}
    (w : CustomRegistered H capacity kind sp s0 head before after)
    (frame : NativeFrame sp 544) (deep : embedLimit + 544 ≤ sp.toNat) : EmbedFrame before after := by
  apply (w.allocation.embed_frame frame deep).trans
  apply EmbedFrame.of_out w.publication.memory
  intro a ha
  have region := w.region
  have node := ha.out_low (g := (vsaReg w.allocated 10).toNat) (n := 16)
    (Nat.le_trans (by decide) region.lower) region.upper
    (Or.inr (Nat.le_trans (by decide) region.lower))
  have table := ha.out_low (g := Layout.sym_custom_ops_table) (n := 8) (by decide) (by decide) (by decide)
  exact customPublish_out_byte region node table

theorem CustomNextRegistered.embed_frame {H capacity kind sp head before after}
    (w : CustomNextRegistered H capacity kind sp head before after)
    (frame : NativeFrame sp 544) (deep : embedLimit + 544 ≤ sp.toNat) : EmbedFrame before after :=
  (EmbedFrame.of_memory w.setup.memory).trans (w.registration.embed_frame frame deep)

theorem CustomReturned.embed_frame {H capacity sp ra s0 head before after}
    (w : CustomReturned H capacity sp ra s0 head before after)
    (frame : NativeFrame sp 560) (deep : embedLimit + 560 ≤ sp.toNat) : EmbedFrame before after := by
  have short := frame.resize (small := 16) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  have deep' : embedLimit + 544 ≤ (nativeStack sp 16).toNat := by
    rw [short.stack_nat]; unfold nativeFrameBase; omega
  have deep16 : embedLimit + 16 ≤ sp.toNat := Nat.le_trans (Nat.add_le_add_left (by decide) _) deep
  have first := EmbedFrame.stack (size := 16) w.nodes.int32.setup.memory (customSaveLog_inside short) deep16
  have call := EmbedFrame.of_memory (before := w.nodes.int32.saved) w.nodes.int32.call.memory
  have reg := w.nodes.int32.registration.embed_frame nested deep'
  have rest := (w.nodes.nativeint.embed_frame nested deep').trans
    ((w.nodes.int64.embed_frame nested deep').trans (w.nodes.bigarray.embed_frame nested deep'))
  exact (first.trans (call.trans (reg.trans rest))).trans
    (EmbedFrame.of_memory w.post.memory)

theorem ExtTableReturned.embed_frame {H capacity sp ra s0 t n before after}
    (w : ExtTableReturned H capacity sp ra s0 t n before after)
    (frame : NativeFrame sp 560) (site : ExtTableSite sp t) (deep : embedLimit + 560 ≤ sp.toNat) :
    EmbedFrame before after := by
  have short := frame.resize (small := 16) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  have deep' : embedLimit + 544 ≤ (nativeStack sp 16).toNat := by
    rw [short.stack_nat]; unfold nativeFrameBase; omega
  have header (a : Nat) (ha : KeptByte a) : a < t.toNat ∨ t.toNat + Layout.ext_table_bytes ≤ a := by
    have := ha.lt
    rcases site.place with ⟨above, _⟩ | g
    · left; unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size at *; omega
    · exact ha.out_low g.low (Nat.le_trans g.high (by decide)) g.files
  have setup : EmbedFrame before w.allocation.saved := by
    constructor
    intro a ha
    rw [w.allocation.setup.memory, frameOn_writeLog _ _ _ (extTableLog_inside short) a ?_]
    have := ha.lt
    have h := header a ha
    exact ⟨Or.inl (by show a < nativeFrameBase sp 16; unfold nativeFrameBase; omega), h, trivial⟩
  have call := EmbedFrame.of_memory (before := w.allocation.saved) w.allocation.call.memory
  have alloc := w.allocation.allocation.embed_frame nested deep'
  have publish : EmbedFrame w.allocated w.published := by
    apply EmbedFrame.of_out w.publication.memory
    intro a ha
    have h := header a ha
    simp only [extTablePublishLog, OutL]
    unfold Layout.off_ext_table_contents Layout.ext_table_bytes at *
    exact ⟨by omega, trivial⟩
  exact (setup.trans (call.trans (alloc.trans publish))).trans
    (EmbedFrame.of_memory w.post.memory)
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.VsaHeap OCaml.Vm.Primitives

theorem StartupDataFrame.embed {before after} (h : StartupDataFrame before after) :
    EmbedFrame before after := by
  constructor
  intro a ha
  apply h.byte a
  rcases ha with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | htif
  · exact Or.inr ⟨lo, by unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size at *; omega⟩
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · unfold Layout.sym_environ heapStart at *; omega
    · unfold allocGlobal InRange; unfold Layout.sym_environ at lo hi; omega
    · left; unfold Layout.sym_environ Layout.sym_Caml_state at *; omega
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · unfold Layout.sym_caml_verb_gc heapStart at *; omega
    · unfold allocGlobal InRange; unfold Layout.sym_caml_verb_gc at lo hi; omega
    · left; unfold Layout.sym_caml_verb_gc Layout.sym_Caml_state at *; omega
  · have b := htif.bounds
    refine Or.inl ⟨by unfold heapStart Layout.sym_files at *; omega, htif.not_alloc, ?_⟩
    rcases htif with ⟨l, h⟩ | ⟨l, h⟩ | ⟨l, h⟩ <;>
      simp only [Layout.sym_fs_ready, Layout.sym_impure_ptr, Layout.sym_files, Layout.sym_Caml_state] at * <;> omega

/-- Every embed byte still has its loader value. -/
structure EmbedImage (c : Config) : Prop where
  byte : ∀ a, EmbedByte a → (c.σ.mem[a]?).getD 0 = (WhileMinImage.initialMem[a]?).getD 0

theorem EmbedImage.frame {before after} (h : EmbedImage before) (f : EmbedFrame before after) :
    EmbedImage after := ⟨fun a ha => (f.byte a (Or.inl ha)).trans (h.byte a ha)⟩

/-- The embedded image only needs its own bytes kept. -/
theorem EmbedImage.of_bytes {before after} (h : EmbedImage before)
    (f : ∀ a, EmbedByte a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0) : EmbedImage after :=
  ⟨fun a ha => (f a ha).trans (h.byte a ha)⟩

/-- The embedded image together with main's `environ` publication and the
zero GC verbosity. -/
structure KeptImage (c : Config) : Prop where
  embed : EmbedImage c
  environ : bytesT c.σ.mem Layout.sym_environ 8 = BitVec.ofNat 64 WhileMinImage.envArray
  verbGc : LPins8 c.σ.mem Layout.sym_caml_verb_gc (List.replicate 8 0#8)

/-- The `environ` global survives every kept frame. -/
theorem EmbedFrame.environ {before after v} (f : EmbedFrame before after)
    (h : bytesT before.σ.mem Layout.sym_environ 8 = v) : bytesT after.σ.mem Layout.sym_environ 8 = v :=
  (word_observed _ (fun i hi => f.byte _ (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans h

theorem EmbedFrame.verbGc {before after bytes} (f : EmbedFrame before after)
    (h : LPins8 before.σ.mem Layout.sym_caml_verb_gc bytes) : LPins8 after.σ.mem Layout.sym_caml_verb_gc bytes :=
  lpins8_observed h (fun i hi => f.byte _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))

theorem KeptImage.frame {before after} (h : KeptImage before) (f : EmbedFrame before after) :
    KeptImage after := ⟨h.embed.frame f, f.environ h.environ, f.verbGc h.verbGc⟩
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup OCaml.Vm.Primitives

theorem ResetCamlMainWitness.embed {initial atMain : Config}
    (w : ResetCamlMainWitness initial atMain) : EmbedImage atMain := by
  constructor
  intro a ha
  have low := ha.1
  have high := ha.2
  rw [w.post.memory, writeLog_out _ _ _ ?_, clearWords_above _ _ _ _ ?_]
  · exact reset_total_byte w.reset a
  · have bound : Layout.sym_bss_start + 8 * bssWords ≤ heapEnd := by decide
    omega
  · change (a < Layout.sym_stack_top - 8 ∨ Layout.sym_stack_top ≤ a) ∧
      (a < Layout.sym_environ ∨ Layout.sym_environ + 8 ≤ a) ∧ True
    unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size Layout.sym_environ heapEnd at *
    exact ⟨Or.inl (by omega), Or.inr (by omega), trivial⟩

theorem ResetParameterEntry.embed {initial entry} (w : ResetParameterEntry initial entry) :
    EmbedImage entry :=
  w.domain.witness.tables.third.first.published.allocation.before.request.tables.allocation.before.alloc.domain.main.embed.frame
    w.data_frame.embed

theorem ResetParameterEntry.verb_gc {initial entry} (w : ResetParameterEntry initial entry) :
    LPins8 entry.σ.mem Layout.sym_caml_verb_gc (List.replicate 8 0#8) := by
  have main := w.domain.witness.tables.third.first.published.allocation.before.request.tables.allocation.before.alloc.domain.main.post.toCrtCamlMainPost
  have bounds : Layout.sym_bss_start ≤ Layout.sym_caml_verb_gc ∧
      Layout.sym_caml_verb_gc + 8 ≤ Layout.sym_bss_start + 8 * bssWords ∧
      Layout.sym_environ + 8 ≤ Layout.sym_caml_verb_gc ∧
      Layout.sym_caml_verb_gc + 8 ≤ Layout.sym_stack_top - 8 := by decide
  have zero (i : Nat) (hi : i < 8) : (entry.σ.mem[Layout.sym_caml_verb_gc + i]?).getD 0 = 0#8 := by
    rw [w.data_frame.byte _ (show StartupDataBytes (Layout.sym_caml_verb_gc + i) from by
        refine Or.inl ⟨?_, ?_, ?_⟩
        · unfold Layout.sym_caml_verb_gc heapStart; omega
        · unfold VsaIris.VsaHeap.allocGlobal VsaIris.VsaHeap.InRange Layout.sym_caml_verb_gc; omega
        · left; unfold Layout.sym_caml_verb_gc Layout.sym_Caml_state; omega)]
    exact main.bss_byte _ (by omega) (by omega) (mainWrites_between _ _ _ (by omega) (by omega))
  exact ⟨by simpa using zero 0 (by decide), zero 1 (by decide), zero 2 (by decide), zero 3 (by decide),
    zero 4 (by decide), zero 5 (by decide), zero 6 (by decide), zero 7 (by decide)⟩

theorem ResetParameterEntry.kept {initial entry} (w : ResetParameterEntry initial entry) :
    KeptImage entry := ⟨w.embed, w.environment.global, w.verb_gc⟩

theorem ResetParameterReturned.kept {initial after} (w : ResetParameterReturned initial after) :
    KeptImage after :=
  w.before.kept.frame (EmbedFrame.stack (size := 176) w.post.memory
    (parameterPresentLog_inside (by constructor <;> decide)) (by decide))

theorem ResetCustomEntry.kept {initial entry} (w : ResetCustomEntry initial entry) :
    KeptImage entry := by
  have auxFrame : NativeFrame parameterStack 16 := by constructor <;> decide
  have aux : EmbedFrame w.auxiliary.called w.source := by
    constructor
    intro a ha
    have high := ha.lt
    rw [w.auxiliary.post.memory, startupAuxLog, writeLog_append,
      writeLog_out _ _ _ (show OutL [(Layout.sym_startup_count, 4, 1#64)] a from
        ⟨ha.out_low (Nat.le_refl _) (by decide) (by decide), trivial⟩),
      frameOn_writeLog _ _ _ (startupAuxSave_inside auxFrame) a ⟨Or.inl ?_, trivial⟩]
    show a < nativeFrameBase parameterStack 16
    have bound : embedLimit ≤ nativeFrameBase parameterStack 16 := by decide
    omega
  have source := (w.auxiliary.parameter.kept.frame (EmbedFrame.of_memory w.auxiliary.call.memory)).frame aux
  exact (source.frame (EmbedFrame.stack (size := Layout.camlMainFrameBytes) w.locale.memory
    (camlLocaleLog_inside (by constructor <;> decide)) (by decide))).frame
    (EmbedFrame.of_memory w.call.memory)

theorem ResetSharedTableReturned.kept {initial after} (w : ResetSharedTableReturned initial after) :
    KeptImage after := by
  have frame : NativeFrame parameterStack 560 := by constructor <;> decide
  have custom := w.custom.source.source.kept.frame (w.custom.returned.embed_frame frame (by decide))
  exact (custom.frame (EmbedFrame.of_memory w.call.memory)).frame
    (w.returned.embed_frame frame (ExtTableSite.shared _) (by decide))

theorem ResetSharedTableReturned.embed {initial after} (w : ResetSharedTableReturned initial after) :
    EmbedImage after := w.kept.embed
end OCaml.Vm.Boot.WhileMinElfParse

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem EmbedImage.word {c} (h : EmbedImage c) (a : Nat) (inside : ∀ i, i < 8 → EmbedByte (a + i)) :
    bytesT c.σ.mem a 8 = bytesT WhileMinImage.initialMem a 8 :=
  word_observed a (fun i hi => h.byte _ (inside i hi))

/-- The embedded argv table: pointer words read back from any startup state. -/
theorem EmbedImage.argv_word {c} (h : EmbedImage c) (k : Nat) (small : k ≤ WhileMinImage.argvCount) :
    bytesT c.σ.mem (WhileMinImage.argvArray + 8 * k) 8 =
      bytesT WhileMinImage.initialMem (WhileMinImage.argvArray + 8 * k) 8 := by
  apply h.word
  intro i hi
  unfold EmbedByte embedLimit WhileMinImage.argvArray WhileMinImage.argvCount Layout.sym_stack_top
    Layout.sym_stack_size Vsa.Sim.DlHeap.heapEnd at *
  omega
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup OCaml.Vm.Primitives

/-- caml_main's argv is the embedded command-line array. -/
theorem resetArgv_value {initial : Config} (reset : ElfResetReady elf initial) :
    resetArgv initial = BitVec.ofNat 64 WhileMinImage.argvArray := by
  unfold resetArgv
  rw [read8_value]
  exact (word_observed _ (fun i _ => reset_total_byte reset _)).trans WhileMinImage.argv_header

theorem ResetSharedTableReturned.argv_array {initial after} (w : ResetSharedTableReturned initial after) :
    gprGet after.σ 9 = some (BitVec.ofNat 64 WhileMinImage.argvArray) := by
  rw [w.argv, resetArgv_value w.reset]
end OCaml.Vm.Boot.WhileMinElfParse
