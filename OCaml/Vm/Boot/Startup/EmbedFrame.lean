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
Startup never writes it, so every byte keeps its loader value. -/

def embedLimit : Nat := Layout.sym_stack_top - Layout.sym_stack_size

def EmbedByte (a : Nat) : Prop := heapEnd ≤ a ∧ a < embedLimit

structure EmbedFrame (before after : Config) : Prop where
  byte : ∀ a, EmbedByte a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0

theorem EmbedFrame.trans {before middle after} (h : EmbedFrame before middle)
    (g : EmbedFrame middle after) : EmbedFrame before after :=
  ⟨fun a ha => (g.byte a ha).trans (h.byte a ha)⟩

theorem EmbedFrame.of_memory {before after} (memory : after.σ.mem = before.σ.mem) :
    EmbedFrame before after := ⟨fun _ _ => by rw [memory]⟩

theorem EmbedFrame.of_out {before after log} (memory : after.σ.mem = writeLog before.σ.mem log)
    (out : ∀ a, EmbedByte a → OutL log a) : EmbedFrame before after :=
  ⟨fun a ha => by rw [memory, writeLog_out _ _ _ (out a ha)]⟩

/-- Every native frame of the startup path lies above the embed region. -/
theorem EmbedFrame.stack {before after log} {sp : BitVec 64} {size : Nat}
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (inside : LogInW [⟨nativeFrameBase sp size, sp.toNat⟩] log)
    (deep : embedLimit + size ≤ sp.toNat) : EmbedFrame before after := by
  constructor
  intro a ha
  rw [memory, frameOn_writeLog _ _ _ inside a ⟨Or.inl ?_, trivial⟩]
  have := ha.2
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
    · have := ha.2
      unfold stackWin InExt allocHeadroom at scratch
      rw [short.stack_nat] at scratch
      unfold nativeFrameBase at scratch
      omega
    · have := allocator_foot_below heap
      have := ha.1
      omega
  have unchanged := w.allocation.allocation.memory a unowned
  change (w.allocated.σ.mem[a]?).getD 0 = (w.allocation.atMalloc.σ.mem[a]?).getD 0 at unchanged
  have restored : after.σ.mem = w.allocated.σ.mem := w.returned.memory
  rw [restored, unchanged, w.allocation.call.memory, w.allocation.setup.memory]
  have low : a < nativeFrameBase sp 32 := by
    have := ha.2
    unfold nativeFrameBase
    omega
  rw [frameOn_writeLog _ _ _ (statCheckedLog_inside short) a ⟨Or.inl low, trivial⟩]

theorem CustomRegistered.embed_frame {H capacity kind sp s0 head before after}
    (w : CustomRegistered H capacity kind sp s0 head before after)
    (frame : NativeFrame sp 544) (deep : embedLimit + 544 ≤ sp.toNat) : EmbedFrame before after := by
  apply (w.allocation.embed_frame frame deep).trans
  apply EmbedFrame.of_out w.publication.memory
  intro a ha
  have high := w.region.upper
  have low := ha.1
  unfold heapEnd at high low
  exact customPublish_out_byte w.region (Or.inr (by omega))
    (Or.inr (by unfold Layout.sym_custom_ops_table; omega))

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
  have header (a : Nat) (ha : EmbedByte a) : a < t.toNat ∨ t.toNat + Layout.ext_table_bytes ≤ a := by
    have := ha.2
    have := ha.1
    rcases site.place with ⟨above, _⟩ | g
    · left; unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size at *; omega
    · right; have := g.high; unfold heapStart heapEnd at *; omega
  have setup : EmbedFrame before w.allocation.saved := by
    constructor
    intro a ha
    rw [w.allocation.setup.memory, frameOn_writeLog _ _ _ (extTableLog_inside short) a ?_]
    have := ha.2
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
open Vsa.Machine Vsa.Sim

theorem StartupDataFrame.embed {before after} (h : StartupDataFrame before after) :
    EmbedFrame before after :=
  ⟨fun a ha => h.byte a (Or.inr ⟨ha.1, by
    have := ha.2
    unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size at *
    omega⟩)⟩

/-- Every embed byte still has its loader value. -/
structure EmbedImage (c : Config) : Prop where
  byte : ∀ a, EmbedByte a → (c.σ.mem[a]?).getD 0 = (WhileMinImage.initialMem[a]?).getD 0

theorem EmbedImage.frame {before after} (h : EmbedImage before) (f : EmbedFrame before after) :
    EmbedImage after := ⟨fun a ha => (f.byte a ha).trans (h.byte a ha)⟩
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

theorem ResetParameterReturned.embed {initial after} (w : ResetParameterReturned initial after) :
    EmbedImage after :=
  w.before.embed.frame (EmbedFrame.stack (size := 176) w.post.memory
    (parameterPresentLog_inside (by constructor <;> decide)) (by decide))

theorem ResetCustomEntry.embed {initial entry} (w : ResetCustomEntry initial entry) :
    EmbedImage entry := by
  have auxFrame : NativeFrame parameterStack 16 := by constructor <;> decide
  have aux : EmbedFrame w.auxiliary.called w.source := by
    constructor
    intro a ha
    have high := ha.2
    have low := ha.1
    rw [w.auxiliary.post.memory, startupAuxLog, writeLog_append,
      writeLog_out _ _ _ (show OutL [(Layout.sym_startup_count, 4, 1#64)] a from ⟨Or.inr (by
        show Layout.sym_startup_count + 4 ≤ a
        unfold Layout.sym_startup_count heapEnd at *; omega), trivial⟩),
      frameOn_writeLog _ _ _ (startupAuxSave_inside auxFrame) a ⟨Or.inl ?_, trivial⟩]
    show a < nativeFrameBase parameterStack 16
    have bound : embedLimit ≤ nativeFrameBase parameterStack 16 := by decide
    omega
  have source := (w.auxiliary.parameter.embed.frame (EmbedFrame.of_memory w.auxiliary.call.memory)).frame aux
  exact (source.frame (EmbedFrame.stack (size := Layout.camlMainFrameBytes) w.locale.memory
    (camlLocaleLog_inside (by constructor <;> decide)) (by decide))).frame
    (EmbedFrame.of_memory w.call.memory)

theorem ResetSharedTableReturned.embed {initial after} (w : ResetSharedTableReturned initial after) :
    EmbedImage after := by
  have frame : NativeFrame parameterStack 560 := by constructor <;> decide
  have custom := w.custom.source.source.embed.frame (w.custom.returned.embed_frame frame (by decide))
  exact (custom.frame (EmbedFrame.of_memory w.call.memory)).frame
    (w.returned.embed_frame frame (ExtTableSite.shared _) (by decide))
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
