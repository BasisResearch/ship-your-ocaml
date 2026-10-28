import OCaml.Vm.Boot.Startup.BacktraceReset
import OCaml.Vm.Boot.Startup.InterpreterInit

namespace OCaml.Vm.Boot.WhileMinElfParse
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives Startup
open VsaIris VsaIris.VsaHeap

/-- Exact heap ledger retained after first-root registration. -/
abbrev ResetBacktrace.blocks {initial after} (B : ResetBacktrace initial after) : List (Nat × Nat) :=
  (B.done.inserted.native.p.toNat,24) :: (B.raw.toNat,8192) :: B.H

/-- Initialization needs only the already produced backtrace return. -/
theorem ResetBacktrace.interpreter_input {initial after} (B : ResetBacktrace initial after) :
    InterpreterInitInput B.blocks backtraceCapacity jal_80004e80_call.link after :=
  ⟨B.done.pc,B.done.ready⟩

/-- Reset to the debugger return, retaining the real backtrace and descriptor/fd/argv history. -/
structure ResetInterpreterInit (initial after : Config) where
  reset : ElfResetReady elf initial
  atBacktrace : Config
  source : ResetBacktrace initial atBacktrace
  source_run : Steps atBacktrace after
  done : InterpreterInitDone source.blocks backtraceCapacity atBacktrace after
  run : Steps (Vsa.Densify.fillZero initial) after

/-- The native CODE-section lookup starts here; this does not assert `Loaded`. -/
theorem ResetInterpreterInit.next_pc {initial after} (I : ResetInterpreterInit initial after) :
    PCAt 0x80004e94#64 after := I.done.pc

/-- Explicit access to the executed descriptor-reading ancestor and its actual file/argv producer chain. -/
def ResetInterpreterInit.sections {initial after} (I : ResetInterpreterInit initial after) :
    ResetReadSections initial I.source.source.source.sections := I.source.source.source.source

/-- The retained descriptor ancestor lies on the executed continuation to this return. -/
theorem ResetInterpreterInit.from_sections {initial after} (I : ResetInterpreterInit initial after) :
    Steps I.source.source.source.sections after :=
  I.source.source.source.source_run.trans
    (I.source.source.source_run.trans (I.source.source_run.trans I.source_run))

/-- The CODE lookup consumes the real fd=3/argv bank, kept by the native ABI. -/
theorem ResetInterpreterInit.load_caller {initial after} (I : ResetInterpreterInit initial after) :
    LoadCaller after := I.source.loadCaller.frame I.done.abi (by decide) (by decide)

/-- The GC argument words are excluded; the later trailer is framed by execution. -/
theorem ResetInterpreterInit.caller_frame {initial after} (I : ResetInterpreterInit initial after) :
    CallerFrame (parameterStack + 16#64) I.source.source.source.sections after :=
  I.source.caller_frame.trans (I.done.caller.weaken (by decide))

/-- Current trailer pointer, obtained from the actual descriptor return and frames. -/
theorem ResetInterpreterInit.table_pointer {initial after} (I : ResetInterpreterInit initial after) :
    bytesT after.σ.mem (trailSlot + 16#64).toNat 8 = I.sections.blk := by
  rw [word_observed (m := I.source.source.source.sections.σ.mem) _ fun i hi =>
    I.caller_frame.byte _ (by
      have : (parameterStack + 16#64).toNat ≤ (trailSlot + 16#64).toNat := by decide
      omega)]
  exact I.sections.done.blkWord

/-- Current section count, obtained from the same executed caller frame. -/
theorem ResetInterpreterInit.num_sections {initial after} (I : ResetInterpreterInit initial after) :
    read4 after.σ.mem trailSlot.toNat = sectionsWord := by
  rw [read4_observed (m := I.source.source.source.sections.σ.mem) _ fun i hi =>
    I.caller_frame.byte _ (by
      have : (parameterStack + 16#64).toNat ≤ trailSlot.toNat := by decide
      omega)]
  exact I.sections.done.numWord

/-- The selected descriptor allocation remains owned by the current heap ledger. -/
theorem ResetInterpreterInit.descriptors_owned {initial after} (I : ResetInterpreterInit initial after) :
    (I.sections.blk.toNat, 56) ∈ I.source.blocks :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (I.source.sourceOwned _ (List.mem_cons_self ..)))

/-- Interpreter stores preserve the owned descriptors from the backtrace return.
The earlier GC/atom descriptor frame is still a separate obligation. -/
theorem ResetInterpreterInit.descriptors_live {initial after} (I : ResetInterpreterInit initial after) :
    LiveFrame [(I.sections.blk.toNat, 56)] I.atBacktrace after :=
  I.done.live.mono fun e he => by
    rw [List.mem_singleton.mp he]
    exact I.descriptors_owned

/-- The registered domain root still contains the actually initialized tagged unit. -/
theorem ResetInterpreterInit.last_exn {initial after} (I : ResetInterpreterInit initial after) :
    bytesT after.σ.mem Gc.SkiplistFirst.startupKey.toNat 8 = 1#64 := by
  have inside (i : Nat) (hi : i < 8) :
      InExt (firstDomainPtr.toNat,928) (Gc.SkiplistFirst.startupKey.toNat + i) := by
    have key : Gc.SkiplistFirst.startupKey.toNat = firstDomainPtr.toNat + 256 := by decide
    rw [key]
    constructor <;> dsimp only <;> omega
  rw [word_observed (m := I.atBacktrace.σ.mem) _ fun i hi =>
    I.done.live.byte _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ I.source.atomDone.domainOwned)) _
      (inside i hi)]
  exact I.source.last_exn

/-- The native page-table header and owned entries survive the interpreter saves. -/
theorem ResetInterpreterInit.page_table {initial after} (I : ResetInterpreterInit initial after) :
    MajorTableAt I.source.blocks after.σ.mem I.source.ent := by
  have T := I.source.page_table
  apply T.agree
  intro x hx
  rcases hx with ⟨lo,hi⟩ | ⟨lo,hi⟩
  · apply I.done.below
    have bound : 0x800684e0 ≤ nativeFrameBase parameterStack Layout.interpFrameBytes := by decide
    rw [show pageTable = 0x800684b8 by decide] at lo hi
    omega
  · exact I.done.live.byte _ T.owned x ⟨lo,hi⟩

/-- The universal reset prefix now includes interpreter and debugger initialization. -/
theorem reset_interpreter_init (initial : Config) (reset : ElfReset elf initial) :
    ∃ after, Nonempty (ResetInterpreterInit initial after) := by
  obtain ⟨before,⟨B⟩⟩ := reset_init_backtrace initial reset
  obtain ⟨after,run,⟨D⟩⟩ := interpreter_debugger_init before B.blocks backtraceCapacity _ B.interpreter_input
  exact ⟨after,⟨⟨B.reset,before,B,run,D,B.run.trans run⟩⟩⟩

/-- Same parsed-image/reset interface as `whileMin_reset_backtrace`. -/
theorem whileMin_reset_interpreter_init {imageElf : ELF64File}
    (image : WhileMinElf imageElf) (initial : Config) (reset : ElfReset imageElf initial) :
    ∃ after, Nonempty (ResetInterpreterInit initial after) :=
  reset_interpreter_init initial (reset.of_whileMinElf image whileMin_elf)

/-- Remaining actual native work: CODE/primitive/DATA loading, promotion and
system/argv initialization, then representation at the interpreter-entry cut.
The descriptor ancestor is retained, but no unproved frame from it is assumed. -/
def interpreter_init_loaded_Statement : Prop :=
  ∀ initial after, ResetInterpreterInit initial after →
    ∃ cut, Steps after cut ∧
      Loaded (runtimeLayout BestFitSingleton OCaml.Vm.Gc.g1Budget) OCaml.Programs.whileMin cut

theorem whileMin_reset_loaded_of_interpreter_init (continuation : interpreter_init_loaded_Statement) :
    whileMin_reset_loaded_Statement := by
  intro imageElf image initial reset
  obtain ⟨after,⟨I⟩⟩ := whileMin_reset_interpreter_init image initial reset
  obtain ⟨cut,run,loaded⟩ := continuation initial after I
  exact ⟨cut,I.run.trans run,loaded⟩

end OCaml.Vm.Boot.WhileMinElfParse
