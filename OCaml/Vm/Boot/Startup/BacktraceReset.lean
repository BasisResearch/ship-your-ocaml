import OCaml.Vm.Boot.Startup.Backtrace
import OCaml.Vm.Boot.Startup.AtomTableReset

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives Startup

/-- Remaining allocation room after the first global-root cell. -/
def backtraceCapacity : Nat := startupAllocatorCredits - 656 - initGcCredits - 32768 - 8192 - 32

/-- The actual reset prefix, atom return, backtrace call and global-root insertion. -/
structure ResetBacktrace (initial after : Config) where
  reset : ElfResetReady elf initial
  atoms : Config
  source : ResetAtomTable initial atoms
  source_run : Steps atoms after
  loadCaller : LoadCaller after
  H : List (Nat × Nat)
  sourceOwned : ∀ e ∈ source.source.source.blocks, e ∈ H
  ent : BitVec 64
  raw : BitVec 64
  beforeAtoms : Config
  atomDone : AtomTableReset H (startupAllocatorCredits - 656 - initGcCredits - 32768 - 8192)
    parameterStack jal_80004e7c_call.link ent raw beforeAtoms atoms
  atCall : Config
  a0 : BitVec 64
  call : RegistersPost [1] atoms.σ.mem atoms jal_80004e80_call.target a0
    [(1,jal_80004e80_call.link),(10,a0)] atCall
  done : BacktraceDone ((raw.toNat,8192) :: H) backtraceCapacity parameterStack jal_80004e80_call.link atCall after
  run : Steps (Vsa.Densify.fillZero initial) after

/-- The selected original loader allocations survive the actual root insertion. -/
theorem ResetBacktrace.selected_live {initial after} (B : ResetBacktrace initial after) :
    LiveFrame B.source.source.source.keptBlocks B.source.source.sections after := by
  have owned (e : Nat × Nat) (he : e ∈ B.source.source.source.keptBlocks) : e ∈ ((B.raw.toNat,8192) :: B.H) :=
    List.mem_cons_of_mem _ (B.sourceOwned e (B.source.source.source.kept_owned e he))
  have selection : Gc.SkiplistFirst.Selected ((B.raw.toNat,8192) :: B.H) B.source.source.source.keptBlocks := by
    constructor
    · exact owned
    · intro e he; exact (B.done.inserted.ready.block_bounds (List.mem_cons_of_mem _ (owned e he))).1
    · intro e he; exact (B.done.inserted.ready.block_bounds (List.mem_cons_of_mem _ (owned e he))).2
    · intro e he
      simp only [ResetReadSections.keptBlocks, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> dsimp only <;> decide
  exact B.source.selectedLive.trans ((LiveFrame.of_memory B.call.memory).trans
    (B.done.selected_live selection (by constructor <;> decide)))

/-- The descriptor projection of the selected original loader allocations. -/
theorem ResetBacktrace.descriptors_live {initial after} (B : ResetBacktrace initial after) :
    LiveFrame [(B.source.source.source.blk.toNat,56)] B.source.source.sections after :=
  B.selected_live.mono fun e he => by
    obtain rfl := List.mem_singleton.mp he
    exact List.mem_cons_self ..

/-- HTIF records and fd positions are kept by the actual root insertion. -/
theorem ResetBacktrace.htif {initial after} (B : ResetBacktrace initial after) :
    MemSame B.source.source.sections after HtifByte := by
  constructor
  intro x h
  have low := h.bounds
  rw [B.done.inserted.native.low_kept (by constructor <;> decide) x
    (by simp only [Layout.sym_files, heapStart] at low ⊢; omega) h.not_alloc
    (by
      rcases h with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
        simp only [Layout.sym_fs_ready, Layout.sym_impure_ptr, Layout.sym_files, Layout.sym_print_config,
          Layout.sym_fds, Gc.Skiplist.randomSeed] at * <;> omega)
    (by
      rcases h with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
        simp only [Layout.sym_fs_ready, Layout.sym_impure_ptr, Layout.sym_files, Layout.sym_print_config,
          Layout.sym_fds, Gc.Skiplist.globalRoots] at * <;> omega), B.done.memory, B.call.memory]
  exact B.source.htif.same x h

/-- Embedded bytes are framed along the actual root-insertion execution. -/
theorem ResetBacktrace.embed {initial after} (B : ResetBacktrace initial after) : EmbedImage after :=
  B.source.embed.of_bytes fun x hx => by
    rw [B.done.inserted.native.high_kept (by constructor <;> decide) x hx.1
      (by have := hx.stack_room; omega), B.done.memory, B.call.memory]

/-- The explicit next native instruction initializes the interpreter arguments. -/
theorem ResetBacktrace.next_pc {initial after} (B : ResetBacktrace initial after) : PCAt 0x80004e84#64 after :=
  B.done.pc

/-- The whole native continuation keeps the domain record from the atom return. -/
theorem ResetBacktrace.domain_live {initial after} (B : ResetBacktrace initial after) :
    LiveFrame Gc.SkiplistFirst.startupBlocks B.atoms after :=
  (LiveFrame.of_memory B.call.memory).trans B.done.live

/-- Trailer bytes survive the actual backtrace tail calls and root insertion. -/
theorem ResetBacktrace.caller_frame {initial after} (B : ResetBacktrace initial after) :
    CallerFrame (parameterStack + 16#64) B.source.source.sections after :=
  B.source.caller.trans (((CallerFrame.of_memory B.call.memory).trans
    (B.done.caller_frame (by constructor <;> decide))).weaken (by decide))

/-- The first insertion preserves both the native page-table header and its
selected owned entry block; the allocator ledger also retains the new cell. -/
theorem ResetBacktrace.page_table {initial after} (B : ResetBacktrace initial after) :
    MajorTableAt ((B.done.inserted.native.p.toNat,24) :: (B.raw.toNat,8192) :: B.H) after.σ.mem B.ent := by
  have T := B.atomDone.done.table
  have selection : Gc.SkiplistFirst.Selected ((B.raw.toNat,8192) :: B.H) [(B.ent.toNat,16384)] := by
    constructor
    · intro e he; obtain rfl := List.mem_singleton.mp he; exact T.owned
    · intro e he; obtain rfl := List.mem_singleton.mp he; exact T.high
    · intro e he; obtain rfl := List.mem_singleton.mp he; exact T.low
    · intro e he; obtain rfl := List.mem_singleton.mp he; exact (show 0 < (16384 : Nat) by decide)
  have frame : NativeFrame parameterStack Gc.Skiplist.opStack := by constructor <;> decide
  have live := B.done.selected_live selection frame
  apply (T.agree ?_).cons _
  intro x inT
  rcases inT with ⟨lo,hi⟩ | ⟨lo,hi⟩
  · have range : 0x800684b8 ≤ x ∧ x < 0x800684e0 := ⟨lo,hi⟩
    have kept := B.done.inserted.native.low_kept frame x
      (by unfold heapStart; omega)
      (by unfold allocGlobal InRange; omega)
      (Or.inr (by unfold Gc.Skiplist.randomSeed; omega))
      (Or.inl (by unfold Gc.Skiplist.globalRoots; omega))
    rw [kept, B.done.memory, B.call.memory]
  · rw [live.byte _ (List.mem_singleton_self _) x ⟨lo,hi⟩, B.call.memory]

/-- The registered root points to the executed domain initializer's tagged unit. -/
theorem ResetBacktrace.last_exn {initial after} (B : ResetBacktrace initial after) :
    bytesT after.σ.mem Gc.SkiplistFirst.startupKey.toNat 8 = 1#64 := by
  rw [B.done.keyKept, B.call.memory,
    show Gc.SkiplistFirst.startupKey.toNat = domainField backtrace_last_exnOffset by decide]
  exact B.atomDone.lastExn

/-- No initial heap, root-header, seed, domain-ownership or capacity assumptions:
they are supplied by the checked reset producer before taking the actual call. -/
theorem reset_init_backtrace_returned_exists :
    ∃ initial after, Nonempty (ResetBacktrace initial after) := by
  obtain ⟨initial, d, ⟨atoms⟩⟩ := reset_init_atom_table_witness_exists
  let H := atoms.H
  let ent := atoms.ent
  let raw := atoms.raw
  have A := atoms.post
  obtain ⟨a0, ha0⟩ := Option.isSome_iff_exists.mp (A.done.ready.gpr_some 10 (by decide) (by decide))
  have pc : PCAt jal_80004e80_call.pc d := A.done.pc
  obtain ⟨e, step, P⟩ := (call_registers_summary jal_80004e80_call_shape jal_80004e80_call_decode d
    (jal_80004e80_call_pins A.done.ready.image) A.done.ready.good A.done.ready.image A.done.ready.tick
    A.done.ready.minstret [(10,a0)] ⟨ha0,trivial⟩ (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl).run d ⟨pc,rfl⟩
  have callPost : WriteRegistersPost [1] [] d jal_80004e80_call.target a0
      [(1,jal_80004e80_call.link),(10,a0)] e := P
  have g := GprsSame.of_post callPost (by decide)
  have frame : NativeFrame parameterStack Gc.Skiplist.opStack := by constructor <;> decide
  have short := frame.resize (small := 16) (by decide) (by decide)
  have credits : startupAllocatorCredits - 656 - initGcCredits - 32768 - 8192 = backtraceCapacity + 32 := by decide
  have ready := A.done.ready
  rw [credits] at ready
  have readyE := ready.stack_log callPost (by decide) (by simp only [keysG]; decide) (by decide)
    (g.get (by decide) (by decide) (by decide) ready.stack)
    (gholds_lookup (n := 1) _ P.regs rfl) (by decide) short (by simp only [LogInW])
  have empty : Gc.SkiplistFirst.Empty e.σ.mem := {
    header := fun k hk => by
      rw [show e.σ.mem = d.σ.mem from P.memory]
      exact A.globals _ (Or.inr ⟨by unfold Gc.Skiplist.globalRoots; omega,
        by unfold Gc.Skiplist.globalRoots Gc.Skiplist.headerBytes at *; omega⟩)
    seed := fun k hk => by
      rw [show e.σ.mem = d.σ.mem from P.memory]
      exact A.globals _ (Or.inl ⟨by unfold Gc.Skiplist.randomSeed; omega,
        by unfold Gc.Skiplist.randomSeed; omega⟩) }
  obtain ⟨f, steps, ⟨B⟩⟩ := (caml_init_backtrace e ((raw.toNat,8192) :: H) backtraceCapacity 32 parameterStack
    jal_80004e80_call.link readyE frame empty (List.mem_cons_of_mem _ A.domainOwned) ⟨by decide,by decide⟩).run e
    ⟨by rw [← jal_80004e80_call_target]; exact P.pc, rfl⟩
  exact ⟨initial, f, ⟨{
    reset := atoms.reset
    atoms := d
    source := atoms
    source_run := step.trans steps
    loadCaller := atoms.loadCaller.frame (g.trans (GprsSame.of_saved B.saved)) (by decide) (by decide)
    H := H
    sourceOwned := atoms.sourceOwned
    ent := ent
    raw := raw
    beforeAtoms := atoms.before
    atomDone := A
    atCall := e
    a0 := a0
    call := P
    done := B
    run := atoms.run.trans (step.trans steps) }⟩⟩

/-- Every successful reset of the parsed ELF reaches the checked backtrace return.
Deterministic setup identifies the producer's initial config before transporting its run. -/
theorem reset_init_backtrace (initial : Config) (reset : ElfReset elf initial) :
    ∃ after, Nonempty (ResetBacktrace initial after) := by
  obtain ⟨source, after, ⟨B⟩⟩ := reset_init_backtrace_returned_exists
  have same := reset.unique B.reset.toElfReset
  subst source
  exact ⟨after, ⟨B⟩⟩

/-- The reset-facing interface of `whileMin_reset_loaded_Statement`: any image
with its existing loader/metadata contract reaches the same structured native return. -/
theorem whileMin_reset_backtrace {imageElf : ELF64File}
    (image : WhileMinElf imageElf) (initial : Config) (reset : ElfReset imageElf initial) :
    ∃ after, Nonempty (ResetBacktrace initial after) :=
  reset_init_backtrace initial (reset.of_whileMinElf image whileMin_elf)

/-- Remaining native execution from the backtrace return at `0x80004e84`:
interpreter initialization, debugger initialization, CODE/primitive/DATA loading,
global promotion and system/argv initialization, then the represented interpreter cut.
All input facts are supplied by `ResetBacktrace`; this is an open continuation,
not an additional premise of reset-to-backtrace reachability. -/
def backtrace_loaded_Statement : Prop :=
  ∀ initial after, ResetBacktrace initial after →
    ∃ cut, Steps after cut ∧
      Loaded (runtimeLayout BestFitSingleton OCaml.Vm.Gc.g1Budget) OCaml.Programs.whileMin cut

/-- Discharging just the remaining continuation closes the existing full reset target. -/
theorem whileMin_reset_loaded_of_backtrace (continuation : backtrace_loaded_Statement) :
    whileMin_reset_loaded_Statement := by
  intro imageElf image initial reset
  obtain ⟨after, ⟨B⟩⟩ := whileMin_reset_backtrace image initial reset
  obtain ⟨cut, run, loaded⟩ := continuation initial after B
  exact ⟨cut, B.run.trans run, loaded⟩

end OCaml.Vm.Boot.WhileMinElfParse
