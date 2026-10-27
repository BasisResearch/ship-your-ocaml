import OCaml.Vm.Boot.Startup.ReadSectionsLoop
import OCaml.Vm.Boot.Startup.AttemptOkReset
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  OCaml.Vm.Boot.Startup

/-! The reset run through caml_main's `caml_read_section_descriptors`. -/

/-- The trailer's first word after caml_attempt_open swapped it: 7 sections. -/
theorem swapped_sections : [swappedTrailer 0, swappedTrailer 1, swappedTrailer 2, swappedTrailer 3] = sectionsWord := by
  have e (k : Nat) (hk : k < 4) : trailerSource + (3 - k) = WhileMinImage.embedEnd0 - 16 + (3 - k) := by
    unfold trailerSource WhileMinImage.embedEnd0; omega
  simp only [swappedTrailer, show (0 : Nat) < 4 by decide, show (1 : Nat) < 4 by decide,
    show (2 : Nat) < 4 by decide, show (3 : Nat) < 4 by decide, ite_true]
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
  rw [WhileMinImage.embedTrailer0_byte_3, WhileMinImage.embedTrailer0_byte_2, WhileMinImage.embedTrailer0_byte_1,
    WhileMinImage.embedTrailer0_byte_0]
  rfl

/-- The live blocks after caml_attempt_open. -/
abbrev attemptBlocks {initial atOpen : Config} (o : ResetProgOpened initial atOpen) : List (Nat × Nat) :=
  (o.call.call.copy.toNat, 5 + 1) :: (o.call.retry.failed.opened.opened.node.toNat, 5) ::
    o.call.retry.failed.opened.call.search.path.table.H

/-- The reset run, through `caml_read_section_descriptors(3, &trail)`'s return. -/
structure ResetReadSections (initial after : Config) where
  attempted : Config
  attempt : ResetAttemptOk initial attempted
  atCall : Config
  /-- The descriptor-read call stores nothing. -/
  callMemory : atCall.σ.mem = attempted.σ.mem
  /-- caml_init_gc's globals at the descriptor read. -/
  params : GcInitImage atCall
  blk : BitVec 64
  done : ReadSectionsDone (attemptBlocks attempt.opened) (startupAllocatorCredits - 656)
    attempt.opened.call.retry.failed.opened.opened.node jal_80004e10_call.link 3#64 argvPtr
    (vsaReg attempt.opened.call.atRetry 18) blk atCall after
  run : Steps (Vsa.Densify.fillZero initial) after

/-- Follow the actual attempt/open/search history back to the parameter producer,
whose nested source retains the parsed ELF's successful setup. -/
theorem ResetReadSections.reset {initial after} (w : ResetReadSections initial after) :
    ElfResetReady elf initial :=
  w.attempt.opened.call.retry.failed.opened.call.search.path.table.shared.reset

theorem reset_read_sections_exists : ∃ initial after, Nonempty (ResetReadSections initial after) := by
  obtain ⟨initial, d, ⟨w⟩⟩ := reset_attempt_ok_exists
  have K := w.ok
  have A := w.attempt
  -- caml_main: the descriptor is valid; `caml_read_section_descriptors(fd, &trail)`
  obtain ⟨d1, run1, p1⟩ := (caml_read_sections_call d jal_8000512c_call.link 3#64 _ K.ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ K.regs rfl, gholds_lookup (n := 2) _ K.regs rfl, trivial⟩ rfl
    (by decide) (by decide) (by decide)).run d ⟨K.pc, rfl⟩
  have keep (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [10, 11, 15, 14, 8] ++ [1])
      (hv : gprGet d.σ n = some v) : gprGet d1.σ n = some v :=
    (p1.toEffectPost.gpr_frame (by decide) n lo hi out).trans hv
  have credits : startupAllocatorCredits - 592 = (startupAllocatorCredits - 656) + 64 := by decide
  have ready1 : RuntimeReady (attemptBlocks w.opened) ((startupAllocatorCredits - 656) + 64) parameterStack
      jal_80004e10_call.link d1 := by
    rw [← credits]
    exact K.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) (by decide)
      (show NativeFrame parameterStack 32 by constructor <;> decide) (by simp only [LogInW])
  have mem1 : d1.σ.mem = d.σ.mem := p1.memory
  have hsp : attemptStack.toNat = 0x87ffff40 := by decide
  -- low memory caml_attempt_open kept
  have low (x : Nat) (hx : x < heapEnd) (errno : OutW errnoWindows x)
      (pos : x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x) (magic : x < Layout.sym_magicstr ∨
        Layout.sym_magicstr + 13 ≤ x) : (d1.σ.mem[x]?).getD 0 = (w.atOpen.σ.mem[x]?).getD 0 := by
    rw [mem1, K.kept x (Or.inl (by unfold heapEnd at hx; omega)) errno pos (by
      simp only [OutW, attemptWindows, and_true]
      rw [show WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 by decide,
        show WhileMinElfParse.exeNameSlot.toNat = 0x87ffffa0 by decide]
      unfold heapEnd at hx; omega)]
  have R : ReadSectionsCall (attemptBlocks w.opened) (startupAllocatorCredits - 656) 64
      w.opened.call.retry.failed.opened.opened.node jal_80004e10_call.link 3#64 argvPtr
      (vsaReg w.opened.call.atRetry 18) d1 := {
    pc := p1.pc
    regs := ⟨gholds_lookup (n := 2) _ p1.regs rfl, gholds_lookup (n := 1) _ p1.regs rfl,
      gholds_lookup (n := 10) _ p1.regs rfl, gholds_lookup (n := 11) _ p1.regs rfl,
      gholds_lookup (n := 8) _ p1.regs rfl,
      keep 9 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ K.regs rfl),
      keep 18 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ K.regs rfl), trivial⟩
    ready := ready1
    charged := ⟨by decide, by decide⟩
    embed := ⟨fun a ha => by
      have lt := (show KeptByte a from Or.inl ha).lt
      unfold EmbedByte at ha
      rw [mem1, K.kept a (Or.inl (by unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size at lt; omega))
        (by simp only [OutW, errnoWindows, and_true]; unfold heapEnd at ha; omega)
        (Or.inr (by unfold heapEnd at ha; unfold Layout.sym_fds; omega)) (by
          simp only [OutW, attemptWindows, and_true]
          rw [show WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 by decide,
            show WhileMinElfParse.exeNameSlot.toNat = 0x87ffffa0 by decide]
          unfold embedLimit Layout.sym_stack_top Layout.sym_stack_size Layout.sym_magicstr heapEnd at *; omega)]
      exact A.late.embed.byte a ⟨ha.1, ha.2⟩⟩
    file := (show OpenFile w.atOpen.σ.mem w.opened.call.retry.failed.opened.opened.node from
        ⟨A.words, A.slot, A.kind, A.nodeWord, A.flags⟩).transport fun x hx => by
      rcases hx with ⟨htif, pos⟩ | ⟨lo, hi⟩
      · have := htif.bounds
        exact low x (by unfold Layout.sym_files heapEnd at *; omega) htif.out_errno pos (by
          rcases htif with ⟨l, h⟩ | ⟨l, h⟩ | ⟨l, h⟩ | ⟨l, h⟩ | ⟨l, h⟩ <;>
            simp only [Layout.sym_fs_ready, Layout.sym_impure_ptr, Layout.sym_files, Layout.sym_print_config,
              Layout.sym_fds, Layout.sym_magicstr] at * <;> omega)
      · have heap := A.nodeHeap
        exact low x (by omega) (by simp only [OutW, errnoWindows, and_true]; unfold heapStart at heap; omega)
          (Or.inr (by unfold heapStart Layout.sym_fds at *; omega))
          (Or.inr (by unfold heapStart Layout.sym_magicstr at *; omega))
    nodeOwned := fun j hj => ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by unfold InExt; omega⟩
    numWord := by
      rw [mem1]
      simp only [read4]
      rw [show WhileMinElfParse.trailSlot.toNat = WhileMinElfParse.trailSlot.toNat + 0 from rfl,
        K.trailer 0 (by decide), K.trailer 1 (by decide), K.trailer 2 (by decide), K.trailer 3 (by decide)]
      exact swapped_sections }
  have params : GcInitImage d1 := A.late.gc.of_bytes fun a ha => by
    have r := ha.late.range
    exact low a (by unfold heapEnd; omega) (by simp only [OutW, errnoWindows, and_true]; omega)
      (by unfold Layout.sym_fds; omega) (by unfold Layout.sym_magicstr; omega)
  obtain ⟨blk, after, run2, done⟩ := read_section_descriptors d1 _ _ _ _ _ _ _ _ R
  exact ⟨initial, after, ⟨⟨d, w, d1, mem1, params, blk, done, w.run.trans (run1.trans run2)⟩⟩⟩

/-- caml_init_gc's globals after the descriptor table is read. -/
theorem ResetReadSections.gc {initial after} (w : ResetReadSections initial after) : GcInitImage after :=
  w.params.of_bytes fun a ha => by
    have r := ha.late.range
    exact w.done.globals a (by unfold heapEnd; omega)
      (KeptByte.not_foot (Or.inr (Or.inr (Or.inr (Or.inr ha)))))
      (by simp only [OutW, errnoWindows, and_true]; omega) (by unfold Layout.sym_fds; omega)

/-- The record and the tables after the section table is read. -/
theorem ResetReadSections.kept_after {initial after} (w : ResetReadSections initial after) :
    DomainKept w.attempt.opened.call.retry.failed.opened.call.search.path.table.H after.σ.mem
      w.attempt.opened.call.retry.failed.opened.call.search.path.table.t1
      w.attempt.opened.call.retry.failed.opened.call.search.path.table.t2
      w.attempt.opened.call.retry.failed.opened.call.search.path.table.t3 := by
  have k := w.attempt.kept_after
  rw [← w.callMemory] at k
  apply k.live
  constructor
  intro e he x inside
  have member : e ∈ attemptBlocks w.attempt.opened := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)
  have b := w.done.ready.block_bounds (q := e.1) (n := e.2) (List.mem_cons_of_mem _ member)
  have inside' := inside
  unfold InExt at inside'
  have hs : heapStart = 0x8007d140 := rfl
  exact w.done.globals x (by omega) (owned_not_foot (by omega) ⟨e, member, inside⟩)
    (by simp only [OutW, errnoWindows, and_true]; omega) (Or.inr (by unfold Layout.sym_fds; omega))
end OCaml.Vm.Boot.WhileMinElfParse
