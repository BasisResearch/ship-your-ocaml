import OCaml.Vm.Boot.Startup.EmbedFrame
import OCaml.Vm.Boot.Startup.CamlAttemptOpen
import OCaml.Vm.Boot.Startup.AttemptOpenPrefix
import OCaml.Vm.Boot.Startup.SearchExePrefix
import OCaml.Vm.Boot.Startup.RuntimeStack
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

/-- caml_main's `exe_name` slot and caml_attempt_open's frame. -/
def exeNameSlot : BitVec 64 := parameterStack + 32#64
def trailSlot : BitVec 64 := parameterStack + 40#64
def attemptStack : BitVec 64 := nativeStack parameterStack 64
def searchStack : BitVec 64 := nativeStack attemptStack 48

theorem gpr_of_ready {H capacity sp ra c} (ready : RuntimeReady H capacity sp ra c) (n : Nat)
    (lower : 1 ≤ n) (upper : n ≤ 31) : gprGet c.σ n = some (vsaReg c n) :=
  library_gpr ready.platform lower upper rfl

/-- Actual reset execution into caml_attempt_open's search for `argv[0]`,
through the stack-local path table's initialization. -/
structure ResetSearchTableReturned (initial after : Config) where
  source : Config
  shared : ResetSharedTableReturned initial source
  atOpen : Config
  call : WriteRegistersPost [12, 10, 11, 15, 1]
    (camlAttemptLog parameterStack (bytesT source.σ.mem (BitVec.ofNat 64 WhileMinImage.argvArray).toNat 8))
    source jal_80004df8_call.target exeNameSlot
    ((1, jal_80004df8_call.link) :: camlAttemptRegs parameterStack (BitVec.ofNat 64 WhileMinImage.argvArray)
      (bytesT source.σ.mem (BitVec.ofNat 64 WhileMinImage.argvArray).toNat 8)) atOpen
  atSaved : Config
  save : WriteRegistersPost [2, 19]
    (attemptOpenLog parameterStack jal_80004df8_call.link (vsaReg source 8)
      (BitVec.ofNat 64 WhileMinImage.argvArray) (vsaReg source 18) (vsaReg source 19) (vsaReg source 20))
    atOpen 0x800048e0#64 exeNameSlot
    (attemptOpenSaved parameterStack jal_80004df8_call.link (vsaReg source 8)
      (BitVec.ofNat 64 WhileMinImage.argvArray) (vsaReg source 18) (vsaReg source 20) exeNameSlot) atSaved
  atSearch : Config
  name : WriteRegistersPost [20, 8, 10, 1] [] atSaved jal_800048ec_call.target
    (bytesT atSaved.σ.mem exeNameSlot.toNat 8)
    ((1, jal_800048ec_call.link) :: attemptOpenRegs parameterStack (BitVec.ofNat 64 WhileMinImage.argvArray)
      (vsaReg source 18) exeNameSlot trailSlot 0#64 (bytesT atSaved.σ.mem exeNameSlot.toNat 8)) atSearch
  atTable : Config
  search : WriteRegistersPost [2, 11, 8, 10, 1]
    (searchExeLog attemptStack jal_800048ec_call.link trailSlot (BitVec.ofNat 64 WhileMinImage.argvArray))
    atSearch jal_8002554c_call.target searchStack
    ((1, jal_8002554c_call.link) :: searchExeArgs attemptStack (BitVec.ofNat 64 WhileMinImage.argvArray)
      (bytesT atSaved.σ.mem exeNameSlot.toNat 8)) atTable
  H : List (Nat × Nat)
  domain : (firstDomainPtr.toNat, 928) ∈ H
  returned : ExtTableReturned H (startupAllocatorCredits - 448) searchStack jal_8002554c_call.link
    (bytesT atSaved.σ.mem exeNameSlot.toNat 8) searchStack 8#64 atTable after
  run : Steps (Vsa.Densify.fillZero initial) after

theorem ResetSearchTableReturned.pc {initial after} (w : ResetSearchTableReturned initial after) :
    PCAt jal_8002554c_call.link after := w.returned.post.pc

theorem reset_search_table_returned_exists :
    ∃ initial after, Nonempty (ResetSearchTableReturned initial after) := by
  obtain ⟨initial, source, ⟨w⟩⟩ := reset_shared_table_returned_exists
  obtain ⟨H, domain, ready⟩ := w.ready
  have argv := w.argv_array
  -- caml_main: exe_name = argv[0]; call caml_attempt_open
  obtain ⟨atOpen, run1, call⟩ := (caml_attempt_open_call source parameterStack _
    (BitVec.ofNat 64 WhileMinImage.argvArray) ready.toLeafInput ⟨argv, ready.stack, trivial⟩
    (by constructor <;> decide) (by constructor <;> decide)
    (by constructor <;> simp only [camlAttemptLog, OutLRange] <;> decide)).run source ⟨w.pc, rfl⟩
  have openFrame : NativeFrame (parameterStack + 48#64) 16 := by constructor <;> decide
  have openReady := ready.stack_log call (by decide)
    (by simp only [camlAttemptRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ call.regs (by rfl)) (gholds_lookup (n := 1) _ call.regs (by rfl))
    (by decide) openFrame (by simp only [camlAttemptLog, LogInW, InsideW]; decide)
  have kept (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [12, 10, 11, 15, 1]) :
      gprGet atOpen.σ n = some (vsaReg source n) :=
    (call.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans (gpr_of_ready ready n lower upper)
  -- caml_attempt_open: saves
  have attemptFrame : NativeFrame parameterStack 64 := by constructor <;> decide
  obtain ⟨atSaved, run2, save⟩ := (attempt_open_save atOpen parameterStack jal_80004df8_call.link
    (vsaReg source 8) (BitVec.ofNat 64 WhileMinImage.argvArray) (vsaReg source 18) (vsaReg source 19)
    (vsaReg source 20) exeNameSlot openReady.toLeafInput attemptFrame
    ⟨gholds_lookup (n := 2) _ call.regs (by rfl), gholds_lookup (n := 1) _ call.regs (by rfl),
      kept 8 (by decide) (by decide) (by decide), gholds_lookup (n := 9) _ call.regs (by rfl),
      kept 18 (by decide) (by decide) (by decide), kept 19 (by decide) (by decide) (by decide),
      kept 20 (by decide) (by decide) (by decide), gholds_lookup (n := 10) _ call.regs (by rfl),
      trivial⟩).run atOpen ⟨call.pc, rfl⟩
  have savedReady := openReady.stack_log save (by decide)
    (by simp only [attemptOpenSaved, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ save.regs (by rfl)) (gholds_lookup (n := 1) _ save.regs (by rfl))
    (by decide) attemptFrame (attemptOpenLog_inside attemptFrame)
  have savedArg (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [2, 19])
      (h : gprGet atOpen.σ n = some v) : gprGet atSaved.σ n = some v :=
    (save.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans h
  -- caml_attempt_open: *name; call caml_search_exe_in_path
  obtain ⟨atSearch, run3, name⟩ := (attempt_open_name atSaved jal_80004df8_call.link parameterStack
    (BitVec.ofNat 64 WhileMinImage.argvArray) (vsaReg source 18) exeNameSlot trailSlot 0#64
    savedReady.toLeafInput
    ⟨gholds_lookup (n := 10) _ save.regs (by rfl),
      savedArg 11 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 11) _ call.regs (by rfl)),
      savedArg 12 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 12) _ call.regs (by rfl)),
      gholds_lookup (n := 19) _ save.regs (by rfl), gholds_lookup (n := 2) _ save.regs (by rfl),
      gholds_lookup (n := 9) _ save.regs (by rfl), gholds_lookup (n := 18) _ save.regs (by rfl), trivial⟩
    (by constructor <;> decide)).run atSaved ⟨save.pc, rfl⟩
  have nameReady := savedReady.effect name (by decide)
    (by simp only [attemptOpenRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ name.regs (by rfl)) (gholds_lookup (n := 1) _ name.regs (by rfl)) (by decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  -- caml_search_exe_in_path: saves; call caml_ext_table_init(&path, 8)
  have searchFrame : NativeFrame attemptStack 48 := by constructor <;> decide
  obtain ⟨atTable, run4, search⟩ := (search_exe_prefix atSearch attemptStack jal_800048ec_call.link trailSlot
    (BitVec.ofNat 64 WhileMinImage.argvArray) (bytesT atSaved.σ.mem exeNameSlot.toNat 8) nameReady.toLeafInput
    searchFrame
    ⟨gholds_lookup (n := 2) _ name.regs (by rfl), gholds_lookup (n := 8) _ name.regs (by rfl),
      gholds_lookup (n := 10) _ name.regs (by rfl), gholds_lookup (n := 1) _ name.regs (by rfl),
      gholds_lookup (n := 9) _ name.regs (by rfl), trivial⟩).run atSearch ⟨name.pc, rfl⟩
  have tableReady := nameReady.stack_log search (by decide)
    (by simp only [searchExeArgs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ search.regs (by rfl)) (gholds_lookup (n := 1) _ search.regs (by rfl))
    (by decide) searchFrame (searchExeLog_inside searchFrame)
  have capacity : startupAllocatorCredits - 384 = (startupAllocatorCredits - 448) + 64 := by decide
  rw [capacity] at tableReady
  have tableFrame : NativeFrame searchStack 560 := by constructor <;> decide
  obtain ⟨after, run5, ⟨returned⟩⟩ := (ext_table_init atTable H (startupAllocatorCredits - 448) 64 searchStack
    jal_8002554c_call.link (bytesT atSaved.σ.mem exeNameSlot.toNat 8) searchStack 8#64 tableReady tableFrame
    (ExtTableSite.at_sp (tableFrame.resize (by decide) (by decide)) (by decide))
    (gholds_lookup (n := 8) _ search.regs (by rfl)) (gholds_lookup (n := 10) _ search.regs (by rfl))
    (gholds_lookup (n := 11) _ search.regs (by rfl)) (by constructor <;> decide)).run atTable ⟨search.pc, rfl⟩
  exact ⟨initial, after, ⟨source, w, atOpen, call, atSaved, save, atSearch, name, atTable, search, H, domain,
    returned, w.run.trans (run1.trans (run2.trans (run3.trans (run4.trans run5))))⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
