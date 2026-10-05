import OCaml.Vm.Boot.Startup.SearchTableReset
import OCaml.Vm.Boot.Startup.SearchExePath
import OCaml.Vm.Boot.Startup.GetenvMiss
import OCaml.Vm.Boot.WhileMinEnvironment
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem getenvMissLog_inside {sp ra s0 s1 s2 s3 s4 s5 s6} (frame : NativeFrame sp 112) :
    LogInW [⟨nativeFrameBase sp 112, sp.toNat⟩] (getenvMissLog sp ra s0 s1 s2 s3 s4 s5 s6) := by
  have outer := frame.resize (small := 32) (by decide) (by decide)
  apply log_in_append
  · apply log_in_larger_window (getenvLog_inside outer)
    · change nativeFrameBase sp 112 ≤ nativeFrameBase sp 32
      unfold nativeFrameBase
      omega
    · exact Nat.le_refl _
  · apply log_in_larger_window (getenv_miss_below_caller frame)
    · exact Nat.le_refl _
    · change nativeFrameBase sp 32 + 16 ≤ sp.toNat
      unfold nativeFrameBase
      have := frame.lower
      omega

theorem embed_bytes {a n : Nat} (inside : Vsa.Sim.DlHeap.heapEnd ≤ a ∧ a + n ≤ embedLimit) :
    ∀ i, i < n → EmbedByte (a + i) := fun _ hi => ⟨by omega, by omega⟩
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

theorem ResetSearchTableReturned.kept {initial after} (w : ResetSearchTableReturned initial after) :
    KeptImage after := by
  have openFrame : NativeFrame (parameterStack + 48#64) 16 := by constructor <;> decide
  have callFrame := EmbedFrame.stack (size := 16) (sp := parameterStack + 48#64) w.call.memory
    (by simp only [camlAttemptLog, LogInW, InsideW]; decide) (by decide)
  have attemptFrame : NativeFrame parameterStack 64 := by constructor <;> decide
  have saveFrame := EmbedFrame.stack w.save.memory (attemptOpenLog_inside attemptFrame) (by decide)
  have searchFrame : NativeFrame attemptStack 48 := by constructor <;> decide
  have searchKept := EmbedFrame.stack w.search.memory (searchExeLog_inside searchFrame) (by decide)
  have tableFrame : NativeFrame searchStack 560 := by constructor <;> decide
  have tableKept := w.returned.embed_frame tableFrame
    (ExtTableSite.at_sp (tableFrame.resize (by decide) (by decide)) (by decide)) (by decide)
  exact (((((w.shared.kept.frame callFrame).frame saveFrame).frame (EmbedFrame.of_memory w.name.memory)).frame
    searchKept).frame tableKept)

/-- Actual reset execution through `getenv("PATH")`, which finds nothing in the
one-entry embedded environment and returns null to caml_search_exe_in_path. -/
structure ResetPathMissed (initial after : Config) where
  source : Config
  table : ResetSearchTableReturned initial source
  atGetenv : Config
  call : WriteRegistersPost [10, 1] [] source jal_80025558_call.target pathName0
    [(1, jal_80025558_call.link), (10, pathName0)] atGetenv
  missed : WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
    (getenvMissLog searchStack jal_80025558_call.link (bytesT table.atSaved.σ.mem exeNameSlot.toNat 8)
      (vsaReg source 9) (vsaReg source 18) (vsaReg source 19) (vsaReg source 20) (vsaReg source 21)
      (vsaReg source 22))
    atGetenv jal_80025558_call.link 0#64
    (getenvReturnRegs searchStack jal_80025558_call.link ++
      getenvMissKeptRegs (bytesT table.atSaved.σ.mem exeNameSlot.toNat 8) (vsaReg source 9)
        (vsaReg source 18) (vsaReg source 19) (vsaReg source 20) (vsaReg source 21) (vsaReg source 22)) after
  run : Steps (Vsa.Densify.fillZero initial) after

theorem reset_path_missed_exists : ∃ initial after, Nonempty (ResetPathMissed initial after) := by
  obtain ⟨initial, source, ⟨w⟩⟩ := reset_search_table_returned_exists
  have ready := w.returned.ready
  have kept := w.kept
  obtain ⟨atGetenv, run1, call⟩ := (search_exe_path source _ ready.toLeafInput).run source ⟨w.pc, rfl⟩
  have keep (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [10, 1]) :
      gprGet atGetenv.σ n = some (vsaReg source n) :=
    (call.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans (gpr_of_ready ready n lower upper)
  have same : atGetenv.σ.mem = source.σ.mem := call.memory
  have keptG := kept.frame (EmbedFrame.of_memory same)
  have envWord (a : Nat) (inside : ∀ i, i < 8 → EmbedByte (a + i)) :
      bytesT atGetenv.σ.mem a 8 = bytesT WhileMinImage.initialMem a 8 := keptG.embed.word a inside
  have entryByte : (atGetenv.σ.mem[(0x8680007f#64 : BitVec 64).toNat]?).getD 0 = BitVec.ofNat 8 79 := by
    have byte := keptG.embed.byte WhileMinImage.envEntry (embed_bytes (n := 1) (by decide) 0 (by decide))
    have value := cstr_getD WhileMinImage.env_string 0 (by decide)
    exact byte.trans value
  have nameByte : (atGetenv.σ.mem[pathName0.toNat]?).getD 0 = BitVec.ofNat 8 80 :=
    cstr_getD (path_name_0 call.image).bytes 0 (by decide)
  have frame : NativeFrame searchStack 112 := by constructor <;> decide
  have input : GetenvMissInput searchStack (BitVec.ofNat 64 WhileMinImage.envArray) 0x8680007f#64 pathName0
      jal_80025558_call.link (bytesT w.atSaved.σ.mem exeNameSlot.toNat 8) (vsaReg source 9) (vsaReg source 18)
      (vsaReg source 19) (vsaReg source 20) (vsaReg source 21) (vsaReg source 22) pathChars0
      (BitVec.ofNat 8 79) (BitVec.ofNat 8 80) atGetenv := {
    toLeafInput := call.leaf (by rfl) (by decide)
    frame := frame
    regs := ⟨gholds_lookup (n := 10) _ call.regs (by rfl),
      (call.frame .x2 (by decide) (by decide)).trans ready.stack, gholds_lookup (n := 1) _ call.regs (by rfl),
      trivial⟩
    saved := ⟨keep 9 (by decide) (by decide) (by decide), keep 18 (by decide) (by decide) (by decide),
      keep 19 (by decide) (by decide) (by decide), keep 20 (by decide) (by decide) (by decide),
      keep 21 (by decide) (by decide) (by decide), keep 22 (by decide) (by decide) (by decide), trivial⟩
    saved0 := (call.frame .x8 (by decide) (by decide)).trans (gholds_lookup (n := 8) _ w.returned.post.regs (by rfl))
    query := path_name_0 call.image
    positive := by decide
    small := by decide
    nameBelow := by decide
    environment := keptG.environ
    envNonzero := by decide
    array := by constructor <;> decide
    first := by
      rw [show (BitVec.ofNat 64 WhileMinImage.envArray).toNat = WhileMinImage.envArray from by decide,
        envWord _ (embed_bytes (by decide))]
      exact WhileMinImage.env_first
    entryNonnull := by decide
    next := by constructor <;> decide
    last := by
      rw [show (BitVec.ofNat 64 WhileMinImage.envArray + 8#64).toNat = WhileMinImage.envArray + 8 from by decide,
        envWord _ (embed_bytes (by decide))]
      exact WhileMinImage.env_end
    arrayBelow := by decide
    firstBelow := by decide
    entryWindow := by constructor <;> decide
    nameWindow := by constructor <;> decide
    entryByte := entryByte
    nameByte := by rw [show pathName0.toNat = pathName0.toNat + 0 from rfl]; exact nameByte
    differ := by decide
    entryBelow := by decide
    unaligned := by decide }
  obtain ⟨after, run2, missed⟩ := (getenv_miss atGetenv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ input).run atGetenv
    ⟨call.pc, rfl⟩
  exact ⟨initial, after, ⟨source, w, atGetenv, call, missed, w.run.trans (run1.trans run2)⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
