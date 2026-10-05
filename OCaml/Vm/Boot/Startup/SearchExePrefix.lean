import OCaml.Vm.Boot.Startup.SearchExePrefixNormalized
import OCaml.Vm.Boot.Startup.SearchExePrefixCallInterface
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.Write
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def searchExeSlots (ra s0 s1 : BitVec 64) : List (Nat × BitVec 64) := [(32, s0), (40, ra), (24, s1)]
def searchExeLog (sp ra s0 s1 : BitVec 64) : List WEntry := nativeWordLog sp 48 (searchExeSlots ra s0 s1)

def searchExeInput (sp ra s0 s1 name : BitVec 64) : GRegs := [(2, sp), (8, s0), (10, name), (1, ra), (9, s1)]
def searchExeBlockRegs (sp ra s1 name : BitVec 64) : GRegs :=
  [(10, nativeStack sp 48), (8, name), (11, 8#64), (2, nativeStack sp 48), (1, ra), (9, s1)]
/-- Calling `caml_ext_table_init(&path, 8)` with `path` at the new stack pointer. -/
def searchExeArgs (sp s1 name : BitVec 64) : GRegs :=
  [(10, nativeStack sp 48), (8, name), (11, 8#64), (2, nativeStack sp 48), (9, s1)]

theorem searchExeLog_inside {sp ra s0 s1} (frame : NativeFrame sp 48) :
    LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (searchExeLog sp ra s0 s1) := by
  apply frame.word_log_inside
  intro off value member
  simp only [searchExeSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  omega

theorem searchExe_image_outside {sp ra s0 s1} (frame : NativeFrame sp 48) :
    ImageOutside (searchExeLog sp ra s0 s1) := by
  have lower := frame.lower
  have bounds : Image.textBase + Image.textSize ≤ Vsa.Sim.DlHeap.heapEnd ∧
      Image.rodataBase + Image.rodataSize ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  constructor
  all_goals apply OCaml.Vm.Sim.outLRange_of_windows (searchExeLog_inside frame)
  all_goals exact ⟨Or.inl (by change _ ≤ nativeFrameBase sp 48; unfold nativeFrameBase; omega), trivial⟩

theorem searchExePrefix_input {sp ra s0 s1 name c} (leaf : LeafInput ra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ (searchExeInput sp ra s0 s1 name)) :
    BlockInput searchExePrefixSave 0x80025530#64 (searchExeInput sp ra s0 s1 name) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 8, 10, 1, 9]; decide
  shape := by change ChainOK _ [2, 8, 10, 1, 9] _; decide
  tick := leaf.tick
  facts := by
    have code := searchExePrefix_code leaf.image
    have slot (off : Nat) (bound : off + 8 ≤ 48) (aligned : off % 8 = 0) :
        WriteWindow (nativeStack sp 48 + BitVec.ofNat 64 off) 8 := by
      rw [nativeStack, frame.address _ (by omega)]
      exact frame.word bound aligned
    chain_facts code with "Vsa.Sim.Code.caml_search_exe_in_path_at_"
    · exact (slot 32 (by decide) (by decide)).sd rfl rfl
    · exact (slot 40 (by decide) (by decide)).sd rfl rfl
    · exact (slot 24 (by decide) (by decide)).sd rfl rfl

/-- caml_search_exe_in_path's prologue and its call initializing the stack-local
path table. -/
theorem search_exe_prefix (c : Config) (sp ra s0 s1 name : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ (searchExeInput sp ra s0 s1 name)) :
    FnSummary 0x80025530#64 (fun d => d = c)
      (WriteRegistersPost [2, 11, 8, 10, 1] (searchExeLog sp ra s0 s1) c jal_8002554c_call.target
        (nativeStack sp 48) ((1, jal_8002554c_call.link) :: searchExeArgs sp s1 name)) := by
  have front : FnSummary 0x80025530#64 (fun d => d = c)
      (WriteRegistersPost [2, 11, 8, 10] (searchExeLog sp ra s0 s1) c jal_8002554c_call.pc
        (nativeStack sp 48) (searchExeBlockRegs sp ra s1 name)) := by
    apply registers_of_blocks leaf.image (searchExe_image_outside frame)
      (block_summary _ _ _ _ _ (searchExePrefix_input leaf frame regs))
    · rfl
    · rfl
    · change [(10, nativeStack sp 48 + 0#64), (8, name + 0#64), (11, 0#64 + 8#64),
        (2, nativeStack sp 48), (1, ra), (9, s1)] = _
      rw [BitVec.add_zero, BitVec.add_zero, BitVec.zero_add]
      rfl
    · rfl
    · decide
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  have args : GHolds request.σ (searchExeArgs sp s1 name) :=
    holds_project setup.regs (by simp [searchExeArgs, searchExeBlockRegs, lookupG])
  obtain ⟨after, run2, called⟩ := (call_registers_summary jal_8002554c_call_shape jal_8002554c_call_decode request
    (jal_8002554c_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ args
    (by change KeysOK [10, 8, 11, 2, 9]; decide)
    (by simp only [KeysAvoidRa, searchExeArgs, keysG]; decide) (by rfl)).run request ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩
end OCaml.Vm.Boot.Startup
