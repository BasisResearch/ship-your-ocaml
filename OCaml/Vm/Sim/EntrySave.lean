import OCaml.Vm.Sim.EntryFrame

/-!
# caml_interprete's entry, part 1: the callee-saved stores

`entry_save` runs the generated prologue (`tr_interp_entry_save`): the frame
allocation, the thirteen callee-saved stores and the `prog ≠ NULL` branch.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The prologue's callee-saved stores, in program order. -/
def entrySaveLog (sp : Nat) (regs : Nat → BitVec 64) : List WEntry :=
  Layout.interpSavedRegs.map fun r => (sp - Layout.interpFrameBytes + Layout.interpSaveOffset r, 8, regs r)

theorem entrySaveLog_above {sp : Nat} {regs : Nat → BitVec 64} (frame : EntryFrame sp) :
    ∀ e ∈ entrySaveLog sp regs, Vsa.Sim.DlHeap.heapEnd ≤ e.1 := by
  intro e he
  simp only [entrySaveLog, List.mem_map] at he
  obtain ⟨r, -, rfl⟩ := he
  exact Nat.le_trans (Nat.le_sub_of_add_le frame.low) (Nat.le_add_right _ _)

structure EntrySaveInput (c : Config) (sp : Nat) (regs : Nat → BitVec 64) (a0 : BitVec 64) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  pc : pcOf c = some (BitVec.ofNat 64 Layout.sym_caml_interprete)
  stack : gpr c 2 = some (BitVec.ofNat 64 sp)
  saved : ∀ r ∈ Layout.interpSavedRegs, gpr c r = some (regs r)
  arg : gpr c 10 = some a0
  nonzero : a0 ≠ 0#64
  frame : EntryFrame sp

structure EntrySavePost (before : Config) (sp : Nat) (regs : Nat → BitVec 64) (a0 : BitVec 64)
    (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some 0x80001e38#64
  stack : gpr after 2 = some (BitVec.ofNat 64 (sp - Layout.interpFrameBytes))
  saved : ∀ r ∈ Layout.interpSavedRegs, gpr after r = some (regs r)
  arg : gpr after 10 = some a0
  memory : after.σ.mem = writeLog before.σ.mem (entrySaveLog sp regs)
  output : after.σ.sailOutput = before.σ.sailOutput
  htif : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes
  gprs : OCaml.Vm.Boot.Startup.GprPresent before.σ → OCaml.Vm.Boot.Startup.GprPresent after.σ

theorem entry_save {c : Config} {sp : Nat} {regs : Nat → BitVec 64} {a0 : BitVec 64}
    (h : EntrySaveInput c sp regs a0) :
    ∃ n after, StepsN n c after ∧ EntrySavePost c sp regs a0 after := by
  obtain ⟨b1, b2, b3⟩ := h.frame.nat
  have r (k : Nat) (hk : k ∈ Layout.interpSavedRegs) := h.saved k hk
  have bp : SegSt (0x80001df8#64) [⟨Register.x2, BitVec.ofNat 64 sp⟩, ⟨Register.x1, regs 1⟩,
      ⟨Register.x8, regs 8⟩, ⟨Register.x9, regs 9⟩, ⟨Register.x18, regs 18⟩, ⟨Register.x19, regs 19⟩,
      ⟨Register.x20, regs 20⟩, ⟨Register.x21, regs 21⟩, ⟨Register.x22, regs 22⟩, ⟨Register.x23, regs 23⟩,
      ⟨Register.x24, regs 24⟩, ⟨Register.x25, regs 25⟩, ⟨Register.x26, regs 26⟩, ⟨Register.x27, regs 27⟩,
      ⟨Register.x10, a0⟩]
      (fun σ => Vsa.Sim.Code.CamlInterpEntrySaveLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.good, h.pc, ⟨h.stack, r 1 (by decide), r 8 (by decide), r 9 (by decide), r 18 (by decide),
      r 19 (by decide), r 20 (by decide), r 21 (by decide), r 22 (by decide), r 23 (by decide),
      r 24 (by decide), r 25 (by decide), r 26 (by decide), r 27 (by decide), h.arg, trivial⟩,
      h.good.minstret, h.tick, interp_entry_save_loaded h.image, rfl, rfl⟩
  have run := tr_interp_entry_save (BitVec.ofNat 64 sp) (regs 1) (regs 8) (regs 9) (regs 18) (regs 19)
    (regs 20) (regs 21) (regs 22) (regs 23) (regs 24) (regs 25) (regs 26) (regs 27) a0 c.σ.mem c.σ
  simp (disch := decide) only [slot_nat sp _ (by omega) (by omega)] at run
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, frame_sp sp (by omega) (by omega)] at run
  obtain ⟨n, after, _, steps, post⟩ := run (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl
    (by simpa only [bne_iff_ne, ne_eq] using h.nonzero) c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have memLog : after.σ.mem = writeLog c.σ.mem (entrySaveLog sp regs) := by
    rw [memory]
    simp only [entrySaveLog, Layout.interpSavedRegs, List.map, writeLog, List.foldl, applyW,
      Layout.interpSaveOffset, Layout.interpFrameBytes]
  refine ⟨n, after, steps, post.good, ?_, post.tick, post.pcAt, PinsHold.get post.pins ⟨0, by simp⟩,
    ?_, ?_, ?_, frame.out, frame.frame _ (by decide), ?_⟩
  · exact image_of_writeLog h.image (image_outside_of_above (entrySaveLog_above h.frame)) memLog
  · intro k hk
    exact (frame.gpr_list (L := Layout.interpSavedRegs) (by decide) k hk).trans (h.saved k hk)
  · exact (frame.frame Register.x10 (by decide)).trans h.arg
  · exact memLog
  · exact fun p => p.of_stepFrame frame (writes := [2]) (by decide) (by decide) fun n hn => by
      rw [List.mem_singleton.1 hn]; exact gprGet_isSome_of (PinsHold.get post.pins ⟨0, by simp⟩)

end OCaml.Vm.Sim
