import OCaml.Vm.Boot.Startup.InitStackSaveNormalized
import OCaml.Vm.Boot.Startup.InitStackSaveImage
import OCaml.Vm.Boot.Startup.InitStackStateNormalized
import OCaml.Vm.Boot.Startup.InitStackStateImage
import OCaml.Vm.Boot.Startup.InitStackStateCallInterface
import OCaml.Vm.Boot.Startup.InitStackFieldsNormalized
import OCaml.Vm.Boot.Startup.InitStackFieldsImage
import OCaml.Vm.Boot.Startup.InitStackReturnNormalized
import OCaml.Vm.Boot.Startup.InitStackReturnImage
import OCaml.Vm.Boot.Startup.CamlInitGcArgs
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_init_stack's blocks, called from caml_main at `parameterStack`. -/

/-- caml_init_stack's saved registers in its 32-byte frame. -/
def initStackSlots (ra s0 s1 s2 : BitVec 64) : List (Nat × BitVec 64) := [(16, s0), (8, s1), (24, ra), (0, s2)]

def initStackSaveLog (sp ra s0 s1 s2 : BitVec 64) : List WEntry :=
  nativeWordLog sp 32 (initStackSlots ra s0 s1 s2)

theorem initStack_frame : NativeFrame parameterStack 32 := by constructor <;> decide

local macro "iss" : tactic => `(tactic| simp only [initstacksave_line_80004064, initstacksave_line_80004068, initstacksave_line_8000406c, initstacksave_line_80004070, initstacksave_line_80004074, initstackstate_line_80004078, initstackstate_line_8000407c, initstackstate_line_80004080, initstackstate_line_80004084, initstackstate_line_80004088, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- Open a 32-byte frame; save s0–s2 and ra. -/
theorem init_stack_save (c : Config) (sp ra s0 s1 s2 a0 : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 32)
    (regs : GHolds c.σ [(2, sp), (8, s0), (9, s1), (1, ra), (18, s2), (10, a0)]) :
    FnSummary 0x80004064#64 (fun e => e = c) (WriteRegistersPost [2]
      (initStackSaveLog sp ra s0 s1 s2) c 0x80004078#64 a0
      [(2, nativeStack sp 32), (10, a0), (1, ra)]) := by
  have inside : LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (initStackSaveLog sp ra s0 s1 s2) :=
    frame.word_log_inside fun off value member => by simp [initStackSlots] at member; omega
  apply registers_of_blocks' leaf.image (frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_stackX4064Seg 0x80004064#64
        [(2, sp), (8, s0), (9, s1), (1, ra), (18, s2), (10, a0)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 8, 9, 1, 18, 10]; decide
      shape := by change ChainOK _ [2, 8, 9, 1, 18, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := initStackSave_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 32) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 32 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_init_stack_at_"
        · exact (slot 16 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 0 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_stackX4064Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG, eraseG,
      wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, initstacksave_line_80004064,
      initstacksave_line_80004068, initstacksave_line_8000406c, initstacksave_line_80004070,
      initstacksave_line_80004074] at pins
    exact ⟨gholds_lookup (n := 2) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, gholds_lookup (n := 1) _ pins rfl,
      trivial⟩
  · rfl
  · decide

/-- `s0 = max_size`, `s1 = &Caml_state`, `s2 = Caml_state`, `a0 = Stack_size`. -/
theorem init_stack_state (c : Config) (ra a0 : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, a0)])
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr) :
    FnSummary 0x80004078#64 (fun e => e = c) (WriteRegistersPost [8, 9, 10, 18] [] c jal_8000408c_call.pc 0x8000#64
      [(8, a0), (9, BitVec.ofNat 64 Layout.sym_Caml_state), (10, 0x8000#64), (18, firstDomainPtr)]) := by
  have state : bytesVal .ld (Primitives.read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat) = firstDomainPtr := by
    rw [read8_value]; exact domain
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_stackX4078Seg 0x80004078#64 [(10, a0)]
        [Primitives.read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := initStackState_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_stack_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 by constructor <;> decide).ld rfl
            (by iss; decide) (read8_pins _ _) }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_stackX4078Seg, evalBlocks, evalBlock, SegEvalState.init] at pins
    simp only [initstacksave_line_80004064, initstacksave_line_80004068, initstacksave_line_8000406c, initstacksave_line_80004070, initstacksave_line_80004074, initstackstate_line_80004078, initstackstate_line_8000407c, initstackstate_line_80004080, initstackstate_line_80004084, initstackstate_line_80004088, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons] at pins
    rw [state] at pins
    exact ⟨gholds_lookup_eq pins rfl (by rw [sext_zero, BitVec.add_zero]), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 18) _ pins rfl, trivial⟩
  · rfl
  · decide
def camlMaxStackSizeAddr : Nat := 0x80064970

/-- The stack fields of the domain record and `caml_max_stack_size`, for a
stack block `p`: `stack_low`, `stack_threshold`, `stack_high`, `extern_sp`,
`trapsp`, `trap_barrier`. -/
def initStackCells (p mx : BitVec 64) : List (Nat × BitVec 64) :=
  [(domainField 136, p), (domainField 152, p + 2048#64), (domainField 144, p + 0x8000#64),
    (domainField 160, p + 0x8000#64), (domainField 168, p + 0x8000#64), (domainField 176, p + 0x8008#64),
    (camlMaxStackSizeAddr, mx)]

def initStackFieldsLog (p mx : BitVec 64) : List WEntry := (initStackCells p mx).map fun (a, v) => (a, 8, v)

/-- The bytes the block loads: `Caml_state`, then `stack_low` just stored. -/
def initStackFieldsLoads (m : Std.ExtHashMap Nat (BitVec 8)) (p : BitVec 64) : List (List (BitVec 8)) :=
  [Primitives.read8 m (BitVec.ofNat 64 Layout.sym_Caml_state).toNat,
    Primitives.read8 (writeLog m [((firstDomainPtr + Functions.sign_extend (m := 64) 136#12).toNat, 8, p)])
      (firstDomainPtr + Functions.sign_extend (m := 64) 136#12).toNat]

local macro "isf" : tactic => `(tactic| simp only [initstackfields_line_80004090, initstackfields_line_80004094, initstackfields_line_80004098, initstackfields_line_8000409c, initstackfields_line_800040a0, initstackfields_line_800040a4, initstackfields_line_800040a8, initstackfields_line_800040ac, initstackfields_line_800040b0, initstackfields_line_800040b4, initstackfields_line_800040b8, initstackfields_line_800040bc, initstackfields_line_800040c0, initstackfields_line_800040c4, initstackfields_line_800040c8, initstackfields_line_800040cc, initstackfields_line_800040d0, initstackfields_line_800040d4, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons, initStackFieldsLoads, MemFacts, stepMemM, wentryM, widthOfM, wlogM])

/-- Store the new stack's bounds into the domain record and `caml_max_stack_size`. -/
theorem init_stack_fields (c : Config) (ra p mx : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(9, BitVec.ofNat 64 Layout.sym_Caml_state), (18, firstDomainPtr), (10, p), (8, mx)])
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr) :
    FnSummary 0x80004090#64 (fun e => e = c) (WriteRegistersPost [14, 13, 15, 10, 11, 12]
      (initStackFieldsLog p mx) c 0x800040d8#64 0x8000#64
      [(8, mx), (10, 0x8000#64), (14, firstDomainPtr), (13, p + 0x8008#64), (15, 0x800650d0#64), (11, p + 2048#64),
        (12, mx >>> 10)]) := by
  have state : bytesVal .ld (Primitives.read8 c.σ.mem (BitVec.ofNat 64 Layout.sym_Caml_state).toNat) = firstDomainPtr := by
    rw [read8_value]; exact domain
  have back : bytesVal .ld (Primitives.read8 (writeLog c.σ.mem [((firstDomainPtr + Functions.sign_extend (m := 64) 136#12).toNat, 8, p)])
      (firstDomainPtr + Functions.sign_extend (m := 64) 136#12).toNat) = p := by
    rw [read8_value]; exact word_writeLog _ _ _
  apply registers_of_blocks' leaf.image
    (by constructor <;> simp only [initStackFieldsLog, initStackCells, List.map, OutLRange, domainField, camlMaxStackSizeAddr] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_stackX4090Seg 0x80004090#64
        [(9, BitVec.ofNat 64 Layout.sym_Caml_state), (18, firstDomainPtr), (10, p), (8, mx)]
        (initStackFieldsLoads c.σ.mem p) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [9, 18, 10, 8]; decide
      shape := by change ChainOK _ [9, 18, 10, 8] _; decide
      tick := leaf.tick
      facts := by
        have code := initStackFields_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_stack_at_"
        all_goals try isf
        all_goals try rw [state]
        all_goals try rw [back]
        all_goals first
          | (constructor; decide; exact read8_pins _ _)
          | decide
          | trace_state }))
  · simp only [caml_init_stackX4090Seg, evalBlocks, evalBlock, SegEvalState.init]
    isf
    rw [state, back,
      show Functions.sign_extend (m := 64) 2047#12 = 2047#64 by decide,
      show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide,
      show Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 34103#32 +++ 0#12) = 0x8000#64 by decide,
      show Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 34487#32 +++ 0#12) +
        Functions.sign_extend (m := 64) 8#12 = 0x8008#64 by decide,
      BitVec.add_assoc, show (2047#64 + 1#64 : BitVec 64) = 2048#64 by decide]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_init_stackX4090Seg, evalBlocks, evalBlock, SegEvalState.init] at pins
    simp only [initstackfields_line_80004090, initstackfields_line_80004094, initstackfields_line_80004098, initstackfields_line_8000409c, initstackfields_line_800040a0, initstackfields_line_800040a4, initstackfields_line_800040a8, initstackfields_line_800040ac, initstackfields_line_800040b0, initstackfields_line_800040b4, initstackfields_line_800040b8, initstackfields_line_800040bc, initstackfields_line_800040c0, initstackfields_line_800040c4, initstackfields_line_800040c8, initstackfields_line_800040cc, initstackfields_line_800040d0, initstackfields_line_800040d4, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons, initStackFieldsLoads, MemFacts, stepMemM, wentryM, widthOfM, wlogM] at pins
    rw [state, back,
      show Functions.sign_extend (m := 64) 2047#12 = 2047#64 by decide,
      show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide,
      show Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 34487#32 +++ 0#12) +
        Functions.sign_extend (m := 64) 8#12 = 0x8008#64 by decide,
      BitVec.add_assoc, show (2047#64 + 1#64 : BitVec 64) = 2048#64 by decide, srli_ten _ _ rfl] at pins
    exact ⟨gholds_lookup (n := 8) _ pins rfl, gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 14) _ pins rfl,
      gholds_lookup (n := 13) _ pins rfl, gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 11) _ pins rfl,
      gholds_lookup (n := 12) _ pins rfl, trivial⟩
  · rfl
  · decide
def initStackSavedLoads (m : Std.ExtHashMap Nat (BitVec 8)) (sp : BitVec 64) : List (List (BitVec 8)) :=
  [Primitives.read8 m (nativeFrameBase sp 32 + 16), Primitives.read8 m (nativeFrameBase sp 32 + 24),
    Primitives.read8 m (nativeFrameBase sp 32 + 8), Primitives.read8 m (nativeFrameBase sp 32 + 0)]

/-- Restore s0–s2 and ra; tail call `caml_gc_message(0x08, "Initial stack limit…", …)`. -/
theorem init_stack_return (c : Config) (sp ra s0 s1 s2 a2 oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 32) (regs : GHolds c.σ [(2, nativeStack sp 32), (12, a2)])
    (saved : ∀ off value, (off, value) ∈ initStackSlots ra s0 s1 s2 →
      bytesT c.σ.mem (nativeFrameBase sp 32 + off) 8 = value) :
    FnSummary 0x800040d8#64 (fun e => e = c) (WriteRegistersPost [8, 1, 9, 18, 12, 11, 10, 2]
      [] c 0x80003cb0#64 8#64 [(8, s0), (1, ra), (9, s1), (18, s2), (10, 8#64), (2, sp), (12, a2 <<< 3),
        (11, 0x800555f0#64)]) := by
  have word (off : Nat) (value : BitVec 64) (member : (off, value) ∈ initStackSlots ra s0 s1 s2) :
      bytesVal .ld (Primitives.read8 c.σ.mem (nativeFrameBase sp 32 + off)) = value := by
    rw [read8_value]; exact saved off value member
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_stackX40d8Seg 0x800040d8#64
        [(2, nativeStack sp 32), (12, a2)] (initStackSavedLoads c.σ.mem sp) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 12]; decide
      shape := by change ChainOK _ [2, 12] _; decide
      tick := leaf.tick
      facts := by
        have code := initStackReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_stack_at_"
        · exact (frame.read_slot (off := 16) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 0) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide)) }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_stackX40d8Seg, initStackSavedLoads, evalBlocks, evalBlock, SegEvalState.init] at pins
    simp only [runGM, stepGM, stepLdsM, ldsRunM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff,
      Nat.reduceAdd, ite_true, ite_false, List.headD_cons, List.tail_cons, imm20Of, eaddrM, initstackreturn_line_800040d8, initstackreturn_line_800040dc, initstackreturn_line_800040e0, initstackreturn_line_800040e4, initstackreturn_line_800040e8, initstackreturn_line_800040ec, initstackreturn_line_800040f0, initstackreturn_line_800040f4, initstackreturn_line_800040f8] at pins
    rw [show Functions.sign_extend (m := 64) 32#12 = 32#64 by decide, nativeStack_restore,
      word 16 s0 (by simp [initStackSlots]), word 24 ra (by simp [initStackSlots]),
      word 8 s1 (by simp [initStackSlots]), word 0 s2 (by simp [initStackSlots])] at pins
    exact ⟨gholds_lookup (n := 8) _ pins rfl, gholds_lookup (n := 1) _ pins rfl, gholds_lookup (n := 9) _ pins rfl,
      gholds_lookup (n := 18) _ pins rfl, gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 2) _ pins rfl,
      gholds_lookup_eq pins rfl (slli_three _ _ rfl), gholds_lookup_eq pins rfl (by decide), trivial⟩
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
