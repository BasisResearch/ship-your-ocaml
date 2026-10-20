import OCaml.Vm.Boot.Startup.InitGc
import OCaml.Vm.Boot.Startup.GcParamPins
import OCaml.Vm.Boot.Startup.CamlInitGcNormalized
import OCaml.Vm.Boot.Startup.CamlInitGcImage
import OCaml.Vm.Boot.Startup.CamlInitGcCallInterface
import OCaml.Vm.Boot.Startup.EmbedFrame
import OCaml.Vm.Boot.Startup.MinorRefSteps
import OCaml.Vm.Boot.Startup.BlockCall
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_main's call `caml_init_gc(caml_init_minor_heap_wsz, caml_init_heap_wsz,
caml_init_heap_chunk_sz, caml_init_percent_free, caml_init_max_percent_free,
caml_init_major_window, caml_init_custom_major_ratio, caml_init_custom_minor_ratio,
caml_init_custom_minor_max_bsz, caml_init_policy)` with the loader's parameters. -/

/-- The `k`-th parameter word as the loader leaves it. -/
def gcParamWord (k : Nat) : BitVec 64 :=
  bytesVal .ld [gcParamByte (8 * k), gcParamByte (8 * k + 1), gcParamByte (8 * k + 2), gcParamByte (8 * k + 3),
    gcParamByte (8 * k + 4), gcParamByte (8 * k + 5), gcParamByte (8 * k + 6), gcParamByte (8 * k + 7)]

theorem gcParam_layout : gcParamAddr = 0x800647f0 ∧ gcParamBytes = 88 := by decide

/-- The bytes caml_main loads for the `k`-th parameter. -/
def gcLoad (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) : List (BitVec 8) :=
  Primitives.read8 m (BitVec.ofNat 64 (gcParamAddr + 8 * k)).toNat

/-- A parameter word of a kept image. -/
theorem GcInitImage.param {c : Config} (h : GcInitImage c) (k : Nat) (hk : k < 11) :
    bytesVal .ld (gcLoad c.σ.mem k) = gcParamWord k := by
  have addr : (BitVec.ofNat 64 (gcParamAddr + 8 * k)).toNat = gcParamAddr + 8 * k := by
    rw [BitVec.toNat_ofNat]; unfold gcParamAddr; exact Nat.mod_eq_of_lt (by omega)
  have b (i : Nat) (hi : i < 8) : (c.σ.mem[gcParamAddr + 8 * k + i]?).getD 0 = gcParamByte (8 * k + i) := by
    rw [h.data _ (by unfold GcDataByte gcParamAddr; omega), Nat.add_assoc,
      gc_param_initial _ (Nat.zero_le _) (by omega)]
    rfl
  have b0 := b 0 (by decide)
  simp only [Nat.add_zero] at b0
  rw [gcLoad, addr, Primitives.read8, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide), b 4 (by decide), b 5 (by decide),
    b 6 (by decide), b 7 (by decide)]
  rfl

/-- caml_main's outgoing stack arguments: `policy` at 8(sp), `custom_minor_max_bsz` at 0(sp). -/
def camlInitGcArgSlots : List (Nat × BitVec 64) := [(8, 2#64), (0, 8192#64)]

/-- The argument stores, as words of caml_main's 16-byte outgoing area. -/
def camlInitGcArgsLog : List WEntry := nativeWordLog (parameterStack + 16#64) 16 camlInitGcArgSlots

theorem camlInitGcArgs_frame : NativeFrame (parameterStack + 16#64) 16 := by constructor <;> decide

local macro "cig" : tactic => `(tactic| simp only [camlinitgc_line_80004e14, camlinitgc_line_80004e18, camlinitgc_line_80004e1c, camlinitgc_line_80004e20, camlinitgc_line_80004e24, camlinitgc_line_80004e28, camlinitgc_line_80004e2c, camlinitgc_line_80004e30, camlinitgc_line_80004e34, camlinitgc_line_80004e38, camlinitgc_line_80004e3c, camlinitgc_line_80004e40, camlinitgc_line_80004e44, camlinitgc_line_80004e48, camlinitgc_line_80004e4c, camlinitgc_line_80004e50, camlinitgc_line_80004e54, camlinitgc_line_80004e58, camlinitgc_line_80004e5c, camlinitgc_line_80004e60, camlinitgc_line_80004e64, camlinitgc_line_80004e68, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- Load the ten parameters; store the two stack arguments. -/
theorem caml_init_gc_args (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(2, parameterStack)]) (params : GcInitImage c) :
    FnSummary 0x80004e14#64 (fun e => e = c) (WriteRegistersPost [14, 15, 17, 16, 13, 12, 11, 10]
      camlInitGcArgsLog c jal_80004e6c_call.pc 262144#64
      [(14, 500#64), (15, 1#64), (17, 100#64), (16, 44#64), (13, 120#64), (12, 15#64), (11, 126976#64),
        (10, 262144#64), (2, parameterStack)]) := by
  have w (k : Nat) (hk : k < 11) := params.param k hk
  apply registers_of_blocks' leaf.image
    (camlInitGcArgs_frame.image_outside (camlInitGcArgs_frame.word_log_inside fun off value member => by
      simp [camlInitGcArgSlots] at member; omega))
    (block_summary _ _ _ _ _ (show BlockInput caml_mainX4e14Seg 0x80004e14#64 [(2, parameterStack)]
        [gcLoad c.σ.mem 0, gcLoad c.σ.mem 1,
          gcLoad c.σ.mem 2, gcLoad c.σ.mem 3,
          gcLoad c.σ.mem 10, gcLoad c.σ.mem 7,
          gcLoad c.σ.mem 6, gcLoad c.σ.mem 8,
          gcLoad c.σ.mem 9, gcLoad c.σ.mem 4]
        c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2]; decide
      shape := by change ChainOK _ [2] _; decide
      tick := leaf.tick
      facts := by
        have code := camlInitGc_code leaf.image
        have rd (k : Nat) (hk : k < 11) : ReadWindow (BitVec.ofNat 64 (gcParamAddr + 8 * k)) 8 := by
          constructor <;> simp only [BitVec.toNat_ofNat, gcParamAddr, Layout.sym_tohost] <;> omega
        chain_facts code with "Vsa.Sim.Code.caml_main_at_"
        · exact (rd 0 (by decide)).ld rfl (by cig; decide) (read8_pins _ _)
        · exact (rd 1 (by decide)).ld rfl (by cig; decide) (read8_pins _ _)
        · exact (rd 2 (by decide)).ld rfl (by cig; decide) (read8_pins _ _)
        · exact (rd 3 (by decide)).ld rfl (by cig; decide) (read8_pins _ _)
        · exact (rd 10 (by decide)).ld rfl (by cig; decide) (read8_pins _ _)
        · exact (rd 7 (by decide)).ld rfl (by cig; decide) (read8_pins _ _)
        · exact (rd 6 (by decide)).ld rfl (by cig; decide) (read8_pins _ _)
        · exact (rd 8 (by decide)).ld rfl (by cig; decide) (read8_pins _ _)
        · exact (show WriteWindow (parameterStack + 8#64) 8 by constructor <;> decide).sd rfl (by cig; decide)
        · exact (show WriteWindow parameterStack 8 by constructor <;> decide).sd rfl (by cig; decide)
        · past_stores
          · exact (rd 9 (by decide)).ld rfl (by cig; decide) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, and_true]; cig; decide)
        · past_stores
          · exact (rd 4 (by decide)).ld rfl (by cig; decide) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, and_true]; cig; decide) }))
  · simp only [caml_mainX4e14Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, ldsRunM, wlogM, stepGM, stepLdsM,
      eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some,
      Nat.reduceEqDiff, ite_true, ite_false, camlinitgc_line_80004e14, camlinitgc_line_80004e18, camlinitgc_line_80004e1c, camlinitgc_line_80004e20, camlinitgc_line_80004e24, camlinitgc_line_80004e28, camlinitgc_line_80004e2c, camlinitgc_line_80004e30, camlinitgc_line_80004e34, camlinitgc_line_80004e38, camlinitgc_line_80004e3c, camlinitgc_line_80004e40, camlinitgc_line_80004e44, camlinitgc_line_80004e48, camlinitgc_line_80004e4c, camlinitgc_line_80004e50, camlinitgc_line_80004e54, camlinitgc_line_80004e58, camlinitgc_line_80004e5c, camlinitgc_line_80004e60, camlinitgc_line_80004e64, camlinitgc_line_80004e68]
    rw [w 0 (by decide), w 1 (by decide)]
    rfl
  · rfl
  · intro σ pins
    simp only [caml_mainX4e14Seg, evalBlocks, evalBlock, SegEvalState.init, camlinitgc_line_80004e14, camlinitgc_line_80004e18, camlinitgc_line_80004e1c, camlinitgc_line_80004e20, camlinitgc_line_80004e24, camlinitgc_line_80004e28, camlinitgc_line_80004e2c, camlinitgc_line_80004e30, camlinitgc_line_80004e34, camlinitgc_line_80004e38, camlinitgc_line_80004e3c, camlinitgc_line_80004e40, camlinitgc_line_80004e44, camlinitgc_line_80004e48, camlinitgc_line_80004e4c, camlinitgc_line_80004e50, camlinitgc_line_80004e54, camlinitgc_line_80004e58, camlinitgc_line_80004e5c, camlinitgc_line_80004e60, camlinitgc_line_80004e64, camlinitgc_line_80004e68, runGM,
      stepGM, eraseG, wvalM, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, ldsRunM,
      stepLdsM, List.headD_cons, List.tail_cons] at pins
    rw [w 9 (by decide), w 4 (by decide), w 2 (by decide), w 3 (by decide), w 10 (by decide), w 7 (by decide),
      w 6 (by decide), w 8 (by decide)] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup (n := 2) _ pins rfl, trivial⟩
  · rfl
  · decide
/-- Then `jal caml_init_gc`. -/
theorem caml_init_gc_call (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(2, parameterStack)]) (params : GcInitImage c) :
    FnSummary 0x80004e14#64 (fun d => d = c) (WriteRegistersPost ([14, 15, 17, 16, 13, 12, 11, 10] ++ [1])
      camlInitGcArgsLog c jal_80004e6c_call.target 262144#64 ((1, jal_80004e6c_call.link) ::
      [(14, 500#64), (15, 1#64), (17, 100#64), (16, 44#64), (13, 120#64), (12, 15#64), (11, 126976#64),
        (10, 262144#64), (2, parameterStack)])) :=
  block_then_call c jal_80004e6c_call_shape jal_80004e6c_call_decode (fun _ h => jal_80004e6c_call_pins h)
    (caml_init_gc_args c ra leaf regs params) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl
end OCaml.Vm.Boot.Startup
