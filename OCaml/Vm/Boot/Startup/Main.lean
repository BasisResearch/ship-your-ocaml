import OCaml.Vm.Boot.Startup.MainRows
import OCaml.Vm.Boot.Startup.MainCalls
import OCaml.Vm.Primitives.Blocks
import OCaml.Vm.Primitives.Write
import Vsa.Sim.ChainFactsTac

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

structure MainReady (ra : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  code : Code.MainLoaded c.σ.mem
  stack : gprGet c.σ 2 = some (BitVec.ofNat 64 Layout.sym_stack_top)
  linkReg : gprGet c.σ 1 = some ra

def mainLoads (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [read8 m Layout.sym_embedded_env, read8 m Layout.sym_embedded_argv]

theorem main_input_bytes {ra : BitVec 64} {c : Config} (h : MainReady ra c)
    (envBytes argBytes : List (BitVec 8))
    (envPins : LPins8 c.σ.mem Layout.sym_embedded_env envBytes)
    (argPins : LPins8 c.σ.mem Layout.sym_embedded_argv argBytes) :
    BlockInput mainX1dccSeg (BitVec.ofNat 64 Layout.sym_main)
      (mainX1dccL (BitVec.ofNat 64 Layout.sym_stack_top) ra) [envBytes, argBytes] c where
  good := h.good
  minstret := h.good.minstret
  regs := ⟨h.stack, h.linkReg, True.intro⟩
  keys := by show KeysOK [2, 1]; decide
  shape := by show ChainOK (BitVec.ofNat 64 Layout.sym_main) [2, 1] mainX1dccSeg; decide
  tick := h.tick
  facts := by
    chain_facts h.code with "Vsa.Sim.Code.main_at_"
    · apply ReadWindow.ld (x := BitVec.ofNat 64 Layout.sym_embedded_env)
        (by constructor <;> decide) rfl rfl
      exact envPins
    · apply ReadWindow.ld (x := BitVec.ofNat 64 Layout.sym_embedded_argv)
        (by constructor <;> decide) rfl rfl
      exact argPins
    · exact WriteWindow.sd (x := BitVec.ofNat 64 (Layout.sym_stack_top - 8))
        (by constructor <;> decide) rfl (by
          simp [eaddrM, mainX1dccL, stepGM, srcVal, lookupG, eraseG,
            wvalM, mkLine, decodeM, stepLdsM,
            LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
          decide +kernel)
    · exact WriteWindow.sd (x := BitVec.ofNat 64 Layout.sym_environ)
        (by constructor <;> decide) rfl (by
          simp [eaddrM, mainX1dccL, stepGM, srcVal, lookupG, eraseG,
            wvalM, mkLine, decodeM, stepLdsM,
            LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
          decide +kernel)

/-- Main reads the fixed three-pointer header for arbitrary embedded argv/env. -/
theorem main_prefix (c : Config) (ra : BitVec 64) (h : MainReady ra c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_main) (fun d => d = c)
      (BlockPost mainX1dccSeg (BitVec.ofNat 64 Layout.sym_main)
        (mainX1dccL (BitVec.ofNat 64 Layout.sym_stack_top) ra) (mainLoads c.σ.mem) c) :=
  block_summary _ _ _ _ _ (main_input_bytes h _ _ (read8_pins _ _) (read8_pins _ _))

end OCaml.Vm.Boot.Startup
