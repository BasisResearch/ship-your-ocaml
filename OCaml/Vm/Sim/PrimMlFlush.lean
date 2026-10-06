import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Sim.CcallWriting
import OCaml.Vm.Primitives.Console.MlFlush
import OCaml.Vm.Primitives.Console.Runtime
import OCaml.Vm.Primitives.ChannelFrame

/-! `caml_ml_flush` at a `C_CALL1` site: its write footprint and the
runtime-stability obligation it puts on the layout. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- `caml_ml_flush`'s writes: the native stack below the C-call sp, newlib's
two `errno` words, the channel record's `offset` and `curr` words. -/
def flushWindows (sp a : Nat) : List W :=
  [⟨sp - 384, sp⟩, ⟨Layout.sym_errno, Layout.sym_errno + 4⟩,
   ⟨Layout.sym_impure_data, Layout.sym_impure_data + 4⟩, ⟨a + 8, a + 16⟩, ⟨a + 24, a + 32⟩]

/-- **Named obligation** (a6-gc, `f1_flush_stable` for F1): the runtime
invariant survives `caml_ml_flush`'s writes to a represented channel record,
from the call site's geometry and native sp. -/
def FlushStable (L : OCaml.Layout) : Prop :=
  ∀ (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace) (high id : Nat) (chn : Chan) (a sp : Nat),
    OCaml.LoopGeometry L P s c pl cp high → L.runtimeOk c →
    s.world.chans[id]? = some chn → cp id = some a →
    Vsa.Sim.DlHeap.heapEnd + nativeHeadroom ≤ sp → sp ≤ Layout.sym_stack_top →
    WindowStable L.runtimeOk (flushWindows sp a)

end OCaml.Vm.Sim
