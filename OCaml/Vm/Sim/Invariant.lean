import OCaml.Vm.Repr
import OCaml.Vm.ImageData
import Vsa.Sim.FrameOn

/-!
# The running invariant: VM stack geometry (a1-arms)

`caml_init_stack` allocates the VM stack once, `Stack_size` bytes below
`Caml_state->stack_high`. Under the budget (`Fits`), `check_stacks` never
reaches `caml_realloc_stack`, so the stack stays in the window
`[high - stackBytes, high)` for the whole run.

`StackGeometry` places that window in writable RAM above every static
symbol, and separates it from every other part of the represented payload:
the `Caml_state` record, the code words, the live heap objects, the channel
records and the primitive-table entries. Consumers (`InvariantUse.lean`)
derive the arms' read/write windows and `PayloadOutside` certificates from it.
The code geometry facts are a2-sem's (`CodeFacts.lean`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- The VM stack's allocation, `[high - stackBytes, high)`. -/
def stackWindow (high : Nat) : W := ⟨high - Layout.stackBytes, high⟩

/-- **Stack geometry** of a represented state under its placement. Every
field is placement-level or names a config word the arms frame anyway. -/
structure StackGeometry (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (high : Nat) : Prop where
  /-- the whole allocation lies above `.bss` (hence above the image, `tohost`
  and every static runtime variable) -/
  statics : Layout.sym_bss_end + Layout.stackBytes ≤ high
  /-- and inside RAM -/
  top : high ≤ 0x100000000
  aligned : high % 8 = 0
  domain : OutWRange [stackWindow high] (word c Layout.sym_Caml_state).toNat Layout.domainStateBytes
  code : ∀ i w, P.code[i]? = some w → OutWRange [stackWindow high] (pl.codeBase + 4 * i) 4
  heap : ∀ l a o, Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some o →
    OutWRange [stackWindow high] (a - 8) (8 * o.wosize + 8)
  channels : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    OutWRange [stackWindow high] a (chanOffBuff + ch.buffer.length)
  primitives : ∀ i name, P.prims[i]? = some name →
    OutWRange [stackWindow high]
      ((word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i) 8

end OCaml.Vm.Sim
