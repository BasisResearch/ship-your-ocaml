import OCaml.Vm.Boot.Startup.LookupLoop

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

theorem lookup_start_input {c : Config} {base : BitVec 64} {bytes : List (BitVec 8)}
    (h : LookupReady c) (hb : gprGet c.σ 18 = some base)
    (window : ReadWindow base 8) (pins : LPins8 c.σ.mem base.toNat bytes)
    (nonnull : bytesVal .ld bytes ≠ 0#64) :
    BlockInput caml_build_primitive_tableX4e0cTSeg 0x80024e0c#64
      (caml_build_primitive_tableX4e0cTL base) [bytes] c where
  good := h.good
  minstret := h.good.minstret
  regs := ⟨hb, True.intro⟩
  keys := by show KeysOK [18]; decide
  shape := by show ChainOK 0x80024e0c#64 [18] caml_build_primitive_tableX4e0cTSeg; decide
  tick := h.tick
  facts := by
    chain_facts h.code with "Vsa.Sim.Code.caml_build_primitive_table_at_"
    · exact window.ld rfl (BitVec.add_zero _) pins
    · exact bne_iff_ne.mpr nonnull

def lookupFunctionAddress (index base : BitVec 64) : BitVec 64 :=
  base + (index <<< 3)

theorem lookup_finish_input {c : Config} {index base : BitVec 64} {bytes : List (BitVec 8)}
    (h : LookupReady c) (hi : gprGet c.σ 8 = some index) (hb : gprGet c.σ 20 = some base)
    (window : ReadWindow (lookupFunctionAddress index base) 8)
    (pins : LPins8 c.σ.mem (lookupFunctionAddress index base).toNat bytes)
    (nonnull : bytesVal .ld bytes ≠ 0#64) :
    BlockInput caml_build_primitive_tableX4e3cFSeg 0x80024e3c#64
      (caml_build_primitive_tableX4e3cFL index base) [bytes] c where
  good := h.good
  minstret := h.good.minstret
  regs := ⟨hi, hb, True.intro⟩
  keys := by show KeysOK [8, 20]; decide
  shape := by show ChainOK 0x80024e3c#64 [8, 20] caml_build_primitive_tableX4e3cFSeg; decide
  tick := h.tick
  facts := by
    chain_facts h.code with "Vsa.Sim.Code.caml_build_primitive_table_at_"
    · apply window.ld rfl ?_ pins
      change lookupFunctionAddress index base + 0#64 = lookupFunctionAddress index base
      exact BitVec.add_zero _
    · exact beq_eq_false_iff_ne.mpr nonnull

end OCaml.Vm.Boot.Startup
