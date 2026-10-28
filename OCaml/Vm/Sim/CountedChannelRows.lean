import OCaml.Vm.Sim.CountedCcall1
import OCaml.Vm.Sim.OpenOutF1Runtime
import OCaml.Vm.Sim.OutListF1Runtime

/-! The three channel summaries consumed by actual unary C_CALL execution.
Runtime suppliers remain the existing data/footprint/pin contracts; none
assumes a primitive result or a counted opcode result. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine
open OutListWalk

/-- The real F1 listing return uses selected runtime credit and the named
native custom call, with no separate listing runtime supplier. -/
theorem counted_f1_out_channels_list_returns {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs) (fits : OCaml.Fits Gc.g1Budget P) :
    CountedPrimReturnsAtR Gc.f1Layout P Customs op ra k "caml_ml_out_channels_list" :=
  counted_caml_ml_out_channels_list_returns (f1_outList_runtime custom) fits

/-- The actual output opening return needs only the accepted native custom call. -/
theorem counted_f1_open_descriptor_out_returns {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs) (fits : OCaml.Fits Gc.g1Budget P)
    (consoles : OCaml.ConsoleChannels P) :
    CountedPrimReturnsAtR Gc.f1Layout P Customs op ra k "caml_ml_open_descriptor_out" :=
  counted_caml_ml_open_descriptor_out_returns (f1_openOut_runtime custom) fits consoles

/-- The shared native opening proof also reconstructs the input-channel runtime. -/
theorem counted_f1_open_descriptor_in_returns {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs) (fits : OCaml.Fits Gc.g1Budget P)
    (stdins : OCaml.StdinChannels P) :
    CountedPrimReturnsAtR Gc.f1Layout P Customs op ra k "caml_ml_open_descriptor_in" :=
  counted_caml_ml_open_descriptor_in_returns (f1_openOut_runtime custom) fits stdins f1_stdinSeek

/-- Execute any successful unary channel call on the full existing semantic
domain. The selected native summary derives readiness from carried physical
counts and the reachable successor's `Fits` bound. -/
theorem counted_channel_c_call1_next {P : Prog} {s : St} {c : Config}
    {index : BitVec 32} {name : String} {v : Val} {heap : Heap} {world : World}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (good : OCaml.GoodF1 P) (fits : OCaml.Fits Gc.g1Budget P)
    (reach : Reach P s) (h : CountedLoopAt Customs Gc.f1Layout P s c)
    (decoded : decodeAt P.code s.pc = some ⟨.C_CALL1, [index.toInt]⟩)
    (nonnegative : 0 ≤ index.toInt) (primitive : P.prims[index.toInt.toNat]? = some name)
    (channel : name = "caml_ml_open_descriptor_out" ∨ name = "caml_ml_open_descriptor_in" ∨
      name = "caml_ml_out_channels_list")
    (sem : primF1Impl name [s.accu] s.heap s.world = .ok v heap world) :
    ∃ after, OCaml.Plus c after ∧ CountedLoopAt Customs Gc.f1Layout P
      {s with pc := s.pc + 2, accu := v, heap := heap, world := world} after := by
  rcases channel with rfl | rfl | rfl
  · exact counted_c_call1_success custom fits reach h decoded nonnegative primitive
      (by decide) sem (counted_f1_open_descriptor_out_returns custom fits good.consoles)
  · exact counted_c_call1_success custom fits reach h decoded nonnegative primitive
      (by decide) sem (counted_f1_open_descriptor_in_returns custom fits good.stdins)
  · exact counted_c_call1_success custom fits reach h decoded nonnegative primitive
      (by decide) sem (counted_f1_out_channels_list_returns custom fits)

end OCaml.Vm.Sim
