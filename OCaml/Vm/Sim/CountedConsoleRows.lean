import OCaml.Vm.Sim.CountedConsole
import OCaml.Vm.Sim.CountedCcall2
import OCaml.Vm.Sim.CountedCcall4
import OCaml.Vm.Sim.CcallShort
import OCaml.Bytecode.PrimOutcome

/-! Counted console returns and consumers at their actual arities. C_CALL4
has only the two output successes; every other real outcome is checked. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- One adapter for the generic native console contracts. -/
theorem counted_console_returns {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {P : Prog} {op : Opcode}
    {ra : BitVec 64} {k : Nat} {name : String}
    (custom : Gc.CustomMemCall Ready state Customs)
    (native : ∀ L : OCaml.Layout, ConsoleStable L →
      (∀ c, L.runtimeOk c → ConsoleWrite.ConsoleRuntime c) → PrimReturnsAt L P op ra k name)
    (model : ∀ args h w v h' w', primF1Impl name args h w = .ok v h' w' → ChannelRefsSame w w') :
    CountedPrimReturnsAtR Gc.f1Layout P Customs op ra k name :=
  counted_prim_returns_of_refs
    (fun _ _ => native _ (counted_console_stable custom) (fun c h => Gc.f1_consoleRuntime c h.1)) model

theorem counted_caml_ml_flush_returns {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {P : Prog} {ra : BitVec 64}
    (custom : Gc.CustomMemCall Ready state Customs) (consoles : OCaml.ConsoleChannels P) :
    CountedPrimReturnsAtR Gc.f1Layout P Customs .C_CALL1 ra 0 "caml_ml_flush" :=
  counted_console_returns custom (fun _ stable rt => prim_caml_ml_flush_returns stable rt consoles)
    (fun _ _ _ _ _ _ sem => flush_primitive_refs_same sem)

theorem counted_caml_ml_output_char_returns {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {P : Prog} {ra : BitVec 64}
    (custom : Gc.CustomMemCall Ready state Customs) (consoles : OCaml.ConsoleChannels P) :
    CountedPrimReturnsAtR Gc.f1Layout P Customs .C_CALL2 ra 1 "caml_ml_output_char" :=
  counted_console_returns custom (fun _ stable rt => prim_caml_ml_output_char_returns stable rt consoles)
    (fun _ _ _ _ _ _ sem => output_char_primitive_refs_same sem)

theorem counted_caml_ml_output_returns {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {P : Prog} {ra : BitVec 64}
    (custom : Gc.CustomMemCall Ready state Customs) (consoles : OCaml.ConsoleChannels P) :
    CountedPrimReturnsAtR Gc.f1Layout P Customs .C_CALL4 ra 3 "caml_ml_output" :=
  counted_console_returns custom (fun _ stable rt => prim_caml_ml_output_returns stable rt consoles)
    (fun _ _ _ _ _ _ sem => output_primitive_refs_same (Or.inl rfl) sem)

theorem counted_caml_ml_output_bytes_returns {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {P : Prog} {ra : BitVec 64}
    (custom : Gc.CustomMemCall Ready state Customs) (consoles : OCaml.ConsoleChannels P) :
    CountedPrimReturnsAtR Gc.f1Layout P Customs .C_CALL4 ra 3 "caml_ml_output_bytes" :=
  counted_console_returns custom (fun _ stable rt => prim_caml_ml_output_bytes_returns stable rt consoles)
    (fun _ _ _ _ _ _ sem => output_primitive_refs_same (Or.inr rfl) sem)

/-- The actual unary setup/return consumer for flush. -/
theorem counted_flush_next {P : Prog} {s : St} {c : Config}
    {index : BitVec 32} {v : Val} {heap : Heap} {world : World}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (good : OCaml.GoodF1 P) (fits : OCaml.Fits Gc.g1Budget P)
    (reach : Reach P s) (h : CountedLoopAt Customs Gc.f1Layout P s c)
    (decoded : decodeAt P.code s.pc = some ⟨.C_CALL1, [index.toInt]⟩)
    (nonnegative : 0 ≤ index.toInt) (primitive : P.prims[index.toInt.toNat]? = some "caml_ml_flush")
    (sem : primF1Impl "caml_ml_flush" [s.accu] s.heap s.world = .ok v heap world) :
    ∃ after, OCaml.Plus c after ∧ CountedLoopAt Customs Gc.f1Layout P
      {s with pc := s.pc + 2, accu := v, heap := heap, world := world} after :=
  counted_c_call1_success custom fits reach h decoded nonnegative primitive (by decide) sem
    (counted_caml_ml_flush_returns custom good.consoles)

/-- The actual binary setup/return consumer for character output. -/
theorem counted_output_char_next {P : Prog} {s : St} {c : Config}
    {index : BitVec 32} {v : Val} {heap : Heap} {world : World}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (good : OCaml.GoodF1 P) (fits : OCaml.Fits Gc.g1Budget P)
    (reach : Reach P s) (h : CountedLoopAt Customs Gc.f1Layout P s c)
    (depth : 1 ≤ s.stack.length)
    (decoded : decodeAt P.code s.pc = some ⟨.C_CALL2, [index.toInt]⟩)
    (nonnegative : 0 ≤ index.toInt) (primitive : P.prims[index.toInt.toNat]? = some "caml_ml_output_char")
    (sem : primF1Impl "caml_ml_output_char" (s.accu :: s.stack.take 1) s.heap s.world = .ok v heap world) :
    ∃ after, OCaml.Plus c after ∧ CountedLoopAt Customs Gc.f1Layout P
      {s with pc := s.pc + 2, accu := v, heap := heap, world := world, stack := s.stack.drop 1} after :=
  counted_c_call2_success custom fits reach h depth decoded nonnegative primitive (by decide) sem
    (counted_caml_ml_output_char_returns custom good.consoles)

/-- Both real four-argument output consumers retain the native returned
placement and pop exactly three arguments. -/
theorem counted_output_next {P : Prog} {s : St} {c : Config}
    {index : BitVec 32} {name : String} {v : Val} {heap : Heap} {world : World}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (good : OCaml.GoodF1 P) (fits : OCaml.Fits Gc.g1Budget P)
    (reach : Reach P s) (h : CountedLoopAt Customs Gc.f1Layout P s c)
    (depth : 3 ≤ s.stack.length)
    (decoded : decodeAt P.code s.pc = some ⟨.C_CALL4, [index.toInt]⟩)
    (nonnegative : 0 ≤ index.toInt) (primitive : P.prims[index.toInt.toNat]? = some name)
    (nameOk : name = "caml_ml_output" ∨ name = "caml_ml_output_bytes")
    (sem : primF1Impl name (s.accu :: s.stack.take 3) s.heap s.world = .ok v heap world) :
    ∃ after, OCaml.Plus c after ∧ CountedLoopAt Customs Gc.f1Layout P
      {s with pc := s.pc + 2, accu := v, heap := heap, world := world, stack := s.stack.drop 3} after := by
  rcases nameOk with rfl | rfl
  · exact counted_c_call4_success custom fits reach h depth decoded nonnegative primitive (by decide) sem
      (counted_caml_ml_output_returns custom good.consoles)
  · exact counted_c_call4_success custom fits reach h depth decoded nonnegative primitive (by decide) sem
      (counted_caml_ml_output_bytes_returns custom good.consoles)

/-- Complete successful-return coverage at arity four: the other implementation
patterns are excluded using the shared arity adapter, not assumed unreachable. -/
theorem counted_c_call4_local_returns {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {P : Prog} {cp : ChanPlace} {world : World}
    (custom : Gc.CustomMemCall Ready state Customs) (good : OCaml.GoodF1 P) :
    CcallReturns (countedLayout Gc.f1Layout Customs cp world) P .C_CALL4 (0x80002f40#64) 3 :=
  CcallReturns.of_primsF1D fun name _ => by
    by_cases nameOk : name = "caml_ml_output" ∨ name = "caml_ml_output_bytes"
    · rcases nameOk with rfl | rfl
      · exact (prim_caml_ml_output_returns (counted_console_stable custom)
          (fun c h => Gc.f1_consoleRuntime c h.1) good.consoles).toR.toD
      · exact (prim_caml_ml_output_bytes_returns (counted_console_stable custom)
          (fun c h => Gc.f1_consoleRuntime c h.1) good.consoles).toR.toD
    · exact PrimReturnsAtD.of_arity (fun _ _ _ _ _ _ len sem =>
        nameOk (primF1Impl_four_name len sem))

/-- Every accepted four-argument F1 step obtains its reference frame from
its actual successful primitive return. Rejection branches have no successor. -/
theorem counted_c_call4_refs {P : Prog} {s s' : St} {args : List Int}
    (f1 : OCaml.InF1 P ⟨.C_CALL4, args⟩)
    (effect : stepI P s ⟨.C_CALL4, args⟩ = .next s') : ChannelRefsSame s.world s'.world := by
  rcases args with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · cases effect
  · change (if p < 0 ∨ s.stack.length < 3 then .unsupported else
      opt P.prims[p.toNat]? fun name => cCall P s 2 name (s.accu :: s.stack.take 3)) = .next s' at effect
    split at effect
    · cases effect
    · rename_i guard
      cases slot : P.prims[p.toNat]? with
      | none => simp [slot, opt] at effect
      | some name =>
        have member : name ∈ primsF1 := f1.prim (by simpa only [Instr.ccallName] using slot)
        have len : (s.accu :: s.stack.take 3).length = 4 := by
          simp only [List.length_cons, List.length_take]; omega
        simp only [slot, opt, cCall, prim, primF1, member, ite_true] at effect
        cases result : primF1Impl name (s.accu :: s.stack.take 3) s.heap s.world with
        | ok v heap world =>
          rw [result] at effect; cases effect
          exact output_primitive_refs_same (primF1Impl_four_name len result) result
        | exit e world => rw [result] at effect; cases effect
        | unsupported => rw [result] at effect; cases effect
        | raise e heap world => exact (primF1Impl_ne_raise result).elim
        | callback cb cbargs heap world => exact (primF1Impl_ne_callback result).elim
  · cases effect

/-- Complete C_CALL4: generic native setup/callee/suffix, actual output frames,
all operand/primitive/outcome cases, and the real GoodF1/Fits guards. -/
theorem counted_c_call4_row {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {P : Prog}
    (custom : Gc.CustomMemCall Ready state Customs)
    (fits : OCaml.Fits Gc.g1Budget P) (good : OCaml.GoodF1 P) :
    OCaml.OpArm P (CountedLoopAt Customs Gc.f1Layout P) .C_CALL4 :=
  counted_refs_row
    (fun _ _ => c_call4_row (counted_memoryStable f1_memoryStable custom.accounting)
      (counted_runtimeFrame custom) fits g1_capacity (counted_c_call4_local_returns custom good)
      (fun name s young aligned => allocPlaces_ok name s young aligned))
    (fun _ i _ opcode f1 effect => counted_c_call4_refs (P := P) (args := i.args)
      (by cases i; cases opcode; exact f1) (by cases i; cases opcode; exact effect))

end OCaml.Vm.Sim
