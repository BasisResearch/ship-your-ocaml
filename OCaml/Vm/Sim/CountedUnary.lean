import OCaml.Vm.Sim.CountedPrimRows
import OCaml.Vm.Sim.CountedChannelRows
import OCaml.Vm.Sim.CountedConsoleRows
import OCaml.Vm.Sim.CountedCcallOutcome

/-! Complete counted unary assembly. Concrete opening/listing suppliers use
only named CustomMemCall. All success paths retain their actual counts and
returned placement; the shared native exit has no successor obligation. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine

/-- All successful unary F1 implementations belong to the sixteen ordinary
adapters, the counter, flush, or the three allocating channel summaries.
Wrong arities and exit cannot return successfully, whatever the argument. -/
theorem counted_unary_success_cases {name : String} {arg v : Val}
    {heap heap' : Heap} {world world' : World}
    (member : name ∈ primsF1)
    (sem : primF1Impl name [arg] heap world = .ok v heap' world') :
    (name, 1) ∈ countedPrimCases ∨ name = "caml_fresh_oo_id" ∨
      name = "caml_ml_flush" ∨ name = "caml_ml_open_descriptor_out" ∨
      name = "caml_ml_open_descriptor_in" ∨ name = "caml_ml_out_channels_list" := by
  simp only [primsF1, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals solve
    | (apply Or.inl; decide)
    | (apply Or.inr; simp)
    | exact (primF1Impl_sys_exit_ne_ok sem).elim
    | simp [primF1Impl] at sem

/-- Each successful unary implementation executes the existing counted
setup/callee/suffix with its concrete runtime supplier and reachable Fits. -/
theorem counted_unary_success {P : Prog} {s : St} {c : Config}
    {index : BitVec 32} {name : String} {v : Val} {heap : Heap} {world : World}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (fits : OCaml.Fits Gc.g1Budget P) (good : OCaml.GoodF1 P)
    (reach : Reach P s) (h : CountedLoopAt Customs Gc.f1Layout P s c)
    (decoded : decodeAt P.code s.pc = some ⟨.C_CALL1, [index.toInt]⟩)
    (nonnegative : 0 ≤ index.toInt) (primitive : P.prims[index.toInt.toNat]? = some name)
    (member : name ∈ primsF1)
    (sem : primF1Impl name [s.accu] s.heap s.world = .ok v heap world) :
    ∃ after, OCaml.Plus c after ∧ CountedLoopAt Customs Gc.f1Layout P
      {s with pc := s.pc + 2, accu := v, heap := heap, world := world} after := by
  rcases counted_unary_success_cases member sem with ordinary | rfl | rfl | channel
  · exact counted_supported_c_call1_next custom fits reach h decoded nonnegative primitive ordinary sem
  · simp [primF1Impl] at sem
    rcases sem with ⟨rfl, rfl, rfl⟩
    exact counted_fresh_oo_id_next custom fits reach h decoded nonnegative primitive
  · exact counted_flush_next custom good fits reach h decoded nonnegative primitive sem
  · exact counted_channel_c_call1_next custom good fits reach h decoded nonnegative primitive channel sem

/-- Complete success classification from the actual decoded opcode and InF1.
Malformed operands, negative indices, missing slots, wrong arguments and
unsupported primitive outcomes yield no successor; raise/callback are excluded
by the existing primitive outcome interface. -/
theorem counted_c_call1_next {P : Prog} {s s' : St} {c : Config} {i : Instr}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (fits : OCaml.Fits Gc.g1Budget P) (good : OCaml.GoodF1 P)
    (reach : Reach P s) (h : CountedLoopAt Customs Gc.f1Layout P s c)
    (decoded : decodeAt P.code s.pc = some i) (opcode : i.op = .C_CALL1)
    (fragment : OCaml.InF1 P i) (effect : stepI P s i = .next s') :
    ∃ after, OCaml.Plus c after ∧ CountedLoopAt Customs Gc.f1Layout P s' after := by
  obtain ⟨_, fetches⟩ := decode_fetch decoded
  obtain ⟨op, args⟩ := i
  dsimp only at opcode
  subst opcode
  rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · cases effect
  · obtain ⟨index, fetch, rfl⟩ := fetches 0 a rfl
    change (if index.toInt < 0 then .unsupported else
      opt P.prims[index.toInt.toNat]? fun name => cCall P s 2 name [s.accu]) = .next s' at effect
    split at effect
    · cases effect
    · rename_i nonnegative
      cases slot : P.prims[index.toInt.toNat]? with
      | none => simp only [slot, opt] at effect; cases effect
      | some name =>
        have member : name ∈ primsF1 := fragment.prim
          (by change P.prims[index.toInt.toNat]? = some name; exact slot)
        simp only [slot, opt, cCall, prim, primF1, member, ite_true] at effect
        cases result : primF1Impl name [s.accu] s.heap s.world with
        | ok v heap world =>
          rw [result] at effect
          cases effect
          exact counted_unary_success custom fits good reach h decoded (by omega) slot member result
        | raise v heap world => exact (primF1Impl_ne_raise result).elim
        | callback f args heap world => exact (primF1Impl_ne_callback result).elim
        | unsupported => rw [result] at effect; cases effect
        | exit e world => rw [result] at effect; cases effect
  · cases effect

/-- Complete counted C_CALL1 on unchanged GoodF1/Fits. CustomMemCall is the
only native supplier; the opcode's halt uses the actual pinned native exit. -/
theorem counted_c_call1_row {P : Prog}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (fits : OCaml.Fits Gc.g1Budget P) (good : OCaml.GoodF1 P) :
    OCaml.OpArm P (CountedLoopAt Customs Gc.f1Layout P) .C_CALL1 :=
  counted_c_call1_row_of_next fits (fun _ _ _ reach h decoded opcode fragment _ effect =>
    counted_c_call1_next custom fits good reach h decoded opcode fragment effect)

end OCaml.Vm.Sim
