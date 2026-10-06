import OCaml.Vm.Sim.Ccall1
import OCaml.Vm.Sim.Ccall2
import OCaml.Vm.Sim.Ccall3
import OCaml.Vm.Sim.Ccall4
import OCaml.Vm.Sim.Ccall5
import OCaml.Vm.Sim.VmLog
import OCaml.Vm.Sim.RaiseRows

/-!
# C_CALL1..5 from the loop head

The call-site contract `CcallReady` is derived from the loop head: the
primitive's entry from the represented bindings, the table slot from the
geometry (`primsRam`), the return-frame stores from `Ccall1WriteOk.of_geometry`
(the VM stack below `sp` and `Caml_state->extern_sp`). The callee's machine
summary is the named obligation `CcallCallee` (lane a1-prims).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **C_CALL's return-frame stores are separated and writable.** -/
theorem Ccall1WriteOk.of_geometry {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} (next env : BitVec 64) (g : ArmGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) (space : 8 * (s.stack.length + 2) ≤ Layout.stackBytes) :
    Ccall1WriteOk P s c pl cp sp (word c Layout.sym_Caml_state).toNat next env := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  have hl := g.domainLow
  have hal := g.domainAligned
  have hda := g.domainArena
  have hd := g.domain.1
  simp only [stackWindow] at hd
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have off : Layout.off_extern_sp + 8 ≤ Layout.domainStateBytes := by decide
  have room : 16 ≤ sp := by omega
  have inside := ccall1_log_in (domain := (word c Layout.sym_Caml_state).toNat) next env room
  have ok := VmLogOk.of_windows g stack (by omega) inside (by
    intro w hw
    simp only [ccall1Windows, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩
    · exact Or.inr ⟨Layout.off_extern_sp, by decide, rfl⟩)
  have trapsp : OutLRange (ccall1Log sp (word c Layout.sym_Caml_state).toNat next env)
      ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) 8 := by
    apply outLRange_of_windows inside
    simp only [ccall1Windows, OutWRange, and_true]
    simp only [Layout.off_trapsp, Layout.off_extern_sp, Layout.domainStateBytes] at *
    omega
  have dn : (BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp)).toNat =
      (word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [Vsa.Sim.DlHeap.heapEnd] at hda; omega)]
  refine ⟨room, by omega, by simp only [Vsa.Sim.DlHeap.heapEnd] at hda; omega,
    by simpa using g.write stack (k := 2) (by decide) (by omega),
    by simpa using g.write stack (k := 1) (by decide) (by omega), ⟨?_, ?_, ?_, ?_⟩, by omega,
    { ok.core with trapsp, stack := ok.stack, heap := fun l a o _ placed object => ok.heap l a o placed object },
    ok.image, ok.young, ok.bindings⟩
  all_goals rw [dn]
  all_goals simp only [Layout.sym_tohost, Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd,
    Layout.off_extern_sp, Layout.domainStateBytes] at *
  all_goals omega

/-- **The C_CALL call-site contract at a loop head.** -/
theorem CcallReady.of_loop {L : OCaml.Layout} {P : Prog} {s : St} {c : Config} {op : Opcode}
    {index : BitVec 32} {name : String} (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op)
    (fetch : P.code[s.pc + 1]? = some index) (nonnegative : 0 ≤ index.toInt)
    (primitive : P.prims[index.toInt.toNat]? = some name)
    (space : 8 * (s.stack.length + 2) ≤ Layout.stackBytes) :
    ∃ pl cp sp high entry value env, CcallReady op L P s c pl cp sp high
      (word c Layout.sym_Caml_state).toNat
      (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat entry value env index name := by
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨entry, lookup, -⟩ := input.primitives.targets _ name primitive
  obtain ⟨value, -, valueWord⟩ := input.accu
  obtain ⟨env, -, envWord⟩ := input.env
  have aligned := PrimitiveEntries.lookup_aligned lookup
  exact ⟨pl, cp, sp, high, entry, value, env,
    { input with
      operand := OperandAt.of_fetch input.geometry.toArmGeometry fetch
      nonnegative, primitive, entryName := lookup
      aligned := by rw [BitVec.toNat_ofNat]; omega
      domainWord := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      tableWord := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      targetRead := input.geometry.primsRam _ name primitive
      value := valueWord
      environment := envWord
      space := Ccall1WriteOk.of_geometry _ env input.geometry.toArmGeometry input.stack space }⟩

/-! ## The C_CALL rows -/

/-- `Caml_state`'s address at a configuration. -/
abbrev domainAt (c : Config) : Nat := (word c Layout.sym_Caml_state).toNat

/-- **Returning F1 primitives at a `C_CALLk` site** (named obligation, lane
a1-prims): for every call-site contract and successful primitive result, the
callee's machine summary. `k` stack words are passed after the accumulator;
`ra` is the arm's return site. -/
structure CcallReturns (L : OCaml.Layout) (P : Prog) (op : Opcode) (ra : BitVec 64) (k : Nat) : Prop where
  callee : ∀ s c pl cp sp high table entry value env index name v heap world, Reach P s →
    CcallReady op L P s c pl cp sp high (domainAt c) table entry value env index name →
    name ∈ primsF1 → primF1Impl name (s.accu :: s.stack.take k) s.heap s.world = .ok v heap world →
    ∃ result, CcallCallee ra (s.accu :: s.stack.take k) L P s pl cp sp high (domainAt c) entry env
      name v result heap world

/-- **The other primitive outcomes** at a `C_CALLk` site: raising, exiting or
calling back (named obligation of the lanes owning those continuations). -/
structure CcallEffects (L : OCaml.Layout) (P : Prog) (op : Opcode) (k : Nat) : Prop where
  outcome : ∀ s c (w : BitVec 32) name, Reach P s → OCaml.LoopAt L P s c → DispatchCode P s op →
    P.code[s.pc + 1]? = some w → 0 ≤ w.toInt → P.prims[w.toInt.toNat]? = some name → name ∈ primsF1 →
    (∀ v heap world, primF1Impl name (s.accu :: s.stack.take k) s.heap s.world ≠ .ok v heap world) →
    OCaml.ArmOutcome (OCaml.LoopAt L P) c (stepI P s ⟨op, [w.toInt]⟩)

/-- **Primitives that always return** discharge the other outcomes: when every
reachable call's F1 primitive returns normally, `CcallEffects` is vacuous. -/
theorem CcallEffects.of_ok {L : OCaml.Layout} {P : Prog} {op : Opcode} {k : Nat}
    (ok : ∀ s (w : BitVec 32) name, Reach P s → DispatchCode P s op → P.code[s.pc + 1]? = some w →
      0 ≤ w.toInt → P.prims[w.toInt.toNat]? = some name → name ∈ primsF1 →
      ∃ v heap world, primF1Impl name (s.accu :: s.stack.take k) s.heap s.world = .ok v heap world) :
    CcallEffects L P op k :=
  ⟨fun s _ w name reach _ code fetch nonnegative hp member notOk => by
    obtain ⟨v, heap, world, result⟩ := ok s w name reach code fetch nonnegative hp member
    exact absurd result (notOk v heap world)⟩

/-- The shared C_CALLk row. -/
theorem ccall_row_of {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k high0 dom0 : Nat} (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B) (small : k ≤ 4)
    (semantics : ∀ s p, stepI P s ⟨op, [p]⟩ = if p < 0 ∨ s.stack.length < k then .unsupported else
      opt P.prims[p.toNat]? fun nm => cCall P s 2 nm (s.accu :: s.stack.take k))
    (shape : ∀ s args, (∀ a, args ≠ [a]) → stepI P s ⟨op, args⟩ = .unsupported)
    (ccallName : ∀ p : Int, Instr.ccallName P ⟨op, [p]⟩ = P.prims[p.toNat]?)
    (arm : ∀ s s' c pl cp sp high table entry value env index name v result heap world,
      WindowStable L.runtimeOk (ccall1Windows sp (domainAt c)) →
      CcallReady op L P s c pl cp sp high (domainAt c) table entry value env index name →
      CcallArguments s sp k →
      CcallCallee ra (s.accu :: s.stack.take k) L P s pl cp sp high (domainAt c) entry env name v result
        heap world →
      stepI P s ⟨op, [index.toInt]⟩ = .next s' → ∃ after, OCaml.Plus c after ∧ OCaml.Running L P s' after)
    (returns : CcallReturns L P op ra k) (effects : CcallEffects L P op k) :
    OCaml.OpArm P (OCaml.LoopAt L P) op := by
  intro s c i reach h hd hop f1
  obtain ⟨code, fetches⟩ := decode_fetch hd
  obtain ⟨o, args⟩ := i
  simp only at hop
  subst hop
  by_cases single : ∃ a, args = [a]
  · obtain ⟨a, rfl⟩ := single
    obtain ⟨w, fetch, rfl⟩ := fetches 0 a rfl
    by_cases neg : w.toInt < 0 ∨ s.stack.length < k
    · rw [semantics, if_pos neg]; trivial
    cases hp : P.prims[w.toInt.toNat]? with
    | none => rw [semantics, if_neg neg, hp]; trivial
    | some name =>
      have member : name ∈ primsF1 := f1.prim (by rw [ccallName, hp])
      have nonnegative : 0 ≤ w.toInt := by omega
      have bound : k ≤ s.stack.length := by omega
      by_cases ok : ∃ v heap world, primF1Impl name (s.accu :: s.stack.take k) s.heap s.world = .ok v heap world
      · obtain ⟨v, heap, world, result⟩ := ok
        apply OCaml.ArmOutcome.of_next
        · intro s' step
          have space := stack_fits fits capacity reach (k := 2)
          obtain ⟨pl, cp, sp, high, entry, value, env, ready⟩ :=
            CcallReady.of_loop h code fetch nonnegative hp space
          obtain ⟨res, callee⟩ := returns.callee s c pl cp sp high _ entry value env w name v heap world
            reach ready member result
          have hs := ready.stack.1
          have same : high = high0 := ready.stackHigh.symm.trans (rf.stackHigh c ready.runtime)
          subst same
          have stable' : WindowStable L.runtimeOk (ccall1Windows sp (domainAt c)) :=
            rf.windows _ fun x hx => by
              simp only [ccall1Windows, List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl
              · exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩
              · rw [domainAt, rf.domainWord c ready.runtime]
                exact Or.inr ⟨Layout.off_extern_sp, by decide, rfl⟩
          have arguments : CcallArguments s sp k :=
            ⟨bound, fun j hj => ready.geometry.read ready.stack (stack_space ready.stack (by omega))
              (i := j) (by omega)⟩
          obtain ⟨after, run, running⟩ := arm s s' c pl cp sp high _ entry value env w name v res heap world
            stable' ready arguments callee step
          exact ⟨after, run, h.of_plus run running⟩
        · intro e x halt
          rw [semantics, if_neg neg, hp] at halt
          simp only [opt, cCall, prim, primF1, member, if_true, result] at halt
          cases halt
      · exact effects.outcome s c w name reach h code fetch nonnegative hp member
          (fun v heap world eq => ok ⟨v, heap, world, eq⟩)
  · rw [shape s args (fun a ha => single ⟨a, ha⟩)]; trivial

/-- **The C_CALL1 row.** -/
theorem c_call1_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (returns : CcallReturns L P .C_CALL1 (0x80003060#64) 0) (effects : CcallEffects L P .C_CALL1 0) :
    OCaml.OpArm P (OCaml.LoopAt L P) .C_CALL1 :=
  ccall_row_of stable rf fits capacity (by decide) (fun _ _ => by simp only [Nat.not_lt_zero, or_false]; rfl)
    (fun s args ne => by
      rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rfl
      · exact absurd rfl (ne a)
      · rfl)
    (fun _ => rfl)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ stable' ready arguments callee step =>
      c_call1_step_arm stable' stable ready callee step)
    returns effects

/-- **The C_CALL2 row.** -/
theorem c_call2_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (returns : CcallReturns L P .C_CALL2 (0x80003004#64) 1) (effects : CcallEffects L P .C_CALL2 1) :
    OCaml.OpArm P (OCaml.LoopAt L P) .C_CALL2 :=
  ccall_row_of stable rf fits capacity (by decide) (fun _ _ => rfl)
    (fun s args ne => by
      rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rfl
      · exact absurd rfl (ne a)
      · rfl)
    (fun _ => rfl)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ stable' ready arguments callee step =>
      c_call2_step_arm stable' stable ready arguments callee step)
    returns effects

/-- **The C_CALL3 row.** -/
theorem c_call3_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (returns : CcallReturns L P .C_CALL3 (0x80002fa4#64) 2) (effects : CcallEffects L P .C_CALL3 2) :
    OCaml.OpArm P (OCaml.LoopAt L P) .C_CALL3 :=
  ccall_row_of stable rf fits capacity (by decide) (fun _ _ => rfl)
    (fun s args ne => by
      rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rfl
      · exact absurd rfl (ne a)
      · rfl)
    (fun _ => rfl)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ stable' ready arguments callee step =>
      c_call3_step_arm stable' stable ready arguments callee step)
    returns effects

/-- **The C_CALL4 row.** -/
theorem c_call4_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (returns : CcallReturns L P .C_CALL4 (0x80002f40#64) 3) (effects : CcallEffects L P .C_CALL4 3) :
    OCaml.OpArm P (OCaml.LoopAt L P) .C_CALL4 :=
  ccall_row_of stable rf fits capacity (by decide) (fun _ _ => rfl)
    (fun s args ne => by
      rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rfl
      · exact absurd rfl (ne a)
      · rfl)
    (fun _ => rfl)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ stable' ready arguments callee step =>
      c_call4_step_arm stable' stable ready arguments callee step)
    returns effects

/-- **The C_CALL5 row.** -/
theorem c_call5_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (returns : CcallReturns L P .C_CALL5 (0x80002ed8#64) 4) (effects : CcallEffects L P .C_CALL5 4) :
    OCaml.OpArm P (OCaml.LoopAt L P) .C_CALL5 :=
  ccall_row_of stable rf fits capacity (by decide) (fun _ _ => rfl)
    (fun s args ne => by
      rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rfl
      · exact absurd rfl (ne a)
      · rfl)
    (fun _ => rfl)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ stable' ready arguments callee step =>
      c_call5_step_arm stable' stable ready arguments callee step)
    returns effects

end OCaml.Vm.Sim
