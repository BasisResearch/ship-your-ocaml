import OCaml.Vm.Sim.ChannelCountFrame
import OCaml.Vm.Sim.ChannelReadiness
import OCaml.Vm.Sim.F1Frame
import OCaml.Vm.Sim.CountedPrimAdapter

/-! Physical accounting at the actual generated C_CALL setup execution. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The setup stores miss the physical custom state. This uses the named
machine premise's footprint separation, rather than readiness or refcounts. -/
theorem Ccall1WriteOk.customCountFrame {P : Prog} {s : St} {c d : Config}
    {pl : Place} {cp : ChanPlace} {sp high domain : Nat} {next env : BitVec 64}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (space : Ccall1WriteOk P s c pl cp sp domain next env)
    (stack : StackRepr c pl sp high s.stack)
    (fits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes)
    (runtime : Gc.f1Layout.runtimeOk c)
    (height : high = Gc.f1High) (dom : domain = Gc.f1Domain)
    (memory : d.σ.mem = writeLog c.σ.mem (ccall1Log sp domain next env)) :
    ChannelCountFrame Customs cp s.world c d := by
  apply ChannelCountFrame.of_log space.payload.channels space.payload.openHead memory
  constructor
  intro n physical
  have domC : (word c Layout.sym_Caml_state).toNat = domain := by
    rw [dom]
    exact Gc.f1_domain runtime
  have stateKept (a : Nat) (ha : state c a) :
      (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := by
    have apart := custom.apart c a ha
    have stackApart := apart.covered
      (Gc.f1High - Layout.stackBytes, Layout.stackBytes) (by
        simp only [Gc.f1Covered, Gc.f1High]
        simp)
      (by decide)
    have domainApart := apart.domainField
    simp only [Gc.domainAddr, domC] at domainApart
    have span := stack.1
    rw [height] at span
    have separated : OutWRange (ccall1Windows sp domain) a 1 := by
      simp only [ccall1Windows, OutWRange, and_true]
      simp only [VsaIris.InExt] at stackApart domainApart
      have offsets : Layout.off_extra_heap_resources_minor + 8 ≤ Layout.off_extern_sp := by decide
      have fieldFits : Layout.off_extern_sp + 8 ≤ Layout.domainStateBytes := by decide
      constructor
      · omega
      · by_cases inDomain : domain ≤ a ∧ a < domain + Layout.domainStateBytes
        · have inExtra := domainApart inDomain
          omega
        · omega
    have outside := outLRange_of_windows (ccall1_log_in next env space.room) separated
    rw [memory, writeLog_out _ _ _ (outL_of_range outside (Nat.le_refl a) (by omega))]
  simpa only [Nat.add_zero] using custom.accounting.frame physical stateKept
    (by rw [word, memory]; exact bytesT_writeLog_out _ space.payload.domain)

/-- The complete counted entry on the same execution as `c_call1_setup`.
No supplier assumes a setup result or a primitive result. -/
theorem counted_c_call1_setup {P : Prog} {s : St} {c d : Config}
    {pl : Place} {cp : ChanPlace} {sp high domain table entry : Nat}
    {value env : BitVec 64} {index : BitVec 32} {name : String}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (h : CcallReady .C_CALL1 Gc.f1Layout P s c pl cp sp high domain table entry value env index name)
    (counts : ChannelCustomsRepr Customs c cp s.world)
    (dp : DispatchPost c .C_CALL1 (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d) :
    ∃ n after, StepsN n d after ∧
      CountedCcallSetupPost Customs (0x80003060#64) [s.accu] Gc.f1Layout P s pl cp sp high domain entry env after ∧
      (runtimeFields after).youngPtr = (runtimeFields c).youngPtr := by
  have height : high = Gc.f1High := h.stackHigh.symm.trans (Gc.f1_stackHigh h.runtime)
  have dom : domain = Gc.f1Domain := by
    have eq := congrArg BitVec.toNat h.domainWord
    have small : domain < 2 ^ 64 := by have := h.space.domainNat; omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at eq
    exact eq.symm.trans (Gc.f1_domain h.runtime)
  have localReady := h.retarget (L' := countedLayout Gc.f1Layout Customs cp s.world)
    ⟨h.runtime, counts⟩ rfl
  have stable : WindowStable (countedLayout Gc.f1Layout Customs cp s.world).runtimeOk
      (ccall1Windows sp domain) := by
    apply (counted_runtimeFrame custom).windows
    intro w hw
    simp only [ccall1Windows, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl ⟨by have := h.stack.1; have := h.stackFits; rw [height] at *; dsimp only; omega,
        by have := h.stack.1; rw [height] at this; dsimp only; omega⟩
    · rw [dom]
      exact Or.inr ⟨Layout.off_extern_sp, by decide, rfl⟩
  obtain ⟨n, after, run, setup, young, memory⟩ := c_call1_setup_framed stable localReady.toArmInput
    h.operand h.nonnegative h.primitive h.entryName h.aligned h.domainWord h.tableWord
    h.targetRead h.value h.environment h.space dp
  exact ⟨n, after, run,
    { toCcallSetupPost := setup.retarget setup.input.runtime.1 rfl
      counts := setup.input.runtime.2 }, young⟩

/-- Successful-state `Fits` supplies readiness at the actual generated call
entry. Opening instantiates `charge` with `openChan_customs`; listing uses
`listRefs_customs`. Neither readiness nor the charge is inferred from refs. -/
theorem counted_c_call1_setup_ready {P : Prog} {s : St} {c d : Config}
    {pl : Place} {cp : ChanPlace} {sp high domain table entry k : Nat}
    {value env : BitVec 64} {index : BitVec 32} {name : String} {heap : Heap} {world : World}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (h : CcallReady .C_CALL1 Gc.f1Layout P s c pl cp sp high domain table entry value env index name)
    (counts : ChannelCustomsRepr Customs c cp s.world)
    (fits : OCaml.Fits Gc.f1Layout.budget P) (succ : CcallSucc P heap world)
    (charge : world.customs = s.world.customs + k)
    (dp : DispatchPost c .C_CALL1 (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d) :
    ∃ n after, StepsN n d after ∧
      CountedCcallSetupPost Customs (0x80003060#64) [s.accu] Gc.f1Layout P s
        pl cp sp high domain entry env after ∧ Ready k after := by
  obtain ⟨n, after, run, setup, _⟩ := counted_c_call1_setup custom h counts dp
  refine ⟨n, after, run, setup, ?_⟩
  exact channel_call_ready custom.accounting setup.counts charge (by
    have bound := succ.customs_bound fits
    exact Nat.le_trans bound (by decide : Gc.f1Layout.budget.customs ≤ Gc.quietBound))

end OCaml.Vm.Sim
