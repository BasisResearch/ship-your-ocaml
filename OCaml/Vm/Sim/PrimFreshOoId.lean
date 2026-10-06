import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Sim.CcallWriting
import OCaml.Vm.Primitives.CamlFreshOoId
import OCaml.Vm.Gc.F1Runtime

/-! `caml_fresh_oo_id` at a `C_CALL1` site: the counter word is a static
below `.bss`, and every represented object, the VM stack, the domain record,
the channel records and the primitive slots lie above it, so the counter's
store misses them all. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Anything at or above `.bss` misses the counter store. -/
theorem counter_out_above {v : BitVec 64} {x n : Nat} (h : Layout.sym_bss_end ≤ x) :
    OutLRange (counterLog v) x n := by
  have : Layout.sym_oo_last_id + 8 ≤ Layout.sym_bss_end := by decide
  exact ⟨Or.inr (by dsimp only; omega), trivial⟩

/-- A static word other than the counter misses the counter store. -/
theorem counter_out_static {v : BitVec 64} {x : Nat} (h : x + 8 ≤ Layout.sym_oo_last_id ∨ Layout.sym_oo_last_id + 8 ≤ x) :
    OutLRange (counterLog v) x 8 :=
  ⟨by dsimp only; omega, trivial⟩

/-- F1's runtime invariant ignores the counter word (a6-gc's `ignoredStatics`). -/
theorem f1_counterStable : WindowStable Gc.f1Layout.runtimeOk counterWindows := by
  intro c c' frame ok
  apply Gc.f1_ignoredStatic c c' _ ok
  intro a ha
  apply frame a
  have key : ∀ (ws : List W), OutW ws a → ∀ w ∈ ws, a < w.lo ∨ w.hi ≤ a := by
    intro ws
    induction ws with
    | nil => intro _ w hw; cases hw
    | cons w ws ih =>
      intro h w' hw'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · exact h.1
      · exact ih h.2 w' hw'
  exact ⟨key _ ha ⟨Layout.sym_oo_last_id, Layout.sym_oo_last_id + 8⟩ (by simp [Gc.ignoredStatics]), trivial⟩

theorem prim_caml_fresh_oo_id_returns {L : OCaml.Layout} {P : Prog} {ra : BitVec 64}
    (counterStable : WindowStable L.runtimeOk counterWindows) :
    PrimReturnsAt L P .C_CALL1 ra 0 "caml_fresh_oo_id" := by
  intro s c pl cp sp high table entry value env index v heap world reach ready sem
  simp only [List.take_zero] at sem ⊢
  have model : primF1Impl "caml_fresh_oo_id" [s.accu] s.heap s.world =
      .ok (Val.ofInt s.world.ooId) s.heap { s.world with ooId := s.world.ooId + 1 } := rfl
  rw [model] at sem
  injection sem with hv hh hw
  subst hv hh hw
  have hentry : entry = Layout.sym_caml_fresh_oo_id :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_fresh_oo_id)
  subst hentry
  refine ⟨counterWord s.world.ooId, by decide, model, fun c' setup => ?_⟩
  have g := setup.geometry
  have SG := g.toArmGeometry.toStackGeometry
  have fits := ready.stackFits
  have hs := setup.input.data.stack.1
  have statics := SG.statics
  have spLow : Layout.sym_bss_end + 16 ≤ sp := by omega
  have domLow := SG.domainLow
  let log := counterLog (counterWord s.world.ooId)
  have dom : ∀ off, OutLRange log ((word c' Layout.sym_Caml_state).toNat + off) 8 :=
    fun off => counter_out_above (by omega)
  have input : CounterInput L.runtimeOk P s pl cp sp high ra c' :=
    { setup.input with
      bindingsOutside := ⟨counter_out_static (by decide),
        fun i name hi => counter_out_above (by have := SG.primsLow i name hi; omega)⟩
      counter := setup.input.data.world.ooId
      outside := ⟨counter_out_static (by decide), dom _, dom _, counter_out_static (by decide),
        counter_out_static (by decide), counter_out_static (by decide),
        fun i w hi => counter_out_above (by have := SG.codeLow; omega),
        fun i v hi => counter_out_above (by omega),
        fun l a o _ placed object => by
          have := SG.heapLow l a o placed object
          exact ⟨counter_out_above (by omega), counter_out_above (by omega)⟩,
        fun id ch a hch hcp => counter_out_above (SG.channelLow id ch a hch hcp)⟩ }
  have S := caml_fresh_oo_id_primitive counterStable input
  apply ccall_writing_summary (S.weaken (fun _ h => h) (fun _ p => p.toPrimitivePost)) (by decide)
    (fun after m => outsideLog_of_observedLog fun a => by rw [m]) setup.saved
  · have SGc := ready.geometry.toArmGeometry.toStackGeometry
    have dl := SGc.domainLow
    have da := SGc.domainArena
    have sn := ready.space.stackNat
    have he : Vsa.Sim.DlHeap.heapEnd ≤ 2 ^ 64 := by decide
    refine ⟨counter_out_static (by decide), counter_out_above ?_, counter_out_above ?_, counter_out_above ?_⟩
    · have off : Layout.off_extern_sp + 8 ≤ Layout.domainStateBytes := by decide
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      simp only [domainAt] at *
      have := (word c Layout.sym_Caml_state).isLt
      omega
    · rw [BitVec.toNat_ofNat]; omega
    · rw [BitVec.toNat_ofNat]
      simp only [domainAt] at *
      have := (word c Layout.sym_Caml_state).isLt
      omega
  · simp [LogInW, InsideW, counterLog, arenaWindow]; decide
  · intro after frame
    have wordEq : ∀ x, OutLRange log x 8 → word after x = word c' x :=
      fun x h => Reloc.bytesT_congr (copied_of_outsideLog frame h)
    have domEq : word after Layout.sym_Caml_state = word c' Layout.sym_Caml_state :=
      wordEq _ (counter_out_static (by decide))
    have field : ∀ off, domainWord after off = domainWord c' off := by
      intro off
      simp only [domainWord]
      rw [domEq, wordEq _ (dom off)]
    exact g.transport (fun l o' h => ⟨o', h, rfl⟩) rfl domEq (wordEq _ (counter_out_static (by decide)))
      (by simp only [runtimeFields, field]) (by simp only [runtimeFields, field]) rfl
  · exact setup.native

end OCaml.Vm.Sim
