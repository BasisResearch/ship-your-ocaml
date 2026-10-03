import OCaml.Vm.Gc.FieldRead

namespace OCaml.Vm.Gc.FieldCopy
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

theorem ReadPost.continuation {slot delta target index before after}
    (post : ReadPost slot delta target index before after) :
    GHolds after.σ (continuationRegs slot delta target index (word before slot.toNat)) := by
  apply gholds_select post.registers
  intro n v member
  simp only [continuationRegs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h <;> cases h <;> rfl

theorem classifier_continuation {value domain before after slot delta target index}
    (post : Young.Result value domain before after)
    (registers : GHolds before.σ (continuationRegs slot delta target index value)) :
    GHolds after.σ (continuationRegs slot delta target index value) := by
  apply gholds_of_frame post.machine.frame _ (by change KeysOK [11,10,8,18,19,9]; decide) ?_ ?_ registers
  · change ∀ n ∈ [11,10,8,18,19,9], ∀ q ∈ noiseRegs, (q == gprReg n) = false
    decide
  · have safe : ∀ n ∈ [11,10,8,18,19,9], ∀ m ∈ [14,15], (gprReg m == gprReg n) = false := by decide
    intro n hn m hm
    exact safe n hn m (Young.written _ _ m hm)

theorem immediate_of_even {slot c} (even : (word c slot.toNat).toNat % 2 = 0) :
    immediate slot c = false := by
  have low : word c slot.toNat &&& 1#64 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_and] using even
  simp [immediate, low, guardB]

/-- The field is loaded and classified, with its destination and scan state
still available to whichever concrete continuation is selected. -/
structure ClassifiedPost (slot delta target index domain : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_mopupLoaded after.σ.mem
  pc : PCAt (if (Young.lowerWord domain before).toNat < (word before slot.toNat).toNat ∧
      (word before slot.toNat).toNat < (Young.upperWord domain before).toNat
    then Young.oldifyPc else Young.copyPc) after
  registers : GHolds after.σ (continuationRegs slot delta target index (word before slot.toNat))
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [10,11,14,15], (gprReg n == r) = false) →
      after.σ.regs.get? r = before.σ.regs.get? r

/-- Compose the real field load/parity branch and both young-range tests.
Evenness supplies the tag branch; concrete domain reads supply all range choices. -/
theorem classify_field {slot delta target index domain c}
    (input : ReadInput slot delta target index c)
    (even : (word c slot.toNat).toNat % 2 = 0)
    (domainReg : gprGet c.σ 22 = some (BitVec.ofNat 64 Layout.sym_Caml_state))
    (root : word c Layout.sym_Caml_state = domain) (windows : Young.Windows domain) :
    FnSummary pc (fun d => d = c) (ClassifiedPost slot delta target index domain c) := by
  constructor
  apply Vsa.Logic.Triple.seq (read_machine input).run
  intro middle read
  have pc : PCAt Young.pc middle := by
    simpa only [immediate_of_even even, Bool.false_eq_true, ite_false, pointerPc, Young.pc] using read.pc
  obtain ⟨after, run, post⟩ := (Young.classify (read.young_input domainReg root windows)).run middle ⟨pc, rfl⟩
  refine ⟨after, run, ⟨post.machine.good, post.machine.minstret, post.machine.tick,
    post.code, ?_, classifier_continuation post read.continuation, post.memory.trans read.memory,
    post.machine.output.trans read.machine.output, ?_⟩⟩
  · have endpoint := post.pc
    simp only [Young.lowerWord, Young.upperWord, word, read.memory] at endpoint ⊢
    split at endpoint <;> rename_i h <;> simpa only [h, and_self, ite_true, ite_false] using endpoint
  · intro r noise untouched
    apply (post.machine.frame r noise ?_).trans (read.machine.frame r noise ?_)
    · intro n hn
      have written := Young.written _ _ n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at written
      rcases written with rfl | rfl <;> exact untouched _ (by decide)
    · intro n hn
      have written := read_written _ n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at written
      rcases written with rfl | rfl | rfl <;> exact untouched _ (by decide)

/-- End-to-end nonpointer branch consequence for the loaded field. -/
theorem ClassifiedPost.copy_nonpointer {slot delta target index domain before after P s pl v}
    (post : ClassifiedPost slot delta target index domain before after)
    (safe : NoForgery P s pl (Young.lowerWord domain before).toNat (Young.upperWord domain before).toNat)
    (scanned : Scanned P s v) (nonpointer : v.loc? = none)
    (represented : valWord pl v = some (word before slot.toNat))
    (even : (word before slot.toNat).toNat % 2 = 0) : PCAt Young.copyPc after := by
  simpa only [ite_eq_right (Young.nonpointer_outside safe scanned nonpointer represented even)] using post.pc

end OCaml.Vm.Gc.FieldCopy
