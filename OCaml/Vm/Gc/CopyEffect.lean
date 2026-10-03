import OCaml.Vm.Gc.FieldStore

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Common observable effect of either verbatim-copy route. The write-set
parameter retains the stronger register frame of the immediate path. -/
structure CopyEffect (written : List Nat) (slot delta target index : BitVec 64)
    (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_mopupLoaded after.σ.mem
  memory : after.σ.mem = writeLog before.σ.mem (copyLog slot delta before)
  pc : PCAt (if again slot delta target index before then pc else exitPc) after
  registers : GHolds after.σ (regs (slot + 8#64) delta target (index + 1#64))
  destination : word after (delta + slot).toNat = word before slot.toNat
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ written, (gprReg n == r) = false) →
      after.σ.regs.get? r = before.σ.regs.get? r

theorem CopyPost.effect {slot delta target index before after}
    (input : Input slot delta target index before) (post : CopyPost slot delta target index before after) :
    CopyEffect [8,9,10,11,15] slot delta target index before after := by
  refine ⟨post.machine.good, post.machine.minstret, post.machine.tick, post.code input,
    post.memory, post.pc, post.scan_regs, post.destination, post.machine.output, ?_⟩
  intro r noise outside
  exact post.machine.frame r noise (fun n hn => outside n (written _ n hn))

theorem StorePost.effect {slot delta target index before after}
    (post : StorePost slot delta target index before after) :
    CopyEffect [8,9,15] slot delta target index before after := by
  refine ⟨post.machine.good, post.machine.minstret, post.machine.tick, post.code,
    post.memory, post.pc, post.registers, post.destination, post.machine.output, ?_⟩
  intro r noise outside
  exact post.machine.frame r noise (fun n hn => outside n (store_written _ n hn))

/-- An even field outside the nursery is read, classified, copied and advanced
by the real machine code. All bound decisions come from concrete domain reads. -/
theorem copy_even {slot delta target index domain c}
    (input : ReadInput slot delta target index c)
    (even : (word c slot.toNat).toNat % 2 = 0)
    (domainReg : gprGet c.σ 22 = some (BitVec.ofNat 64 Layout.sym_Caml_state))
    (root : word c Layout.sym_Caml_state = domain) (windows : Young.Windows domain)
    (outside : ¬ ((Young.lowerWord domain c).toNat < (word c slot.toNat).toNat ∧
      (word c slot.toNat).toNat < (Young.upperWord domain c).toNat))
    (destination : WriteWindow (delta + slot) 8) (header : ReadWindow (target - 8#64) 8) :
    FnSummary pc (fun d => d = c) (CopyEffect [8,9,10,11,14,15] slot delta target index c) := by
  constructor
  apply Vsa.Logic.Triple.seq (classify_field input even domainReg root windows).run
  intro middle classified
  have pc : PCAt storePc middle := by
    simpa only [ite_eq_right outside, Young.copyPc, storePc] using classified.pc
  obtain ⟨after, run, stored⟩ := (store_machine (classified.store_input destination header)).run middle ⟨pc, rfl⟩
  have post := stored.effect
  refine ⟨after, run, ⟨post.good, post.minstret, post.tick, post.code, ?_, ?_, post.registers,
    ?_, post.output.trans classified.output, ?_⟩⟩
  · simpa only [copyLog, word, classified.memory] using post.memory
  · have same : again slot delta target index middle = again slot delta target index c := by
      simp only [again, loads, copyLog, word, classified.memory]
    simpa only [same] using post.pc
  · simpa only [word, classified.memory] using post.destination
  · intro r noise untouched
    apply (post.native r noise ?_).trans (classified.native r noise ?_)
    · intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl <;> exact untouched _ (by decide)
    · intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> exact untouched _ (by decide)

end OCaml.Vm.Gc.FieldCopy
