import OCaml.Vm.Gc.Generated.Fresh
import OCaml.Vm.Gc.CodeFrame
import OCaml.Vm.Gc.Readback

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The fresh path observes the actual source header once. -/
def loads (source : BitVec 64) (c : Config) := [read8 c.σ.mem (source - 8#64).toNat]

structure Input (source : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (regs source)
  headerRead : ReadWindow (source - 8#64) 8
  nonzero : word c (source - 8#64).toNat ≠ 0
  scanned : (tagWord (word c (source - 8#64).toNat)).toNat ≤ maxScannedTag.toNat

/-- The generated chain reads a nonzero header, takes its scanned-tag arm,
and computes allocation arguments without changing memory. -/
theorem access {source c} (input : Input source c) :
    ChainAccess c.σ.mem (regs source) (loads source c) blocks := by
  refine ChainAccess.cons ⟨?_, ?_⟩ (ChainAccess.cons ⟨?_, ?_⟩
    (ChainAccess.cons ⟨?_, True.intro⟩ ChainAccess.nil))
  · simp only [headerBlock, caml_oldify_oneX9ae4FSeg, List.getD_cons_zero, AccessPlan]
    chain_facts True.intro
    apply input.headerRead.ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, mkLine, decodeM, regs, srcVal, lookupG,
      Functions.sign_extend, Sail.BitVec.signExtend]
    bv_omega
  · rw [header_regs]
    simpa [headerBlock, caml_oldify_oneX9ae4FSeg, TermFactsO, TermFactsT, afterHeader,
      loads, srcVal, lookupG, read8_value, word, guardB] using input.nonzero
  · simp [tagBlock, caml_oldify_oneX9af0TSeg, AccessPlan, MemFacts, mkLine, decodeM]
  · rw [header_regs, tag_regs]
    simpa [tagBlock, caml_oldify_oneX9af0TSeg, TermFactsO, TermFactsT, afterTag, afterHeader,
      loads, srcVal, lookupG, read8_value, word, guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt]
      using input.scanned
  · simp [argsBlock, caml_oldify_oneX9b98Seg, AccessPlan, MemFacts, mkLine, decodeM]

/-- The ordinary scanned-object route is at the allocating JAL with real
size/tag/header arguments. The allocation body and native return are not
premises of this prefix theorem and remain separate proofs. -/
structure Post (source : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs source) (loads source before) before after
  memory : after.σ.mem = before.σ.mem
  pc : PCAt call.pc after
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  registers : GHolds after.σ (arguments source (word before (source - 8#64).toNat))

/-- Actual nonzero-header/tag classifier and allocation argument setup. -/
theorem prepare {source c} (input : Input source c) :
    FnSummary pc (fun d => d = c) (Post source c) := by
  have summary := block_summary blocks pc (regs source) (loads source c) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [8,19]; decide,
      chainPlan_facts (code_facts input.code) (access input), chain_ok, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory, no_stores]; rfl
  refine ⟨post, memory, ?_, memory ▸ input.code, ?_⟩
  · rw [PCAt, post.pc, endpoint]
  · have pins := post.regs
    rw [Fresh.registers] at pins
    simpa only [loads, List.headD_cons, read8_value, word] using pins

/-- HeaderOk's typed tag agrees with the byte mask used by the machine. -/
theorem tagWord_nat (hd : BitVec 64) : (tagWord hd).toNat = hd.toNat % 256 := by
  rw [tagWord, BitVec.toNat_and]
  change hd.toNat &&& (2^8 - 1) = hd.toNat % 2^8
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- HeaderOk's word size agrees with the machine's logical shift. -/
theorem sizeWord_nat (hd : BitVec 64) : (sizeWord hd).toNat = hd.toNat / 1024 :=
  Nat.shiftRight_eq_div_pow hd.toNat 10

theorem arguments_of_header {hd : BitVec 64} {size tag : Nat} (header : HeaderOk hd size tag) :
    sizeWord hd = BitVec.ofNat 64 size ∧ tagWord hd = BitVec.ofNat 64 tag := by
  constructor
  · have same := congrArg (BitVec.ofNat 64) ((sizeWord_nat hd).trans header.2)
    simpa using same
  · have same := congrArg (BitVec.ofNat 64) ((tagWord_nat hd).trans header.1)
    simpa using same

/-- A nonempty object with a tag below Infix_tag meets the concrete fresh
classifier conditions; no preselected control-flow outcome is assumed. -/
theorem header_conditions {hd : BitVec 64} {size tag : Nat}
    (header : HeaderOk hd size tag) (positive : 0 < size) (scanned : tag < 249) :
    hd ≠ 0 ∧ (tagWord hd).toNat ≤ maxScannedTag.toNat := by
  constructor
  · intro zero
    have size := header.2
    rw [zero] at size
    change 0 / 1024 = _ at size
    omega
  · rw [tagWord_nat, header.1]
    change tag ≤ 248
    omega

end OCaml.Vm.Gc.Fresh
