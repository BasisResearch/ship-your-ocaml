import OCaml.Vm.Gc.ScanPayload

namespace OCaml.Vm.Gc.FieldCopy
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Concrete setup input, after mopup handles the saved first field. The
allocation/queue invariant supplies a multi-field destination header. -/
structure SetupInput (a b count : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  registers : GHolds c.σ (setupRegs (BitVec.ofNat 64 a) (BitVec.ofNat 64 b))
  geometry : Geometry a b count
  large : 1 < count
  header : (word c (b - 8)).toNat / 1024 = count

def setupLoads (b : Nat) (c : Config) := [read8 c.σ.mem (b - 8)]

/-- The one header load and size test have concrete suppliers. -/
theorem setup_access {a b count c} (input : SetupInput a b count c) :
    ChainAccess c.σ.mem (setupRegs (BitVec.ofNat 64 a) (BitVec.ofNat 64 b))
      (setupLoads b c) setupBlocks := by
  apply ChainAccess.cons ?_ ChainAccess.nil
  constructor
  · simp only [setupBlocks, caml_oldify_mopupX9d34FSeg, AccessPlan]
    chain_facts True.intro
    apply (header_window input.geometry.targetRange).ld rfl ?_ ?_
    · simp [eaddrM, mkLine, decodeM, setupRegs, srcVal, lookupG,
        Functions.sign_extend, Sail.BitVec.signExtend, BitVec.sub_eq_add_neg]
    · rw [header_nat input.geometry.targetRange]
      exact read8_pins _ _
  · have size := header_words _ count input.header
    change bytesT c.σ.mem (b - 8) 8 >>> (10 : Nat) = BitVec.ofNat 64 count at size
    have upper := input.geometry.targetRange.upper
    have large := input.large
    simp [setupBlocks, caml_oldify_mopupX9d34FSeg, TermFactsO, TermFactsT,
      runGM, stepGM, setupRegs, setupLoads, stepLdsM, wvalM, srcVal, lookupG,
      eraseG, mkLine, decodeM, Functions.sign_extend, Sail.BitVec.signExtend,
      read8_value, shamtOf, Sail.BitVec.extractLsb, Sail.shift_bits_right,
      size, guardB, Functions.zopz0zKzJ_u,
      Sail.BitVec.toNatInt, BitVec.toNat_ofNat]
    omega

/-- Setup does not write memory; its endpoint establishes the actual scan pins. -/
structure SetupPost (a b count : Nat) (before after : Config) : Prop where
  machine : BlockPost setupBlocks setupPc (setupRegs (BitVec.ofNat 64 a) (BitVec.ofNat 64 b))
    (setupLoads b before) before after
  memory : after.σ.mem = before.σ.mem
  scan : ScanAt a b count 1 after 1 after

theorem setup_machine {a b count c} (input : SetupInput a b count c) :
    FnSummary setupPc (fun d => d = c) (SetupPost a b count c) := by
  have summary := block_summary setupBlocks setupPc
    (setupRegs (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)) (setupLoads b c) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [19,18,24]; decide,
      chainPlan_facts (setup_code input.code) (setup_access input), setup_shape, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory, setup_log]; rfl
  refine ⟨post, memory, ScanAt.initial post.good post.minstret post.tick
    (memory ▸ input.code) (by have := input.large; omega) ?_ ?_⟩
  · simp only [input.large, ite_true, PCAt, post.pc, setup_pc]
  · have regs := setup_registers (segmentPost_of_block post)
    simpa [scanPtr, BitVec.ofNat_add] using regs

/-- The setup and complete integer suffix produce a represented destination
and preserve everything outside the destination suffix, including output. -/
structure ScannedObject (q : PendingCopy) (fields : List Val) (pl : Place)
    (cp : ChanPlace) (tag : Nat) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_mopupLoaded after.σ.mem
  pc : PCAt exitPc after
  object : ObjAt after pl cp q.target.toNat (.block tag fields)
  memory : FrameOn (scanWindow q.target.toNat 1 fields.length) before.σ.mem after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [8, 9, 10, 11, 15, 18], (gprReg n == r) = false) →
      after.σ.regs.get? r = before.σ.regs.get? r

/-- Compose the real setup block and terminating suffix loop. All branch and
load facts come from the represented grey block and its RAM geometry. -/
theorem setup_scan {q : PendingCopy} {fields : List Val} {pl cp tag c}
    (input : SetupInput q.source.toNat q.target.toNat fields.length c)
    (header : HeaderOk (word c (q.target.toNat - 8)) fields.length tag)
    (grey : (pendingPayload q fields).P pl q.target.toNat c)
    (integers : ∀ i v, fields[i]? = some v → 1 ≤ i → ∃ n, v = .int n) :
    FnSummary setupPc (fun d => d = c) (ScannedObject q fields pl cp tag c) := by
  constructor
  apply Vsa.Logic.Triple.seq (setup_machine input).run
  intro middle setup
  have middleGrey : (pendingPayload q fields).P pl q.target.toNat middle := by
    intro i v hi
    change valWord pl v = some (bytesT middle.σ.mem _ 8)
    rw [setup.memory]
    exact grey i v hi
  have middleHeader : HeaderOk (word middle (q.target.toNat - 8)) fields.length tag := by
    change HeaderOk (bytesT middle.σ.mem _ 8) _ _
    rw [setup.memory]
    exact header
  obtain ⟨after, run, post⟩ := (scan_grey (cp := cp) input.geometry middleHeader middleGrey integers)
    middle setup.scan
  refine ⟨after, run, ⟨post.scan.good, post.scan.minstret, post.scan.tick,
    post.scan.code, ?_, post.object, ?_, post.scan.output.trans setup.machine.output, ?_⟩⟩
  · simpa using post.scan.pc
  · simpa only [setup.memory] using post.scan.memory
  · intro r noise untouched
    apply (post.scan.native r noise ?_).trans
      (setup.machine.frame r noise (fun n hn => untouched n (setup_written n hn)))
    intro n hn
    apply untouched n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide

end OCaml.Vm.Gc.FieldCopy
