import OCaml.Vm.Gc.ForwardedSetupContext

namespace OCaml.Vm.Gc.ForwardedField
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc LeanRV64DExecutable

/-- Setup and the actual forwarded suffix produce a relocated object with
memory/native frames relative to the pre-setup boundary. -/
structure SetupRelocatedPost (R : Nat → BitVec 64) (a b : Nat) (fields : List Val)
    (pl : Place) (μ : Nat → Nat) (cp : ChanPlace) (tag : Nat) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_mopupLoaded after.σ.mem
  oldifyCode : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt FieldCopy.exitPc after
  object : ObjAt after (reloc μ pl) cp b (.block tag fields)
  memory : FrameOn (MopupCall.scanFootprint R b 1 fields.length) before.σ.mem after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,8,9,10,11,12,14,15,18], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Shared composition of setup's frame with a completed represented scan.
Both forwarded-only and mixed field loops instantiate this adapter. -/
theorem setup_result {R a b fields pl μ cp tag before middle after expected}
    (setup : FieldCopy.SetupPost a b fields.length before middle)
    (scan : FieldCopy.ScanAtWith [1,8,9,10,11,12,14,15] a b fields.length 1 middle fields.length after
      (MopupCall.scanFootprint R b 1 fields.length) expected)
    (code : Code.Caml_oldify_oneLoaded after.σ.mem)
    (object : ObjAt after (reloc μ pl) cp b (.block tag fields)) :
    SetupRelocatedPost R a b fields pl μ cp tag before after := by
  refine ⟨scan.good, scan.minstret, scan.tick, scan.code, code, ?_, object, ?_,
    scan.output.trans setup.machine.output, ?_⟩
  · simpa only [Nat.lt_irrefl, ite_false] using scan.pc
  · simpa only [setup.memory] using scan.memory
  · intro r noise untouched
    apply (scan.native r noise ?_).trans
      (setup.machine.frame_subset FieldCopy.setup_written r noise ?_)
    · intro n member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact untouched _ (by decide)
    · intro n member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact untouched _ (by decide)

/-- Real suffix setup and the terminating already-forwarded scan produce
ObjAt at the relocated placement. Scalar observations are transported over
setup's proved memory identity; no loop-head state is assumed. -/
theorem setup_relocated {R domain a b fields c expected pl μ cp tag}
    (input : FieldCopy.SetupInput a b fields.length c)
    (data : LoopData (setupResult R a b) domain a b fields.length 1 c expected)
    (native : GHolds c.σ (setupCarried R))
    (oldifyCode : Code.Caml_oldify_oneLoaded c.σ.mem)
    (grey : FieldCopy.RelocatingGrey a b fields pl μ c)
    (firstOutside : OutWRange (MopupCall.scanFootprint R b 1 fields.length) b 8)
    (header : HeaderOk (word c (b - 8)) fields.length tag)
    (observed : ∀ i v, fields[i]? = some v → 1 ≤ i →
      expected i = relocWord μ pl v (word c (a + 8 * i))) :
    FnSummary FieldCopy.setupPc (fun d => d = c) (SetupRelocatedPost R a b fields pl μ cp tag c) := by
  constructor
  apply Vsa.Logic.Triple.seq (FieldCopy.setup_machine input).run
  intro middle setup
  have atHead := setup_initial setup data native oldifyCode
  have header' : HeaderOk (word middle (b - 8)) fields.length tag := by
    simpa only [word, setup.memory] using header
  have observed' : ∀ i v, fields[i]? = some v → 1 ≤ i →
      expected i = relocWord μ pl v (word middle (a + 8 * i)) := by
    intro i v member lower
    simpa only [word, setup.memory] using observed i v member lower
  obtain ⟨after, run, post⟩ := (scan_relocated (cp := cp) (data.memory_eq setup.memory)
    (grey.memory_eq setup.memory) firstOutside header' observed') middle atHead
  exact ⟨after, run, setup_result setup post.loop.scan post.loop.code post.object⟩

end OCaml.Vm.Gc.ForwardedField
