import OCaml.Vm.Gc.MixedRelocated
import OCaml.Vm.Gc.MixedMemory
import OCaml.Vm.Gc.ForwardedSetup

namespace OCaml.Vm.Gc.MixedField
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc LeanRV64DExecutable

/-- Setup establishes the native maps' first member, while its read-only
execution transports all observations used by the mixed suffix. -/
theorem setup_initial {R maps domain a b count before after expected}
    (post : FieldCopy.SetupPost a b count before after)
    (data : LoopData maps domain a b count 1 before expected)
    (initialMap : maps 1 = ForwardedField.setupResult R a b)
    (large : 1 < count)
    (holds : GHolds before.σ (ForwardedField.setupCarried R))
    (code : Code.Caml_oldify_oneLoaded before.σ.mem) :
    LoopAt maps a b count 1 after expected 1 after := by
  apply LoopAt.initial (data.memory_eq post.memory) post.scan.good post.scan.minstret post.scan.tick
    post.scan.code (post.memory ▸ code) large
    (by simpa only [ite_eq_left large] using post.scan.pc)
  rw [initialMap]
  exact ForwardedField.setup_registers post holds

/-- Actual setup followed by the complete mixed copied/forwarded suffix.
All loop inputs are derived from setup and the fixed initial observations. -/
theorem setup_relocated {R maps domain a b fields c expected pl μ cp tag}
    (input : FieldCopy.SetupInput a b fields.length c)
    (data : LoopData maps domain a b fields.length 1 c expected)
    (initialMap : maps 1 = ForwardedField.setupResult R a b)
    (native : GHolds c.σ (ForwardedField.setupCarried R))
    (oldifyCode : Code.Caml_oldify_oneLoaded c.σ.mem)
    (grey : FieldCopy.RelocatingGrey a b fields pl μ c)
    (firstOutside : OutWRange (MopupCall.scanFootprint R b 1 fields.length) b 8)
    (header : HeaderOk (word c (b - 8)) fields.length tag)
    (observed : ∀ i v, fields[i]? = some v → 1 ≤ i →
      expected i = relocWord μ pl v (word c (a + 8 * i))) :
    FnSummary FieldCopy.setupPc (fun d => d = c)
      (ForwardedField.SetupRelocatedPost R a b fields pl μ cp tag c) := by
  constructor
  apply Vsa.Logic.Triple.seq (FieldCopy.setup_machine input).run
  intro middle setup
  have atHead := setup_initial setup data initialMap input.large native oldifyCode
  have header' : HeaderOk (word middle (b - 8)) fields.length tag := by
    simpa only [word, setup.memory] using header
  have observed' : ∀ i v, fields[i]? = some v → 1 ≤ i →
      expected i = relocWord μ pl v (word middle (a + 8 * i)) := by
    intro i v member lower
    simpa only [word, setup.memory] using observed i v member lower
  have footprint : MopupCall.scanFootprint (maps 1) b 1 fields.length =
      MopupCall.scanFootprint R b 1 fields.length := by
    rw [initialMap]
    rfl
  have first : OutWRange (MopupCall.scanFootprint (maps 1) b 1 fields.length) b 8 := by
    simpa only [footprint] using firstOutside
  obtain ⟨after, run, post⟩ := (scan_relocated (cp := cp) (data.memory_eq setup.memory)
    (grey.memory_eq setup.memory) first header' observed') middle atHead
  have scan : FieldCopy.ScanAtWith [1,8,9,10,11,12,14,15] a b fields.length 1 middle fields.length after
      (MopupCall.scanFootprint R b 1 fields.length) expected := footprint ▸ post.loop.scan
  exact ⟨after, run, ForwardedField.setup_result setup scan post.loop.code post.object⟩

end OCaml.Vm.Gc.MixedField
