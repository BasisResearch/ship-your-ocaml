import OCaml.Vm.Primitives.Boundary

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- A call prefix/suffix exposes its symbolic register interface as well as
its exact memory effect and complete register/output frame. -/
structure RegistersPost (writes : List Nat) (expectedMem : Std.ExtHashMap Nat (BitVec 8))
    (before : Config) (pc value : BitVec 64) (regs : GRegs) (after : Config) : Prop
    extends EffectPost writes expectedMem before pc value after where
  regs : GHolds after.σ regs

abbrev WriteRegistersPost (writes : List Nat) (log : List WEntry) (before : Config)
    (pc value : BitVec 64) (regs : GRegs) :=
  RegistersPost writes (writeLog before.σ.mem log) before pc value regs

/-- One generated block certificate supplies effects and the retained interface. -/
theorem registers_of_blocks {bs entry before L loads writes pc value regs log}
    (image : ExecutableImage before) (outside : ImageOutside log)
    (S : FnSummary entry (fun c => c = before) (BlockPost bs entry L loads before))
    (hlog : (evalBlocks bs (SegEvalState.init L loads)).log = log)
    (hpc : evalBlocksPC entry (SegEvalState.init L loads) bs = pc)
    (hregs : (evalBlocks bs (SegEvalState.init L loads)).regs = regs)
    (result : lookupG 10 regs = some value)
    (writesOk : ∀ n ∈ wrChain bs, n ∈ writes) :
    FnSummary entry (fun c => c = before) (WriteRegistersPost writes log before pc value regs) := by
  apply S.weaken (fun _ h => h)
  intro after post
  have call := post.effect image outside hlog hpc (fun _ h => by
    rw [hregs] at h
    exact gholds_lookup _ h result) writesOk
  exact ⟨call, hregs ▸ post.regs⟩

/-- Compose exact effects once; every nonwritten register frame follows. -/
theorem EffectPost.trans {w1 w2 m1 m2 before mid after p1 p2 v1 v2}
    (h : EffectPost w1 m1 before p1 v1 mid)
    (h' : EffectPost w2 m2 mid p2 v2 after) :
    EffectPost (w1 ++ w2) m2 before p2 v2 after := by
  refine { h' with
    output := h'.output.trans h.output
    frame := ?_ }
  intro r hr hn
  exact (h'.frame r (fun n hm => hr n (List.mem_append_right _ hm)) hn).trans
    (h.frame r (fun n hm => hr n (List.mem_append_left _ hm)) hn)

/-- A coarser write-set is checked as a finite inclusion certificate. -/
theorem EffectPost.widen {writes writes' mem before after pc value}
    (h : EffectPost writes mem before pc value after)
    (subset : ∀ n ∈ writes, n ∈ writes') : EffectPost writes' mem before pc value after :=
  { h with frame := fun r hr hn => h.frame r (fun n hm => hr n (subset n hm)) hn }

/-- Compose a read-only tail prefix with a callee's abstract write log before
instantiating that log. This keeps memory maps opaque during elaboration. -/
theorem BoundaryPost.then_write {w1 w2 before mid after ra pc regs log target value}
    (h : BoundaryPost w1 before ra pc regs mid)
    (h' : WritePost w2 log mid target value after) :
    WritePost (w1 ++ w2) log before target value after := by
  refine ⟨h'.good, h'.image, h'.minstret, h'.tick, h'.pc, h'.result,
    h'.memory.trans (congrArg (fun m => writeLog m log) h.memory), h'.output.trans h.output, ?_⟩
  intro r hr hn
  exact (h'.frame r (fun n hm => hr n (List.mem_append_right _ hm)) hn).trans
    (h.frame r (fun n hm => hr n (List.mem_append_left _ hm)) hn)

end OCaml.Vm.Primitives
