import OCaml.Vm.Gc.FreshEntry

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The actual computed ABI arguments denote the typed source object's
word size and tag, with its original header supplied as the third argument. -/
theorem Prepared.typed_arguments {R before after exitPC writes size tag}
    (post : Prepared R before after exitPC writes)
    (header : HeaderOk (word before (R 10 - 8#64).toNat) size tag) :
    GHolds after.σ [(10,BitVec.ofNat 64 size),(11,BitVec.ofNat 64 tag),
      (12,word before (R 10 - 8#64).toNat)] := by
  obtain ⟨sizeWord,tagWord⟩ := arguments_of_header header
  have pins : GHolds after.σ [(10,Fresh.sizeWord (word before (R 10 - 8#64).toNat)),
      (11,Fresh.tagWord (word before (R 10 - 8#64).toNat)), (12,word before (R 10 - 8#64).toNat)] :=
    ⟨gholds_lookup _ post.arguments rfl, gholds_lookup _ post.arguments rfl,
      gholds_lookup _ post.arguments rfl, True.intro⟩
  simpa only [sizeWord,tagWord] using pins

/-- The allocator entry retains the oldify frame and its own actual return link. -/
structure AllocationEntry (R : Nat → BitVec 64) (before after : Config) : Prop
    extends Prepared R before after allocationPc (1 :: prepareWrites) where
  link : gprGet after.σ 1 = some call.link

/-- Execute the allocating JAL from the fully prepared prefix. The saved
oldify caller frame remains in memory; this JAL installs the allocation
return link and retains every allocation/update argument. -/
theorem Prepared.enter_allocator {R before middle} (post : Prepared R before middle) :
    FnSummary call.pc (fun d => d = middle)
      (AllocationEntry R before) := by
  let pins := Fresh.arguments (R 10) (word before (R 10 - 8#64).toNat) ++ allocationCarried R
  have holds : GHolds middle.σ pins := (gholds_append _ _).mpr ⟨post.arguments, post.carried⟩
  have summary := call_summary call_shape call_decode middle (call_pins post.code) post.good post.tick
    post.minstret pins holds (by change KeysOK [10,25,11,24,12,8,19,2,9,18,19,20,21,22,23]; decide)
    (by change ∀ n ∈ [10,25,11,24,12,8,19,2,9,18,19,20,21,22,23], n ≠ 1; decide)
  apply summary.weaken (fun _ h => h)
  intro after called
  have split := (gholds_append _ _).mp called.registers
  have memory : after.σ.mem = middle.σ.mem := called.mem
  refine ⟨?_, called.ra⟩
  refine ⟨called.good, called.minstret, called.tick, memory ▸ post.code,
    memory.trans post.memory, ?_, split.1, split.2, ?_, called.output.trans post.output, ?_⟩
  · simpa only [PCAt, call_target] using called.pc
  · intro cell member
    simpa only [word, memory] using post.saved cell member
  · intro r noise outside
    apply (called.frame r noise (by simp [wrChain]) (outside 1 (by simp))).trans
    exact post.native r noise (fun n hn => outside n (List.mem_cons_of_mem _ hn))

/-- Fresh scanned-object oldify entry reaches the allocator's actual entry
PC through the decoded JAL. The allocator body remains an open obligation. -/
theorem prepare_allocation {R domain size tag c} (input : EntryInput R domain size tag c) :
    FnSummary OldifyEntry.pc (fun d => d = c)
      (AllocationEntry R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_entry input).run
  intro middle post
  exact post.enter_allocator.run middle ⟨post.pc,rfl⟩

end OCaml.Vm.Gc.Fresh
