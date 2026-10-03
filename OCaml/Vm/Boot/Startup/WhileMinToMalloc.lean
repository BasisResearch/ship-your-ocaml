import OCaml.Vm.Boot.Startup.WhileMinFirstCall
import OCaml.Vm.Boot.Startup.DomainPrefix
import OCaml.Vm.Boot.Startup.StatAlloc
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup OCaml.Vm.Primitives

/-- Caml_main's two stack saves frame every initial runtime-global word. -/
theorem camlMainLog_below (ra saved : BitVec 64) (a : Nat)
    (below : a + 8 ≤ Layout.sym_stack_top - 40) :
    OutLRange (camlMainLog camlMainStack ra saved) a 8 := by
  change (a + 8 ≤ Layout.sym_stack_top - 24 ∨ _) ∧
    (a + 8 ≤ Layout.sym_stack_top - 40 ∨ _) ∧ True
  exact ⟨Or.inl (by omega), Or.inl below, True.intro⟩

/-- The actual fresh-domain test remains zero after caml_main's stack stores. -/
theorem ResetDomainWitness.prefixInput {initial atMain atDomain : Config}
    (w : ResetDomainWitness initial atMain atDomain) :
    DomainPrefixInput (camlMainStack - 112#64) jal_80004d94_call.link atDomain where
  toLeafInput := ⟨w.post.good, w.post.image, w.post.minstret,
    gholds_lookup _ w.post.regs (by rfl), by decide, w.post.tick⟩
  stack := gholds_lookup _ w.post.regs (by rfl)
  fresh := by
    rw [w.post.memory]
    exact lpins8_writeLog w.main.post.toCrtCamlMainPost.domain_zero
      (camlMainLog_below _ _ _ (by decide))
  returnSlot := by constructor <;> decide
  imageOutside := by constructor <;> simp only [savedRaLog, OutLRange] <;> decide

structure ResetStatAllocWitness (initial atMain atDomain atAlloc : Config) : Prop where
  domain : ResetDomainWitness initial atMain atDomain
  run : Steps (Vsa.Densify.fillZero initial) atAlloc
  post : WriteRegistersPost [15, 2, 10, 1]
    (savedRaLog (camlMainStack - 112#64) jal_80004d94_call.link) atDomain
    (BitVec.ofNat 64 Layout.sym_caml_stat_alloc_noexc) 928#64
    [(1, jal_8002a8e8_call.link), (2, camlMainStack - 112#64 - 16#64), (10, 928#64)] atAlloc

theorem reset_stat_alloc_exists : ∃ initial atMain atDomain atAlloc,
    ResetStatAllocWitness initial atMain atDomain atAlloc := by
  obtain ⟨initial, atMain, atDomain, w⟩ := reset_domain_exists
  obtain ⟨atAlloc, run, post⟩ :=
    (domain_allocate atDomain _ _ w.prefixInput).run atDomain ⟨w.post.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, atAlloc, w, w.run.trans run, post⟩

theorem ResetStatAllocWitness.pool_zero {initial atMain atDomain atAlloc : Config}
    (w : ResetStatAllocWitness initial atMain atDomain atAlloc) :
    LPins8 atAlloc.σ.mem Layout.sym_pool (List.replicate 8 0#8) := by
  rw [w.post.memory]
  apply lpins8_writeLog
  · rw [w.domain.post.memory]
    exact lpins8_writeLog w.domain.main.post.toCrtCamlMainPost.pool_zero
      (camlMainLog_below _ _ _ (by decide))
  · simp only [savedRaLog, OutLRange]
    decide

/-- Reaches the first real malloc entry with its 928-byte request and native
return link. Establishing the allocator arena is the next function obligation. -/
structure ResetMallocWitness (initial atMain atDomain atAlloc atMalloc : Config) : Prop where
  alloc : ResetStatAllocWitness initial atMain atDomain atAlloc
  run : Steps (Vsa.Densify.fillZero initial) atMalloc
  post : BoundaryPost [15] atAlloc jal_8002a8e8_call.link
    (BitVec.ofNat 64 Layout.sym_malloc) [] atMalloc
  request : gprGet atMalloc.σ 10 = some 928#64
  stack : gprGet atMalloc.σ 2 = some (camlMainStack - 112#64 - 16#64)

theorem reset_malloc_exists : ∃ initial atMain atDomain atAlloc atMalloc,
    ResetMallocWitness initial atMain atDomain atAlloc atMalloc := by
  obtain ⟨initial, atMain, atDomain, atAlloc, w⟩ := reset_stat_alloc_exists
  have leaf : LeafInput jal_8002a8e8_call.link atAlloc :=
    ⟨w.post.good, w.post.image, w.post.minstret,
      gholds_lookup _ w.post.regs (by rfl), by decide, w.post.tick⟩
  obtain ⟨atMalloc, run, post⟩ :=
    (statAlloc_dispatch atAlloc _ leaf w.pool_zero).run atAlloc ⟨w.post.pc, rfl⟩
  refine ⟨initial, atMain, atDomain, atAlloc, atMalloc, w, w.run.trans run, post, ?_, ?_⟩
  · exact (post.frame .x10 (by decide) (by decide)).trans (gholds_lookup (n := 10) _ w.post.regs (by rfl))
  · exact (post.frame .x2 (by decide) (by decide)).trans (gholds_lookup (n := 2) _ w.post.regs (by rfl))
end OCaml.Vm.Boot.WhileMinElfParse
