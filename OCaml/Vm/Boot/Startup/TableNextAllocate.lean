import OCaml.Vm.Boot.Startup.TableNext
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast OCaml.Vm.Primitives

/-- The generated request prefix retains all inputs required by the allocator. -/
theorem table_next_allocator_input {c request : Config} {last : Bool} {H capacity ra}
    (ready : TableReady H capacity ra c)
    (post : WriteRegistersPost [10, 9, 1] [] c (tableNextCall last).target 56#64
      ((1, (tableNextCall last).link) :: tableNextRegs) request) :
    AllocatorInput H 56#64 (tableNextCall last).link (firstMallocStack - 32#64) capacity request where
  good := post.vsaOk ready.platform (by decide) (by simp only [keysG, tableNextRegs]; decide)
  readOnly := post.toEffectPost.readOnly_log (by decide) (by decide) ready.readOnly (fun _ _ => trivial)
  room := by
    change vsaRoomB (fun a => (request.σ.mem[a]?).getD 0) H capacity
    rw [post.memory]
    exact ready.room
  request := post.result
  stack := (post.frame .x2 (by decide) (by decide)).trans ready.stack
  link := gholds_lookup _ post.regs (by rfl)
  stackOk := by constructor <;> decide
  high := by decide
  aligned := by cases last <;> decide

/-- A later startup table allocation carries its two generated call seams and
successful library postcondition, with the prior live heap kept abstract. -/
structure TableNextAllocated (H : List (Nat × Nat)) (capacity : Nat) (last : Bool) (before after : Config) where
  request : Config
  atMalloc : Config
  setup : WriteRegistersPost [10, 9, 1] [] before (tableNextCall last).target 56#64
    ((1, (tableNextCall last).link) :: tableNextRegs) request
  dispatch : BoundaryPost [15] request (tableNextCall last).link
    (BitVec.ofNat 64 Layout.sym_malloc) [(15, 0#64)] atMalloc
  allocation : LocalPost startupLive VsaIris.MallocFast.roR VsaIris.Sym.allocText VsaIris.Sym.aRegs
    (mS H (firstMallocStack - 32#64))
    (MallocRoomEnd vsaLayoutP vsaRoomB H 56#64 (tableNextCall last).link (firstMallocStack - 32#64)
      (firstMallocSaved (vsaReg atMalloc)) capacity) atMalloc after

/-- Both later 56-byte requests consume the same successful malloc summary. -/
theorem table_next_allocate (c : Config) (last : Bool) (H : List (Nat × Nat)) (capacity : Nat)
    (ra : BitVec 64) (ready : TableReady H (capacity + 64) ra c) :
    FnSummary (tableNextEntry last) (fun d => d = c) (fun after => Nonempty (TableNextAllocated H capacity last c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, setupRun, setup⟩ := (table_next c last ra ready.toLeafInput ready.globalReg ready.domainWord).run c ⟨pc, rfl⟩
  have input := table_next_allocator_input ready setup
  have leaf : LeafInput (tableNextCall last).link request :=
    ⟨setup.good, setup.image, setup.minstret, input.link, input.aligned, setup.tick⟩
  have pool : LPins8 request.σ.mem Layout.sym_pool (List.replicate 8 0#8) := by
    rw [setup.memory]
    exact ready.poolZero
  have atWrapper : PCAt (BitVec.ofNat 64 Layout.sym_caml_stat_alloc_noexc) request := by
    cases last <;> exact setup.pc
  obtain ⟨atMalloc, dispatchRun, dispatch⟩ := (statAlloc_dispatch request _ leaf pool).run request ⟨atWrapper, rfl⟩
  have mallocInput := statAlloc_allocator_input input dispatch
  obtain ⟨after, allocationRun, allocation⟩ := (allocator_summary atMalloc H 56#64 _ _ capacity 64 mallocInput
    (by constructor <;> decide)).run atMalloc ⟨dispatch.pc, rfl⟩
  exact ⟨after, setupRun.trans (dispatchRun.trans allocationRun), ⟨request, atMalloc, setup, dispatch, allocation⟩⟩
end OCaml.Vm.Boot.Startup
