import OCaml.Vm.Gc.BestFitNext
import OCaml.Vm.Boot.Startup.GprsSame

/-! The next-size small-list route from the bitmap-search return to the
original allocator caller. All later inputs are produced from the entry
memory, represented lists, and the actual preceding machine post. -/
namespace OCaml.Vm.Gc.BestFitNext
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open OCaml.Vm.Boot.Startup

/-- Static footprint of pick and pop; the merge word is distinct from every
list head and the bitmap. -/
def prefixWindows (s : BitVec 64) : List W :=
  [⟨(slotS s).toNat,(slotS s).toNat + 8⟩,
   ⟨(slotS s + 8#64).toNat,(slotS s + 8#64).toNat + 8⟩,
   ⟨Layout.sym_bf_small_map,Layout.sym_bf_small_map + 4⟩]

theorem pick_inside (s : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    LogInW (prefixWindows s) (pickLog s m) := by
  unfold pickLog
  split
  · simp [prefixWindows,LogInW,InsideW]
  · trivial

theorem pop_inside (s b bits : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    LogInW (prefixWindows s) (popLog s b bits m) := by
  unfold popLog
  split <;> simp [prefixWindows,LogInW,InsideW]

theorem prefix_out_heap {s : BitVec 64} {a n : Nat} (small : s.toNat ≤ 16)
    (heap : Vsa.Sim.DlHeap.heapStart ≤ a) : OutWRange (prefixWindows s) a n := by
  have hs := BestFitRemnant.slot_nat small
  have hm := BestFitRemnant.merge_nat small
  change (a+n ≤ (slotS s).toNat ∨ (slotS s).toNat+8 ≤ a) ∧
    (a+n ≤ (slotS s+8#64).toNat ∨ (slotS s+8#64).toNat+8 ≤ a) ∧
    (a+n ≤ Layout.sym_bf_small_map ∨ Layout.sym_bf_small_map+4 ≤ a) ∧ True
  change (BestFitRemnant.slot s).toNat = _ at hs
  change (BestFitRemnant.slot s+8#64).toNat = _ at hm
  simp only [slotS,hs,hm,Vsa.Sim.DlHeap.heapStart,Layout.sym_bf_small_fl,Layout.sym_bf_small_map] at heap ⊢
  exact ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega),True.intro⟩

theorem prefix_out_code {s : BitVec 64} {a : Nat} (small : s.toNat ≤ 16)
    (high : a < 0x8000759c) : OutWRange (prefixWindows s) a 1 := by
  have hs := BestFitRemnant.slot_nat small
  have hm := BestFitRemnant.merge_nat small
  simp only [prefixWindows,slotS,OutWRange,hs,hm,Layout.sym_bf_small_fl,Layout.sym_bf_small_map]
  exact ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega),True.intro⟩

/-- A bounded static-log certificate transports both native code images. -/
theorem prefix_code {s before after log} (small : s.toNat ≤ 16)
    (memory : after = writeLog before log) (inside : LogInW (prefixWindows s) log)
    (allocator : Code.Bf_allocateLoaded before)
    (remnant : Code.Bf_insert_remnant_smallLoaded before) :
    Code.Bf_allocateLoaded after ∧ Code.Bf_insert_remnant_smallLoaded after := by
  have same : ∀ a, a < 0x8000759c → after[a]? = before[a]? := by
    intro a hi
    rw [memory]
    exact writeLog_out _ _ _ (outL_of_range
      (OCaml.Vm.Sim.outLRange_of_windows inside (prefix_out_code small hi)) (by omega) (by omega))
  exact ⟨Code.bf_allocate_transport allocator (fun a _ hi => same a hi),
    Code.bf_insert_remnant_small_transport remnant (fun a _ hi => same a (by omega))⟩

theorem PickPost.read {sp s before after a n} (post : PickPost sp s before after)
    (apart : a+n ≤ (slotS s+8#64).toNat ∨ (slotS s+8#64).toNat+8 ≤ a) :
    bytesT after.σ.mem a n = bytesT before.σ.mem a n := by
  rw [post.memory]
  apply bytesT_writeLog_out
  unfold pickLog
  split
  · exact ⟨apart,True.intro⟩
  · trivial

theorem PickPost.shape {sp s before after lists} (post : PickPost sp s before after)
    (small : s.toNat ≤ 16) (shape : BfShape.SmallShape before.σ.mem lists) :
    BfShape.SmallShape after.σ.mem lists := by
  have hm := BestFitRemnant.merge_nat small
  apply shape.congr
  · intro t lo hi
    apply post.read
    have ht := BfShape.slot_toNat t hi
    change (BestFitRemnant.slot s+8#64).toNat = _ at hm
    rw [ht,show slotS s+8#64 = BestFitRemnant.slot s+8#64 from rfl,hm]
    by_cases eq : t ≤ s.toNat
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · intro t lo hi b hb
    apply post.read
    have heap := shape.heap t lo hi b hb
    change (BestFitRemnant.slot s+8#64).toNat = _ at hm
    rw [show slotS s+8#64 = BestFitRemnant.slot s+8#64 from rfl,hm]
    simp only [Vsa.Sim.DlHeap.heapStart,Layout.sym_bf_small_fl] at heap ⊢
    exact Or.inr (by omega)

/-- The actual pop preserves bitmap consistency in both successor branches. -/
theorem PopPost.map {sp s b bits request before after lists bs}
    (post : PopPost sp s b bits request before after) (lo : 1 ≤ s.toNat) (hi : s.toNat ≤ 16)
    (shape : BfShape.SmallShape before.σ.mem lists) (hb : lists s.toNat = b :: bs)
    (map : BfShape.MapConsistent before.σ.mem lists)
    (bitsRead : bits.setWidth 32 = BfShape.mapBits before.σ.mem) :
    BfShape.MapConsistent after.σ.mem (BfShape.popped lists s.toNat bs) := by
  by_cases empty : nextOf b before.σ.mem = 0#64
  · exact post.map_clear lo hi shape hb map empty bitsRead
  · have bits : BfShape.mapBits after.σ.mem = BfShape.mapBits before.σ.mem := by
      rw [BfShape.mapBits,post.memory,popLog,if_neg empty]
      apply bytesT_writeLog_out
      have hs := BestFitRemnant.slot_nat hi
      exact ⟨Or.inl (by
        change Layout.sym_bf_small_map+4 ≤ (BestFitRemnant.slot s).toNat
        rw [hs]; simp only [Layout.sym_bf_small_map,Layout.sym_bf_small_fl]; omega),True.intro⟩
    have tail : bs ≠ [] := by
      intro nil
      have linked := shape.linked s.toNat lo hi
      rw [hb] at linked
      have rest := linked.2.2
      rw [nil] at rest
      exact empty rest
    intro t lt ht
    rw [bits]
    by_cases same : t = s.toNat
    · subst t
      have old := map s.toNat lo hi
      rw [hb] at old
      simpa only [BfShape.popped,ite_true] using old.trans (iff_of_true (by simp) tail)
    · simpa only [BfShape.popped,if_neg same] using map t lt ht

/-- One entry over the original bitmap-search return memory. Header sizes
come from the represented lists, rather than a later split input. -/
structure RouteInput (sp s b request : BitVec 64) (lists : Nat → List (BitVec 64))
    (bs : List (BitVec 64)) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded c.σ.mem
  remnantCode : Code.Bf_insert_remnant_smallLoaded c.σ.mem
  registers : GHolds c.σ (pickRegs sp s)
  shape : BfShape.SmallShape c.σ.mem lists
  headers : BfShape.SmallHeaders c.σ.mem lists
  map : BfShape.MapConsistent c.σ.mem lists
  selected : lists s.toNat = b :: bs
  small : s.toNat ≤ 16
  requestPositive : 1 ≤ request.toNat
  larger : request.toNat < s.toNat
  savedRequest : bytesT c.σ.mem (sp+8#64).toNat 8 = request
  savedBitmap : (bytesT c.σ.mem sp.toNat 8).setWidth 32 = BfShape.mapBits c.σ.mem
  header : WriteWindow (b-8#64) 8
  remnant : WriteWindow b 8
  stack : WriteWindow sp 8
  requestWord : ReadWindow (sp+8#64) 8
  returnWord : ReadWindow (sp+24#64) 8
  geometry : SplitGeometry sp b
  aligned : (bytesT c.σ.mem (sp+24#64).toNat 8).toNat % 4 = 0

theorem RouteInput.positive {sp s b request lists bs c}
    (input : RouteInput sp s b request lists bs c) : 1 ≤ s.toNat := by
  have := input.larger
  omega

theorem RouteInput.head {sp s b request lists bs c}
    (input : RouteInput sp s b request lists bs c) : headOf s c.σ.mem = b := by
  have linked := input.shape.linked s.toNat input.positive input.small
  rw [input.selected] at linked
  change bytesT c.σ.mem (slotS s).toNat 8 = b
  rw [slotS,BestFitRemnant.slot_eq]
  exact linked.1

theorem RouteInput.size {sp s b request lists bs c}
    (input : RouteInput sp s b request lists bs c) :
    sourceSize (sourceHeader b c.σ.mem) = s := by
  have size := input.headers.sizes s.toNat input.positive input.small b
    (by rw [input.selected]; simp)
  exact size.trans (by simp)

theorem RouteInput.pick_input {sp s b request lists bs c}
    (input : RouteInput sp s b request lists bs c) : PickInput sp s c :=
  ⟨input.good,input.tick,input.minstret,input.code,input.registers,input.positive,input.small,
    input.stack.read,input.requestWord⟩

theorem RouteInput.pop_input {sp s b request lists bs c picked}
    (input : RouteInput sp s b request lists bs c) (post : PickPost sp s c picked) :
    PopInput sp s b (bytesT c.σ.mem sp.toNat 8) request picked := by
  have images := prefix_code input.small post.memory (pick_inside s c.σ.mem) input.code input.remnantCode
  refine ⟨post.good,post.tick,post.minstret,images.1,?_,input.small,?_⟩
  · simpa only [input.head,input.savedRequest] using post.registers
  · exact input.shape.blocks s.toNat input.positive input.small b (by rw [input.selected]; simp)

/-- Every observation outside the static pick/pop windows is read from the
original entry memory, independently of both branch decisions. -/
theorem RouteInput.prefix_read {sp s b request lists bs c picked popped a n}
    (_input : RouteInput sp s b request lists bs c) (first : PickPost sp s c picked)
    (second : PopPost sp s b (bytesT c.σ.mem sp.toNat 8) request picked popped)
    (outside : OutWRange (prefixWindows s) a n) :
    bytesT popped.σ.mem a n = bytesT c.σ.mem a n := by
  rw [second.memory,bytesT_writeLog_out _
    (OCaml.Vm.Sim.outLRange_of_windows (pop_inside s b _ picked.σ.mem) outside),
    first.memory,bytesT_writeLog_out _
    (OCaml.Vm.Sim.outLRange_of_windows (pick_inside s c.σ.mem) outside)]

theorem RouteInput.split_input {sp s b request lists bs c picked popped}
    (input : RouteInput sp s b request lists bs c) (first : PickPost sp s c picked)
    (second : PopPost sp s b (bytesT c.σ.mem sp.toNat 8) request picked popped) :
    SplitInput sp b request popped := by
  have images := prefix_code input.small first.memory (pick_inside s c.σ.mem) input.code input.remnantCode
  have images' := prefix_code input.small second.memory (pop_inside s b _ picked.σ.mem) images.1 images.2
  have header := input.prefix_read (n := 8) first second
    (prefix_out_heap input.small (a := (b-8#64).toNat) (by
      rw [input.geometry.header_nat]
      have := input.geometry.blockHeap; omega))
  have size : sourceSize (sourceHeader b popped.σ.mem) = s := by
    change sourceSize (bytesT popped.σ.mem (b-8#64).toNat 8) = s
    rw [header]
    exact input.size
  refine ⟨second.good,second.tick,second.minstret,images'.1,images'.2,second.registers,
    input.header,input.remnant,input.stack,input.returnWord,input.geometry,input.requestPositive,
    ?_,?_,?_⟩
  · rw [size]; exact input.larger
  · rw [size]; exact input.small
  · rw [input.prefix_read first second (prefix_out_heap input.small (a := (sp+24#64).toNat)
      (by rw [input.geometry.return_nat]; have := input.geometry.stackHeap; omega))]
    exact input.aligned

/-- Shape and map are produced at the actual split entry, including the
nonempty successor case where pop leaves the bitmap unchanged. -/
theorem RouteInput.popped_shape {sp s b request lists bs c picked popped}
    (input : RouteInput sp s b request lists bs c) (first : PickPost sp s c picked)
    (second : PopPost sp s b (bytesT c.σ.mem sp.toNat 8) request picked popped) :
    BfShape.SmallShape popped.σ.mem (BfShape.popped lists s.toNat bs) ∧
      BfShape.MapConsistent popped.σ.mem (BfShape.popped lists s.toNat bs) := by
  have shape := first.shape input.small input.shape
  have bits : BfShape.mapBits picked.σ.mem = BfShape.mapBits c.σ.mem := by
    apply first.read
    have hm := BestFitRemnant.merge_nat input.small
    change (BestFitRemnant.slot s+8#64).toNat = _ at hm
    change _ ≤ (BestFitRemnant.slot s+8#64).toNat ∨ _
    rw [hm]
    exact Or.inl (by simp only [Layout.sym_bf_small_fl,Layout.sym_bf_small_map]; omega)
  have map : BfShape.MapConsistent picked.σ.mem lists := by
    intro t lo hi
    change (BfShape.mapBits picked.σ.mem).getLsbD _ = true ↔ _
    rw [bits]
    exact input.map t lo hi
  exact ⟨second.shape input.small shape input.selected,
    second.map input.positive input.small shape input.selected map (input.savedBitmap.trans bits.symm)⟩

/-- The successive memory snapshots are functions of the original data. -/
def pickedMemory (s : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :=
  writeLog m (pickLog s m)
def poppedMemory (sp s b : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :=
  writeLog (pickedMemory s m) (popLog s b (bytesT m sp.toNat 8) (pickedMemory s m))
def routeLog (sp s b request : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :=
  pickLog s m ++ popLog s b (bytesT m sp.toNat 8) (pickedMemory s m) ++
    completeLog sp b request (poppedMemory sp s b m)

/-- The actual stage posts and split-entry representation, retained for callers
which need the selected branch's precise observations. -/
structure RoutePath (sp s b request : BitVec 64) (lists : Nat → List (BitVec 64))
    (bs : List (BitVec 64)) (before after picked popped : Config) : Prop where
  pick : PickPost sp s before picked
  pop : PopPost sp s b (bytesT before.σ.mem sp.toNat 8) request picked popped
  complete : Complete sp b request popped after
  shape : BfShape.SmallShape popped.σ.mem (BfShape.popped lists s.toNat bs)
  map : BfShape.MapConsistent popped.σ.mem (BfShape.popped lists s.toNat bs)

structure RoutePost (sp s b request : BitVec 64) (lists : Nat → List (BitVec 64))
    (bs : List (BitVec 64)) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  pc : PCAt (bytesT before.σ.mem (sp+24#64).toNat 8) after
  result : gprGet after.σ 10 = some (resultHeader b request (sourceHeader b before.σ.mem))
  stack : gprGet after.σ 2 = some (sp+32#64)
  header : sourceHeader b after.σ.mem = smallHeader request (sourceHeader b before.σ.mem)
  remnantSize : (BestFitRemnant.size b after.σ.mem).toNat = s.toNat-request.toNat-1
  counter : bytesT after.σ.mem Layout.sym_caml_fl_cur_wsz 8 =
    if BestFitRemnant.Inserts b (splitMemory sp b request (poppedMemory sp s b before.σ.mem)) then
      removedCount (bytesT before.σ.mem Layout.sym_caml_fl_cur_wsz 8) (sourceHeader b before.σ.mem) +
        1#64 + BestFitRemnant.size b (splitMemory sp b request (poppedMemory sp s b before.σ.mem))
    else removedCount (bytesT before.σ.mem Layout.sym_caml_fl_cur_wsz 8) (sourceHeader b before.σ.mem)
  memory : after.σ.mem = writeLog before.σ.mem (routeLog sp s b request before.σ.mem)
  code : Code.Bf_allocateLoaded after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : GprsSame before after [1,2,10,11,12,13,14,15,16,17]
  path : ∃ picked popped, RoutePath sp s b request lists bs before after picked popped

/-- Named destruction of the retained stage witnesses. -/
theorem RoutePost.path_spec {sp s b request lists bs before after}
    (post : RoutePost sp s b request lists bs before after) :
    ∃ picked popped, RoutePath sp s b request lists bs before after picked popped := post.path

/-- Adapter from the machine summaries' named register frames to the shared
composition law. No register is threaded individually across the stages. -/
theorem route_gprs {before after : Config} {W : List Nat} (keys : KeysOK W)
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ W, (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r) :
    GprsSame before after W := by
  apply GprsSame.of_regFrame keys
  intro r outside noise
  exact frame r noise (fun n hn => beq_eq_false_iff_ne.mpr (outside n hn))

/-- Single native next-size summary, usable immediately after bitmap search.
Pick repair, empty/nonempty pop, and every remnant wrapper branch are
selected by execution from the original entry memory. -/
theorem allocate_next {sp s b request lists bs c}
    (input : RouteInput sp s b request lists bs c) :
    FnSummary pickPc (fun d => d = c) (RoutePost sp s b request lists bs c) := by
  constructor
  apply Vsa.Logic.Triple.seq (pick input.pick_input).run
  intro picked first
  obtain ⟨popped,popRun,second⟩ := (pop (input.pop_input first)).run picked ⟨first.pc,rfl⟩
  have splitInput := input.split_input first second
  obtain ⟨after,splitRun,last⟩ := (split_return splitInput).run popped ⟨second.pc,rfl⟩
  have shape := input.popped_shape first second
  have snapshot : poppedMemory sp s b c.σ.mem = popped.σ.mem := by
    rw [poppedMemory,show pickedMemory s c.σ.mem = picked.σ.mem from first.memory.symm]
    exact second.memory.symm
  have header : sourceHeader b popped.σ.mem = sourceHeader b c.σ.mem :=
    input.prefix_read first second (prefix_out_heap input.small (by
      rw [input.geometry.header_nat]; have := input.geometry.blockHeap; omega))
  have link : bytesT popped.σ.mem (sp+24#64).toNat 8 = bytesT c.σ.mem (sp+24#64).toNat 8 :=
    input.prefix_read first second (prefix_out_heap input.small (by
      rw [input.geometry.return_nat]; have := input.geometry.stackHeap; omega))
  have count : bytesT popped.σ.mem Layout.sym_caml_fl_cur_wsz 8 =
      bytesT c.σ.mem Layout.sym_caml_fl_cur_wsz 8 := by
    apply input.prefix_read first second
    have hs := BestFitRemnant.slot_nat input.small
    have hm := BestFitRemnant.merge_nat input.small
    simp only [prefixWindows,slotS,OutWRange,hs,hm,Layout.sym_caml_fl_cur_wsz,
      Layout.sym_bf_small_fl,Layout.sym_bf_small_map]
    exact ⟨Or.inl (by omega),Or.inl (by omega),Or.inr (by omega),True.intro⟩
  refine ⟨after,popRun.trans splitRun,⟨last.good,last.tick,last.minstret,?_,?_,last.stack,?_,?_,?_,?_,
    last.code,last.output.trans (second.output.trans first.output),?_,⟨picked,popped,first,second,last,shape.1,shape.2⟩⟩⟩
  · simpa only [link] using last.pc
  · simpa only [header] using last.result
  · exact last.header.trans (congrArg (smallHeader request) header)
  · rw [last.remnant_size splitInput,header,input.size]
  · simpa only [snapshot,header,count] using last.counter
  · rw [last.memory,second.memory,first.memory,routeLog,writeLog_append,writeLog_append]
    rfl
  · exact (((route_gprs (by decide) first.frame).trans (route_gprs (by decide) second.frame)).trans
      (route_gprs (by decide) last.frame)).mono (by decide)

/-- The returned route keeps every selected owned block separated from its
original-data write log. Static and helper effects remain in that exact log. -/
theorem RoutePost.live {sp s b request lists bs before after H}
    (post : RoutePost sp s b request lists bs before after)
    (bounds : ∀ e ∈ H, Vsa.Sim.DlHeap.heapStart ≤ e.1 ∧ e.1+e.2 ≤ Vsa.Sim.DlHeap.heapEnd)
    (outside : ∀ x, x < Vsa.Sim.DlHeap.heapEnd → ¬ VsaIris.VsaHeap.vsaFoot H x →
      OutL (routeLog sp s b request before.σ.mem) x) : LiveFrame H before after := by
  apply LiveFrame.of_foot bounds
  intro x high owned
  rw [post.memory,writeLog_out _ _ _ (outside x high owned)]

end OCaml.Vm.Gc.BestFitNext
