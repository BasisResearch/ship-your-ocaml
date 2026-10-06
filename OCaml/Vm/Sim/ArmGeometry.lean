import OCaml.Vm.Gc.NurseryTransport

/-!
# The arms' placement geometry: VM stack and nursery

`ArmGeometry` is the stack geometry of a representation witness together
with a6-gc's `NurseryGeometry` (the free nursery misses the represented
payload). It is what `Running.stack` carries, so allocating arms can place
fresh objects (`NurseryGeometry.placement`) and object stores can frame the
runtime invariant (`Gc.f1_objectField`).

Every arm write is either in the VM stack window or in a VM-owned
`Caml_state` field (`VmWindow`); such logs miss the `young_limit`/`young_ptr`
words (`YoungOutside.of_windows`), so the nursery transports exactly as the
stack geometry does.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Gc

/-- The `Caml_state` fields the VM itself writes. -/
def vmDomainOffsets : List Nat :=
  [Layout.off_trapsp, Layout.off_extern_sp, Layout.off_local_roots, Layout.off_exn_bucket,
    Layout.off_external_raise]

/-- A VM-owned write window: inside the VM stack allocation, or one VM
`Caml_state` field. -/
def VmWindow (high domain : Nat) (w : W) : Prop :=
  (high - Layout.stackBytes ≤ w.lo ∧ w.hi ≤ high) ∨
    ∃ off ∈ vmDomainOffsets, w = ⟨domain + off, domain + off + 8⟩

/-- **Arm geometry**: the stack geometry and the nursery geometry of one
representation witness. -/
structure ArmGeometry (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (high : Nat) : Prop extends StackGeometry P s c pl cp high where
  nursery : NurseryGeometry P s c pl cp high

/-- A write log misses the allocation-pointer words. -/
structure YoungOutside (log : List WEntry) (c : Config) : Prop where
  limit : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit) 8
  ptr : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr) 8

/-- Separation from each window of a list is separation from the list. -/
theorem outWRange_of_each {ws : List W} {a n : Nat} (each : ∀ w ∈ ws, OutWRange [w] a n) :
    OutWRange ws a n := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨(each w (by simp)).1, ih fun w' hw => each w' (by simp [hw])⟩

theorem young_field_offsets : ∀ off ∈ [Layout.off_young_limit, Layout.off_young_ptr],
    off + 8 ≤ Layout.domainStateBytes ∧ ∀ o ∈ vmDomainOffsets, off + 8 ≤ o ∨ o + 8 ≤ off := by
  decide

/-- A VM window misses both allocation-pointer words. -/
theorem VmWindow.young {P s c pl cp high} {w : W} (g : StackGeometry P s c pl cp high)
    (vm : VmWindow high (word c Layout.sym_Caml_state).toNat w) {off : Nat}
    (young : off ∈ [Layout.off_young_limit, Layout.off_young_ptr]) :
    OutWRange [w] ((word c Layout.sym_Caml_state).toNat + off) 8 := by
  obtain ⟨fits, apart⟩ := young_field_offsets off young
  rcases vm with ⟨low, high'⟩ | ⟨o, member, rfl⟩
  · obtain ⟨d, -⟩ := g.domain
    simp only [stackWindow] at d
    exact ⟨by omega, trivial⟩
  · have := apart o member
    exact ⟨by dsimp only; omega, trivial⟩

/-- **A log in VM windows misses the allocation pointers.** -/
theorem YoungOutside.of_windows {P s c pl cp high} {ws : List W} {log : List WEntry}
    (g : StackGeometry P s c pl cp high) (inside : LogInW ws log)
    (vm : ∀ w ∈ ws, VmWindow high (word c Layout.sym_Caml_state).toNat w) : YoungOutside log c :=
  ⟨outLRange_of_windows inside (outWRange_of_each fun w hw => (vm w hw).young g (by simp)),
   outLRange_of_windows inside (outWRange_of_each fun w hw => (vm w hw).young g (by simp))⟩

/-- A log in the VM stack window misses the allocation pointers. -/
theorem YoungOutside.of_stack {P s c pl cp high} {log : List WEntry}
    (g : StackGeometry P s c pl cp high) (inside : LogInW [stackWindow high] log) :
    YoungOutside log c :=
  .of_windows g inside fun w hw => by
    simp only [List.mem_singleton] at hw
    subst hw
    exact Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- A log below the stack pointer in the VM stack misses the allocation pointers. -/
theorem YoungOutside.of_free {P s c pl cp sp high} {log : List WEntry}
    (g : StackGeometry P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (inside : LogInW [freeWindow sp high] log) : YoungOutside log c :=
  .of_windows g inside fun w hw => by
    simp only [List.mem_singleton] at hw
    subst hw
    have := stack.1
    exact Or.inl ⟨Nat.le_refl _, by simp only [freeWindow]; omega⟩

/-! ## Transports -/

theorem ArmGeometry.same {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} (g : ArmGeometry P s c pl cp high)
    (heap : s'.heap = s.heap) (world : s'.world = s.world) (memory : c'.σ.mem = c.σ.mem) :
    ArmGeometry P s' c' pl cp high :=
  ⟨g.toStackGeometry.same heap world memory, g.nursery.same heap world memory⟩

theorem ArmGeometry.state {P : Prog} {s s' : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} (g : ArmGeometry P s c pl cp high)
    (heap : s'.heap = s.heap) (world : s'.world = s.world) : ArmGeometry P s' c pl cp high :=
  g.same heap world rfl

theorem ArmGeometry.transport {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} (g : ArmGeometry P s c pl cp high)
    (objects : ∀ l o', s'.heap.get? l = some o' → ∃ o, s.heap.get? l = some o ∧ o.wosize = o'.wosize)
    (chans : s'.world.chans = s.world.chans)
    (domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (prims : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents))
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (ptr : (runtimeFields c').youngPtr = (runtimeFields c).youngPtr) :
    ArmGeometry P s' c' pl cp high :=
  ⟨g.toStackGeometry.transport objects chans domain prims,
   g.nursery.transport objects chans domain prims limit ptr⟩

/-- **Transport across an arm's write log**, which misses the
`Caml_state`/primitive-table pointers and the allocation pointers. -/
theorem ArmGeometry.frame_log {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} {log : List WEntry} (g : ArmGeometry P s c pl cp high)
    (heap : s'.heap = s.heap) (world : s'.world = s.world)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8)
    (young : YoungOutside log c)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : ArmGeometry P s' c' pl cp high :=
  ⟨g.toStackGeometry.frame_log heap world domain contents memory,
   g.nursery.frame_log (fun l o' h => ⟨o', heap ▸ h, rfl⟩) (by rw [world]) domain contents
     young.limit young.ptr memory⟩

/-- **Transport across a log in VM windows.** -/
theorem ArmGeometry.frame_vm {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} {ws : List W} {log : List WEntry} (g : ArmGeometry P s c pl cp high)
    (heap : s'.heap = s.heap) (world : s'.world = s.world)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8)
    (inside : LogInW ws log) (vm : ∀ w ∈ ws, VmWindow high (word c Layout.sym_Caml_state).toNat w)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : ArmGeometry P s' c' pl cp high :=
  g.frame_log heap world domain contents (.of_windows g.toStackGeometry inside vm) memory

/-! ## Allocation -/

/-- **A nursery reservation by an allocating arm's log**: the object of
`size` fields is placed at `a`, reserved below `young_ptr = a + 8 * count`
within capacity, and the log moves `young_ptr` to the header `a - 8` while
keeping `young_limit`. -/
structure NurseryReserve (c : Config) (log : List WEntry) (a size count : Nat) : Prop where
  before : (runtimeFields c).youngPtr = a + 8 * count
  size : size ≤ count
  room : 8 ≤ a
  aligned : (a - 8) % 8 = 0
  capacity : (runtimeFields c).youngLimit ≤ a - 8
  after : ∀ c' : Config, c'.σ.mem = writeLog c.σ.mem log →
    (runtimeFields c').youngPtr = a - 8 ∧ (runtimeFields c').youngLimit = (runtimeFields c).youngLimit

/-- A reserved object is apart from the `Caml_state` record. -/
theorem _root_.OCaml.Vm.Gc.NurseryGeometry.domainApart {P s c pl cp high} {log : List WEntry} {a count : Nat} {o : Obj}
    (g : NurseryGeometry P s c pl cp high) (reserve : NurseryReserve c log a o.wosize count) :
    OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
      (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] (a - 8) (8 * o.wosize + 8) := by
  have := reserve.before
  have := reserve.size
  have := reserve.room
  have apart := apart_of_inside g.domain reserve.capacity
    (y := a - 8) (k := 8 * o.wosize + 8) (by omega)
  exact ⟨by dsimp only; omega, trivial⟩

/-- A reserved object is apart from every channel record. -/
theorem _root_.OCaml.Vm.Gc.NurseryGeometry.channelsApart {P s c pl cp high} {log : List WEntry}
    {a count : Nat} {o : Obj} (g : NurseryGeometry P s c pl cp high)
    (reserve : NurseryReserve c log a o.wosize count) :
    ∀ id ch b, s.world.chans[id]? = some ch → cp id = some b →
      OutWRange [⟨b, b + (chanOffBuff + ch.buffer.length)⟩] (a - 8) (8 * o.wosize + 8) := by
  intro id ch b hch hcp
  have := reserve.before
  have := reserve.size
  have := reserve.room
  have apart := apart_of_inside (g.channels id ch b hch hcp) reserve.capacity
    (y := a - 8) (k := 8 * o.wosize + 8) (by omega)
  exact ⟨by dsimp only; omega, trivial⟩

/-- A reserved object is apart from every primitive entry. -/
theorem _root_.OCaml.Vm.Gc.NurseryGeometry.primsApart {P s c pl cp high} {log : List WEntry}
    {a count : Nat} {o : Obj} (g : NurseryGeometry P s c pl cp high)
    (reserve : NurseryReserve c log a o.wosize count) :
    ∀ i name, P.prims[i]? = some name →
      OutWRange [⟨(word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i,
        (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i + 8⟩]
        (a - 8) (8 * o.wosize + 8) := by
  intro i name hi
  have := reserve.before
  have := reserve.size
  have := reserve.room
  have apart := apart_of_inside (g.primitives i name hi) reserve.capacity
    (y := a - 8) (k := 8 * o.wosize + 8) (by omega)
  exact ⟨by dsimp only; omega, trivial⟩

/-- **Allocation transports the arm geometry**: the fresh object is placed in
the reserved nursery block, and the log otherwise misses the
`Caml_state`/primitive-table pointers. -/
theorem ArmGeometry.alloc_log {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high a count : Nat} {o : Obj} {log : List WEntry} (g : ArmGeometry P s c pl cp high)
    (placed : pl.φ (s.heap.alloc o).2 = some a)
    (reserve : NurseryReserve c log a o.wosize count)
    (heap : s'.heap = (s.heap.alloc o).1) (world : s'.world = s.world)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : ArmGeometry P s' c' pl cp high := by
  have keep : ∀ x, OutLRange log x 8 → word c' x = word c x := fun x h => by
    change bytesT c'.σ.mem x 8 = bytesT c.σ.mem x 8
    rw [memory, bytesT_writeLog_out _ h]
  obtain ⟨ptr, limit⟩ := reserve.after c' memory
  have stack : StackGeometry P s' c pl cp high :=
    g.toStackGeometry.alloc placed
      (g.nursery.placement reserve.before reserve.capacity reserve.room reserve.size)
      (g.nursery.domainApart reserve) (g.nursery.channelsApart reserve) (g.nursery.primsApart reserve)
      heap world
  exact ⟨stack.frame_log rfl rfl domain contents memory,
    g.nursery.alloc placed reserve.size heap (by rw [world]) (keep _ domain) (keep _ contents) limit
      reserve.before ptr reserve.room reserve.aligned reserve.capacity⟩

end OCaml.Vm.Sim
