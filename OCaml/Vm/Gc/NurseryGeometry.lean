import OCaml.Vm.Gc.G1Room
import OCaml.Vm.Sim.InvariantUse
import OCaml.Vm.Sim.NurseryInput

/-!
# The running invariant: nursery geometry (G1 allocation fast path)

The nursery counterpart of a1-arms' `StackGeometry`. An allocating arm
reserves its block in the free part of the nursery, `[young_limit, young_ptr)`
(`nurseryFree`), and initializes it there. `WindowSeparated w` says a window
misses every observed part of the represented payload (statics, `Caml_state`,
code, the live stack, live heap objects, channels, primitive entries);
`WindowSeparated.payload`/`image`/`bindings` turn a log inside `w` into the
`PayloadOutside`/`ImageOutside`/`BindingsOutside` certificates, for any window.
`NurseryGeometry` instantiates it with `nurseryFree` and adds the RAM bounds
from which `header_write`, `young_write`, `limit_read` give the RAM-access
fields of `Sim.NurseryInput`. `reserve` re-establishes the geometry after a
reservation: the free window shrinks, and the new block lies outside it.
-/

namespace OCaml.Vm.Gc
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Sim OCaml.Vm.Primitives

/-- A window missing every observation of the represented payload. -/
structure WindowSeparated (w : W) (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (high : Nat) : Prop where
  /-- above `.bss` (hence above the image, `tohost` and every static variable) -/
  statics : Layout.sym_bss_end ≤ w.lo
  domain : OutWRange [w] (word c Layout.sym_Caml_state).toNat Layout.domainStateBytes
  stack : OutWRange [w] (high - Layout.stackBytes) Layout.stackBytes
  code : ∀ i v, P.code[i]? = some v → OutWRange [w] (pl.codeBase + 4 * i) 4
  /-- every placed object (live or not, as in `StackGeometry`) -/
  heap : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o → OutWRange [w] (a - 8) (8 * o.wosize + 8)
  channels : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    OutWRange [w] a (chanOffBuff + ch.buffer.length)
  primitives : ∀ i name, P.prims[i]? = some name →
    OutWRange [w] ((word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i) 8

theorem window_static {w : W} {a n : Nat} (g : Layout.sym_bss_end ≤ w.lo)
    (static : a + n ≤ Layout.sym_bss_end) : OutWRange [w] a n :=
  ⟨Or.inl (by omega), trivial⟩

/-- A subrange of a separated range is separated. -/
theorem outW_sub {w : W} {a n b k : Nat} (h : OutWRange [w] a n) (low : a ≤ b) (high : b + k ≤ a + n) :
    OutWRange [w] b k := by
  obtain ⟨h, -⟩ := h
  exact ⟨by omega, trivial⟩

/-- **Writes inside a separated window miss the represented payload.** -/
theorem WindowSeparated.payload {w : W} {P s c pl cp sp high} {log : List WEntry}
    (g : WindowSeparated w P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (space : high - Layout.stackBytes ≤ sp) (inside : LogInW [w] log) : PayloadOutside log P s c pl cp sp := by
  have hs := stack.1
  have static : ∀ a, a + 8 ≤ Layout.sym_bss_end → OutLRange log a 8 :=
    fun a ha => outLRange_of_windows inside (window_static g.statics ha)
  have domainField : ∀ off, off + 8 ≤ Layout.domainStateBytes →
      OutLRange log ((word c Layout.sym_Caml_state).toNat + off) 8 :=
    fun off hoff => outLRange_of_windows inside (outW_sub g.domain (by omega) (by omega))
  refine ⟨static _ (by decide), domainField _ (by decide), domainField _ (by decide),
    static _ (by decide), static _ (by decide), static _ (by decide), ?_, ?_, ?_, ?_⟩
  · exact fun i v hv => outLRange_of_windows inside (g.code i v hv)
  · intro i v hv
    have bound : i < s.stack.length := (List.getElem?_eq_some_iff.1 hv).1
    exact outLRange_of_windows inside (outW_sub g.stack (by omega) (by omega))
  · intro l a o live placed object
    have ho := g.heap l a o placed object
    exact ⟨outLRange_of_windows inside (outW_sub ho (by omega) (by omega)),
      outLRange_of_windows inside (outW_sub ho (by omega) (by omega))⟩
  · exact fun id ch a hch hcp => outLRange_of_windows inside (g.channels id ch a hch hcp)

theorem WindowSeparated.image {w : W} {P s c pl cp high} {log : List WEntry}
    (g : WindowSeparated w P s c pl cp high) (inside : LogInW [w] log) : ImageOutside log :=
  ⟨outLRange_of_windows inside (window_static g.statics (by decide)),
   outLRange_of_windows inside (window_static g.statics (by decide))⟩

theorem WindowSeparated.bindings {w : W} {P s c pl cp high} {log : List WEntry}
    (g : WindowSeparated w P s c pl cp high) (inside : LogInW [w] log) : BindingsOutside log P c :=
  ⟨outLRange_of_windows inside (window_static g.statics (by decide)),
    fun i name h => outLRange_of_windows inside (g.primitives i name h)⟩

/-- The unallocated nursery, `[young_limit, young_ptr)`. -/
def nurseryFree (c : Config) : W := ⟨(runtimeFields c).youngLimit, (runtimeFields c).youngPtr⟩

/-- **Nursery geometry**: the free nursery misses the represented payload and
lies in RAM; the `Caml_state` record lies in aligned RAM above `tohost`. -/
structure NurseryGeometry (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (high : Nat) : Prop extends WindowSeparated (nurseryFree c) P s c pl cp high where
  top : (runtimeFields c).youngPtr ≤ 0x100000000
  aligned : (runtimeFields c).youngPtr % 8 = 0
  domainLow : Layout.sym_tohost + 16 ≤ (word c Layout.sym_Caml_state).toNat
  domainHigh : (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes ≤ 0x100000000
  domainAligned : (word c Layout.sym_Caml_state).toNat % 8 = 0
  /-- the whole loaded code buffer, the atom table, and the allocator arena's end -/
  codeRange : OutWRange [nurseryFree c] pl.codeBase (4 * P.code.size)
  atoms : OutWRange [nurseryFree c] pl.atomBase atomTableBytes
  arena : (runtimeFields c).youngPtr ≤ Vsa.Sim.DlHeap.heapEnd

/-- An aligned `Caml_state` word is writable RAM. -/
theorem NurseryGeometry.domain_write {P s c pl cp high} (g : NurseryGeometry P s c pl cp high)
    {off : Nat} (fits : off + 8 ≤ Layout.domainStateBytes) (offAligned : off % 8 = 0) :
    RamWriteAt ((word c Layout.sym_Caml_state).toNat + off) 8 := by
  have hl := g.domainLow
  have hh := g.domainHigh
  have ha := g.domainAligned
  have hb : 0x80000000 ≤ Layout.sym_tohost := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tohostAddr, ← mailbox_layout] at * <;> omega

/-- `NurseryInput.youngWrite`. -/
theorem NurseryGeometry.young_write {P s c pl cp high} (g : NurseryGeometry P s c pl cp high) :
    RamWriteAt ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr) 8 :=
  g.domain_write (by decide) (by decide)

/-- `NurseryInput.limitRead`. -/
theorem NurseryGeometry.limit_read {P s c pl cp high} (g : NurseryGeometry P s c pl cp high) :
    RamReadAt ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit) 8 :=
  (g.domain_write (by decide) (by decide)).read

/-- `NurseryInput.headerWrite`: the header of a block reserved below
`young_ptr = a + 8 * count`, within capacity, is writable RAM. -/
theorem NurseryGeometry.header_write {P s c pl cp high} (g : NurseryGeometry P s c pl cp high)
    {count a : Nat} (young : (runtimeFields c).youngPtr = a + 8 * count)
    (capacity : (runtimeFields c).youngLimit ≤ a - 8) (room : 8 ≤ a) : RamWriteAt (a - 8) 8 := by
  have hs := g.statics
  have ht := g.top
  have hal := g.aligned
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have hr : 0x80000000 ≤ Layout.sym_tohost := by decide
  simp only [nurseryFree] at hs
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tohostAddr, ← mailbox_layout] at * <;> omega

/-- The reserved block `[a - 8, a + 8 * count)` lies in the free nursery, so
its initializing writes miss the payload (`WindowSeparated.payload`). -/
theorem reserved_inside {c : Config} {count a : Nat} (young : (runtimeFields c).youngPtr = a + 8 * count)
    (capacity : (runtimeFields c).youngLimit ≤ a - 8) {b k : Nat}
    (low : a - 8 ≤ b) (high : b + k ≤ a + 8 * count) : InsideW [nurseryFree c] b k :=
  Or.inl ⟨by simp only [nurseryFree]; omega, by simp only [nurseryFree]; omega⟩

/-- After the reservation the free window ends at `a - 8`, so the new block
lies outside it (`OutWRange.shrink` keeps the older separations). -/
theorem reserve_outside {c' : Config} {count a : Nat}
    (after : (runtimeFields c').youngPtr = a - 8) :
    OutWRange [nurseryFree c'] (a - 8) (8 * count + 8) :=
  ⟨Or.inr (by simp only [nurseryFree, after]; omega), trivial⟩

/-- A range separated from the old free window is separated from the shrunk one. -/
theorem OutWRange.shrink {c c' : Config} {x n : Nat}
    (h : OutWRange [nurseryFree c] x n)
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (lower : (runtimeFields c').youngPtr ≤ (runtimeFields c).youngPtr) :
    OutWRange [nurseryFree c'] x n := by
  obtain ⟨h, -⟩ := h
  simp only [nurseryFree] at h
  exact ⟨by simp only [nurseryFree, limit]; omega, trivial⟩

/-- A range inside the free nursery misses any range separated from it. -/
theorem apart_of_inside {c : Config} {x n y k : Nat} (outside : OutWRange [nurseryFree c] x n)
    (low : (runtimeFields c).youngLimit ≤ y) (high : y + k ≤ (runtimeFields c).youngPtr) :
    y + k ≤ x ∨ x + n ≤ y := by
  obtain ⟨h, -⟩ := outside
  simp only [nurseryFree] at h
  omega

/-- **`NurseryPlacement` for a nursery reservation**: an object of at most
`count` fields reserved below `young_ptr = a + 8 * count`, within capacity. -/
theorem NurseryGeometry.placement {P s c pl cp high} (g : NurseryGeometry P s c pl cp high)
    {count a : Nat} {o : Obj} (young : (runtimeFields c).youngPtr = a + 8 * count)
    (capacity : (runtimeFields c).youngLimit ≤ a - 8) (room : 8 ≤ a) (size : o.wosize ≤ count) :
    NurseryPlacement P pl high a o := by
  have statics := g.statics
  have arena := g.arena
  simp only [nurseryFree] at statics
  have low : (runtimeFields c).youngLimit ≤ a - 8 := capacity
  have high' : a - 8 + (8 * o.wosize + 8) ≤ (runtimeFields c).youngPtr := by omega
  refine ⟨⟨?_, trivial⟩, by omega, by omega, ⟨?_, trivial⟩, ⟨?_, trivial⟩⟩
  · have := apart_of_inside g.stack low high'
    simp only [stackWindow]
    omega
  · have := apart_of_inside g.codeRange low high'
    omega
  · have := apart_of_inside g.atoms low high'
    omega

/-- **Transport** across a step that keeps object sizes, channels, the
`Caml_state` and primitive-table pointers, and the `young_limit`/`young_ptr`
words (every non-allocating arm), mirroring `StackGeometry.transport`. -/
theorem NurseryGeometry.transport {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} (g : NurseryGeometry P s c pl cp high)
    (objects : ∀ l o', s'.heap.get? l = some o' → ∃ o, s.heap.get? l = some o ∧ o.wosize = o'.wosize)
    (chans : s'.world.chans = s.world.chans)
    (domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (prims : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents))
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (ptr : (runtimeFields c').youngPtr = (runtimeFields c).youngPtr) :
    NurseryGeometry P s' c' pl cp high := by
  have window : nurseryFree c' = nurseryFree c := by simp only [nurseryFree, limit, ptr]
  exact {
    statics := by rw [window]; exact g.statics
    domain := by rw [window, domain]; exact g.domain
    stack := by rw [window]; exact g.stack
    code := by rw [window]; exact g.code
    heap := fun l a o' placed object => by
      obtain ⟨o, ho, size⟩ := objects l o' object
      rw [window, ← size]; exact g.heap l a o placed ho
    channels := by rw [window, chans]; exact g.channels
    primitives := by rw [window, prims]; exact g.primitives
    top := by rw [ptr]; exact g.top
    aligned := by rw [ptr]; exact g.aligned
    domainLow := by rw [domain]; exact g.domainLow
    domainHigh := by rw [domain]; exact g.domainHigh
    domainAligned := by rw [domain]; exact g.domainAligned
    codeRange := by rw [window]; exact g.codeRange
    atoms := by rw [window]; exact g.atoms
    arena := by rw [ptr]; exact g.arena }

/-- **Transport across a write log** missing the `Caml_state` and
primitive-table pointers and the `young_limit`/`young_ptr` words (VM-stack
stores, object field stores, other `Caml_state` fields). -/
theorem NurseryGeometry.frame_log {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} {log : List WEntry} (g : NurseryGeometry P s c pl cp high)
    (objects : ∀ l o', s'.heap.get? l = some o' → ∃ o, s.heap.get? l = some o ∧ o.wosize = o'.wosize)
    (chans : s'.world.chans = s.world.chans)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8)
    (limit : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit) 8)
    (ptr : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr) 8)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : NurseryGeometry P s' c' pl cp high := by
  have keep : ∀ x, OutLRange log x 8 → word c' x = word c x := fun x h => by
    change bytesT c'.σ.mem x 8 = bytesT c.σ.mem x 8
    rw [memory, bytesT_writeLog_out _ h]
  have dom := keep _ domain
  refine g.transport objects chans dom (keep _ contents) ?_ ?_
  · simp only [runtimeFields, domainWord, dom]; rw [keep _ limit]
  · simp only [runtimeFields, domainWord, dom]; rw [keep _ ptr]

/-- **Allocation** of `o` at a reserved address `a`: the free window shrinks
to end at `a - 8`, and the new object lies outside it. -/
theorem NurseryGeometry.alloc {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high count a : Nat} {o : Obj} (g : NurseryGeometry P s c pl cp high)
    (placed : pl.φ (s.heap.alloc o).2 = some a) (size : o.wosize ≤ count)
    (heap : s'.heap = (s.heap.alloc o).1) (chans : s'.world.chans = s.world.chans)
    (domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (prims : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents))
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (before : (runtimeFields c).youngPtr = a + 8 * count)
    (after : (runtimeFields c').youngPtr = a - 8) (room : 8 ≤ a) (aligned : (a - 8) % 8 = 0) :
    NurseryGeometry P s' c' pl cp high := by
  have lower : (runtimeFields c').youngPtr ≤ (runtimeFields c).youngPtr := by omega
  have sh : ∀ {x n}, OutWRange [nurseryFree c] x n → OutWRange [nurseryFree c'] x n :=
    fun h => OutWRange.shrink h limit lower
  exact {
    statics := by simp only [nurseryFree, limit]; exact g.statics
    domain := by rw [domain]; exact sh g.domain
    stack := sh g.stack
    code := fun i v hv => sh (g.code i v hv)
    heap := fun l a' o' found object => by
      rw [heap] at object
      rcases heap_alloc_get object with old | ⟨rfl, rfl⟩
      · exact sh (g.heap l a' o' found old)
      · rw [placed] at found
        cases found
        have := reserve_outside (c' := c') (count := o'.wosize) after
        simpa only [Nat.add_comm] using this
    channels := by rw [chans]; exact fun id ch x h1 h2 => sh (g.channels id ch x h1 h2)
    primitives := by rw [prims]; exact fun i name h => sh (g.primitives i name h)
    top := by have := g.top; omega
    aligned := by rw [after]; exact aligned
    domainLow := by rw [domain]; exact g.domainLow
    domainHigh := by rw [domain]; exact g.domainHigh
    domainAligned := by rw [domain]; exact g.domainAligned
    codeRange := sh g.codeRange
    atoms := sh g.atoms
    arena := by have := g.arena; omega }

end OCaml.Vm.Gc
