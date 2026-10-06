import OCaml.Vm.Sim.ArmGeometry
import OCaml.Vm.Gc.NurseryGeometry
import OCaml.Vm.Sim.PayloadRestore

/-!
# Separation from a list of write windows

A native path (an arm, a runtime call, an allocation) stores in a few kinds
of places: inside the VM stack allocation below some bound `top`, into
chosen `Caml_state` fields (offsets `offs`), and into windows apart from the
whole payload (`WindowSeparated`: the free nursery, the native stack).
`LogWindow P s c pl cp top high offs` names the three kinds. A log inside
such windows misses a target range when the range is apart from each kind
(`LogWindow.apart`); `LogWindows` packages the geometry and the log once,
and derives the separation facts of the represented payload from it:
statics, code, objects, channels, primitive entries, `Caml_state` fields
outside `offs`, and stack slots above `top`.

Instances: `PayloadWindow` (`top = sp`, the payload-free fields; full
`PayloadOutside`), `VmWriteWindow` (`VmLogOk.of_windows`), `FreshWindow`
(`FreshLogOk.of_windows`). `WindowSeparated.of_above` gives the separated
kind for any window above the allocator arena.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Gc

/-- **A write window of a native path**: apart from the whole payload, inside
the stack allocation below `top`, or the `Caml_state` field at an offset in
`offs`. -/
inductive LogWindow (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (top high : Nat) (offs : List Nat) : W → Prop
  | separated {w : W} : WindowSeparated w P s c pl cp high → LogWindow P s c pl cp top high offs w
  | belowStack {w : W} : high - Layout.stackBytes ≤ w.lo → w.hi ≤ top →
      LogWindow P s c pl cp top high offs w
  | field {off : Nat} : off ∈ offs →
      LogWindow P s c pl cp top high offs
        ⟨(word c Layout.sym_Caml_state).toNat + off, (word c Layout.sym_Caml_state).toNat + off + 8⟩

/-- **The separation principle**: a range apart from each kind of window. -/
theorem LogWindow.apart {P s c pl cp top high offs} {w : W} {a n : Nat}
    (lw : LogWindow P s c pl cp top high offs w)
    (separated : WindowSeparated w P s c pl cp high → OutWRange [w] a n)
    (stack : a + n ≤ high - Layout.stackBytes ∨ top ≤ a)
    (field : ∀ off ∈ offs,
      a + n ≤ (word c Layout.sym_Caml_state).toNat + off ∨ (word c Layout.sym_Caml_state).toNat + off + 8 ≤ a) :
    OutWRange [w] a n := by
  cases lw with
  | separated h => exact separated h
  | belowStack lo hi => exact ⟨by omega, trivial⟩
  | field member => exact ⟨field _ member, trivial⟩

/-- A log, its windows and the stack geometry they are checked against. -/
structure LogWindows (log : List WEntry) (P : Prog) (s : St) (c : Config) (pl : Place)
    (cp : ChanPlace) (top high : Nat) (offs : List Nat) : Prop where
  geometry : StackGeometry P s c pl cp high
  inside : ∃ ws, LogInW ws log ∧ ∀ w ∈ ws, LogWindow P s c pl cp top high offs w
  /-- the store bound lies in the allocation -/
  top : top ≤ high
  /-- the chosen fields lie in the record -/
  fits : ∀ off ∈ offs, off + 8 ≤ Layout.domainStateBytes

namespace LogWindows

variable {log : List WEntry} {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
  {top high : Nat} {offs : List Nat}

theorem out (h : LogWindows log P s c pl cp top high offs) {a n : Nat}
    (separated : ∀ w, WindowSeparated w P s c pl cp high → OutWRange [w] a n)
    (stack : a + n ≤ high - Layout.stackBytes ∨ top ≤ a)
    (field : ∀ off ∈ offs,
      a + n ≤ (word c Layout.sym_Caml_state).toNat + off ∨ (word c Layout.sym_Caml_state).toNat + off + 8 ≤ a) :
    OutLRange log a n := by
  obtain ⟨ws, inside, each⟩ := h.inside
  exact outLRange_of_windows inside (outWRange_of_each fun w hw =>
    (each w hw).apart (separated w) stack field)

/-- A range apart from the whole `Caml_state` record misses each chosen field. -/
theorem field_of_record (h : LogWindows log P s c pl cp top high offs) {a n : Nat}
    (record : OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
      (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] a n) :
    ∀ off ∈ offs,
      a + n ≤ (word c Layout.sym_Caml_state).toNat + off ∨ (word c Layout.sym_Caml_state).toNat + off + 8 ≤ a := by
  intro off member
  have := h.fits off member
  obtain ⟨record, -⟩ := record
  dsimp only at record
  omega

/-- A range apart from the stack allocation is apart from the stored part. -/
theorem stack_of_window (h : LogWindows log P s c pl cp top high offs) {a n : Nat}
    (apart : OutWRange [stackWindow high] a n) : a + n ≤ high - Layout.stackBytes ∨ top ≤ a := by
  have := h.top
  obtain ⟨apart, -⟩ := apart
  simp only [stackWindow] at apart
  omega

theorem static (h : LogWindows log P s c pl cp top high offs) {a n : Nat}
    (below : a + n ≤ Layout.sym_bss_end) : OutLRange log a n := by
  have st := h.geometry.statics
  have dl := h.geometry.domainLow
  exact h.out (fun w sep => window_static sep.statics below)
    (.inl (by simp only [Layout.stackBytes] at st ⊢; omega)) (fun off _ => .inl (by omega))

/-- A `Caml_state` field away from every chosen offset. -/
theorem domainField (h : LogWindows log P s c pl cp top high offs) {off : Nat}
    (fits : off + 8 ≤ Layout.domainStateBytes)
    (apart : ∀ o ∈ offs, off + 8 ≤ o ∨ o + 8 ≤ off) :
    OutLRange log ((word c Layout.sym_Caml_state).toNat + off) 8 := by
  have gd := h.geometry.domain
  have ht := h.top
  simp only [stackWindow, OutWRange, and_true] at gd
  exact h.out (fun w sep => outW_sub sep.domain (by omega) (by omega))
    (by simp only [Layout.stackBytes] at gd fits ⊢; omega)
    (fun o member => by have := apart o member; omega)

theorem code (h : LogWindows log P s c pl cp top high offs) {i : Nat} {v : BitVec 32}
    (hv : P.code[i]? = some v) : OutLRange log (pl.codeBase + 4 * i) 4 := by
  have bound : i < P.code.size := (Array.getElem?_eq_some_iff.1 hv).1
  have dc := h.geometry.domainCode
  refine h.out (fun w sep => sep.code i v hv) (h.stack_of_window (h.geometry.code i v hv))
    (h.field_of_record ⟨?_, trivial⟩)
  obtain ⟨dc, -⟩ := dc
  dsimp only at dc ⊢
  omega

theorem object (h : LogWindows log P s c pl cp top high offs) {l a : Nat} {o : Obj}
    (placed : pl.φ l = some a) (got : s.heap.get? l = some o) {b k : Nat}
    (lo : a - 8 ≤ b) (hi : b + k ≤ a - 8 + (8 * o.wosize + 8)) : OutLRange log b k :=
  h.out (fun w sep => outW_sub (sep.heap l a o placed got) lo hi)
    (h.stack_of_window (outW_sub (h.geometry.heap l a o placed got) lo hi))
    (h.field_of_record (outW_sub (h.geometry.domainHeap l a o placed got) lo hi))

theorem objectOutside (h : LogWindows log P s c pl cp top high offs) {l a : Nat} {o : Obj}
    (placed : pl.φ l = some a) (got : s.heap.get? l = some o) : ObjectOutside log a o :=
  ⟨h.object placed got (Nat.le_refl _) (by omega), h.object placed got (by omega) (by omega)⟩

theorem channel (h : LogWindows log P s c pl cp top high offs) {id : Nat} {ch : Chan} {a : Nat}
    (hch : s.world.chans[id]? = some ch) (hcp : cp id = some a) :
    OutLRange log a (chanOffBuff + ioBufferSize) :=
  h.out (fun w sep => sep.channels id ch a hch hcp) (h.stack_of_window (h.geometry.channels id ch a hch hcp))
    (h.field_of_record (h.geometry.domainChannels id ch a hch hcp))

theorem bindings (h : LogWindows log P s c pl cp top high offs) : BindingsOutside log P c :=
  ⟨h.static (by decide), fun i name hi =>
    h.out (fun w sep => sep.primitives i name hi) (h.stack_of_window (h.geometry.primitives i name hi))
      (h.field_of_record (h.geometry.domainPrims i name hi))⟩

theorem image (h : LogWindows log P s c pl cp top high offs) : ImageOutside log :=
  ⟨h.static (by decide), h.static (by decide)⟩

/-- A stack slot at or above the store bound. -/
theorem stackSlot (h : LogWindows log P s c pl cp top high offs) {a : Nat}
    (above : top ≤ a) (inStack : high - Layout.stackBytes ≤ a) (below : a + 8 ≤ high) :
    OutLRange log a 8 := by
  have gd := h.geometry.domain
  refine h.out (fun w sep => outW_sub sep.stack inStack (by omega)) (.inr above) fun off member => ?_
  have := h.fits off member
  obtain ⟨gd, -⟩ := gd
  simp only [stackWindow] at gd
  omega

/-- The payload core: away from `stack_high`. -/
theorem core (h : LogWindows log P s c pl cp top high offs)
    (stackHigh : ∀ o ∈ offs, Layout.off_stack_high + 8 ≤ o ∨ o + 8 ≤ Layout.off_stack_high) :
    PayloadCoreOutside log P s c pl cp :=
  ⟨h.static (by decide), h.domainField (by decide) stackHigh, h.static (by decide),
    h.static (by decide), h.static (by decide), fun _ _ hv => h.code hv,
    fun _ _ _ hch hcp => h.channel hch hcp, h.static (by decide), h.static (by decide)⟩

/-- The allocation pointers: away from both. -/
theorem young (h : LogWindows log P s c pl cp top high offs)
    (apart : ∀ off ∈ [Layout.off_young_limit, Layout.off_young_ptr, Layout.off_external_raise], ∀ o ∈ offs,
      off + 8 ≤ o ∨ o + 8 ≤ off) :
    YoungOutside log c :=
  ⟨h.domainField (by decide) (apart _ (by simp)), h.domainField (by decide) (apart _ (by simp)),
    h.domainField (by decide) (apart _ (by simp))⟩

/-- **The full payload**, for a store bound at or below `sp`. -/
theorem payload (h : LogWindows log P s c pl cp top high offs) {sp : Nat}
    (stack : sp + 8 * s.stack.length = high) (low : high - Layout.stackBytes ≤ sp) (bound : top ≤ sp)
    (stackHigh : ∀ o ∈ offs, Layout.off_stack_high + 8 ≤ o ∨ o + 8 ≤ Layout.off_stack_high)
    (trapsp : ∀ o ∈ offs, Layout.off_trapsp + 8 ≤ o ∨ o + 8 ≤ Layout.off_trapsp) :
    PayloadOutside log P s c pl cp sp :=
  ⟨h.static (by decide), h.domainField (by decide) stackHigh, h.domainField (by decide) trapsp,
    h.static (by decide), h.static (by decide), h.static (by decide), fun _ _ hv => h.code hv,
    fun i _ hv => by
      have := (List.getElem?_eq_some_iff.1 hv).1
      exact h.stackSlot (by omega) (by omega) (by omega),
    fun _ _ _ _ placed got => h.objectOutside placed got, fun _ _ _ hch hcp => h.channel hch hcp,
    h.static (by decide), h.static (by decide)⟩

end LogWindows

/-! ## The payload-free instance -/

/-- The `Caml_state` fields a native path may store without touching the
payload: every VM-written field but `trapsp`. -/
def payloadFreeOffsets : List Nat :=
  [Layout.off_extern_sp, Layout.off_local_roots, Layout.off_exn_bucket]

/-- A write window apart from the payload at `sp`. -/
abbrev PayloadWindow (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace) (sp high : Nat) :=
  LogWindow P s c pl cp sp high payloadFreeOffsets

/-- **A log in payload windows misses the represented payload.** -/
theorem PayloadOutside.of_windows {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {ws : List W} {log : List WEntry} (g : StackGeometry P s c pl cp high)
    (stack : sp + 8 * s.stack.length = high) (low : high - Layout.stackBytes ≤ sp)
    (inside : LogInW ws log) (each : ∀ w ∈ ws, PayloadWindow P s c pl cp sp high w) :
    PayloadOutside log P s c pl cp sp :=
  LogWindows.payload ⟨g, ⟨ws, inside, each⟩, by omega, by decide⟩ stack low (Nat.le_refl _)
    (by decide) (by decide)

/-- **A log in payload windows misses the primitive bindings.** -/
theorem BindingsOutside.of_windows {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {ws : List W} {log : List WEntry} (g : StackGeometry P s c pl cp high)
    (top : sp ≤ high) (inside : LogInW ws log) (each : ∀ w ∈ ws, PayloadWindow P s c pl cp sp high w) :
    BindingsOutside log P c :=
  LogWindows.bindings ⟨g, ⟨ws, inside, each⟩, top, by decide⟩

/-- **A log in payload windows misses the allocation pointers.** -/
theorem YoungOutside.of_payloadWindows {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {ws : List W} {log : List WEntry} (g : StackGeometry P s c pl cp high)
    (top : sp ≤ high) (inside : LogInW ws log) (each : ∀ w ∈ ws, PayloadWindow P s c pl cp sp high w) :
    YoungOutside log c :=
  LogWindows.young ⟨g, ⟨ws, inside, each⟩, top, by decide⟩ (by decide)

/-! ## Separated windows -/

/-- **A window above the allocator arena misses the whole payload.** -/
theorem _root_.OCaml.Vm.Gc.WindowSeparated.of_above {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} {w : W} (g : StackGeometry P s c pl cp high)
    (above : Vsa.Sim.DlHeap.heapEnd ≤ w.lo) : WindowSeparated w P s c pl cp high where
  statics := by
    have : Layout.sym_bss_end ≤ Vsa.Sim.DlHeap.heapEnd := by decide
    omega
  domain := ⟨Or.inl (by have := g.domainArena; omega), trivial⟩
  stack := ⟨Or.inl (by
    have := g.arena; have := g.statics
    simp only [Layout.stackBytes, Layout.sym_bss_end] at *; omega), trivial⟩
  code i v hv := by
    have bound : i < P.code.size := (Array.getElem?_eq_some_iff.1 hv).1
    exact ⟨Or.inl (by have := g.codeArena; omega), trivial⟩
  heap l a o placed obj := by
    have := g.heapArena l a o placed obj
    have := g.heapLow l a o placed obj
    exact ⟨Or.inl (by omega), trivial⟩
  channels id ch a hch hcp := ⟨Or.inl (by have := g.channelArena id ch a hch hcp; omega), trivial⟩
  primitives i name hi := ⟨Or.inl (by have := g.primsArena i name hi; omega), trivial⟩

/-- A subwindow of a separated window is separated. -/
theorem _root_.OCaml.Vm.Gc.WindowSeparated.sub {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} {w v : W} (h : WindowSeparated w P s c pl cp high) (lo : w.lo ≤ v.lo) (hi : v.hi ≤ w.hi) :
    WindowSeparated v P s c pl cp high := by
  have sub : ∀ {a n}, OutWRange [w] a n → OutWRange [v] a n := fun h => by
    obtain ⟨h, -⟩ := h
    exact ⟨by omega, trivial⟩
  exact { statics := by have := h.statics; omega
          domain := sub h.domain
          stack := sub h.stack
          code := fun i x hx => sub (h.code i x hx)
          heap := fun l a o placed got => sub (h.heap l a o placed got)
          channels := fun id ch a hch hcp => sub (h.channels id ch a hch hcp)
          primitives := fun i name hi => sub (h.primitives i name hi) }

end OCaml.Vm.Sim
