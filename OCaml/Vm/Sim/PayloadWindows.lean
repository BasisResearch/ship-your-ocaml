import OCaml.Vm.Sim.ArmGeometry
import OCaml.Vm.Gc.NurseryGeometry

/-!
# Payload separation from a list of write windows

A native path (an arm, a runtime call) stores in several places at once:
below the live VM stack, into `Caml_state` fields the payload does not
observe, and into windows apart from the whole payload (the native stack).
`PayloadWindow` names these three kinds; a log inside such windows misses
the represented payload (`PayloadOutside.of_windows`), the primitive bindings
(`BindingsOutside.of_windows`) and the allocation pointers
(`YoungOutside.of_payloadWindows`). `WindowSeparated.of_above` gives the
third kind for any window above the allocator arena.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Gc

/-- The `Caml_state` fields a native path may store without touching the
payload: every VM-written field but `trapsp`. -/
def payloadFreeOffsets : List Nat :=
  [Layout.off_extern_sp, Layout.off_local_roots, Layout.off_exn_bucket, Layout.off_external_raise]

theorem payload_free_offsets : ∀ off ∈ payloadFreeOffsets,
    off + 8 ≤ Layout.domainStateBytes ∧
    (off + 8 ≤ Layout.off_stack_high ∨ Layout.off_stack_high + 8 ≤ off) ∧
    (off + 8 ≤ Layout.off_trapsp ∨ Layout.off_trapsp + 8 ≤ off) ∧
    ∀ o ∈ [Layout.off_young_limit, Layout.off_young_ptr], off + 8 ≤ o ∨ o + 8 ≤ off := by
  decide

/-- **A write window apart from the payload at `sp`**: apart from all of it,
inside the stack allocation below the live stack, or one payload-free
`Caml_state` field. -/
inductive PayloadWindow (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high : Nat) : W → Prop
  | separated {w : W} : WindowSeparated w P s c pl cp high → PayloadWindow P s c pl cp sp high w
  | belowStack {w : W} : high - Layout.stackBytes ≤ w.lo → w.hi ≤ sp → PayloadWindow P s c pl cp sp high w
  | field {off : Nat} : off ∈ payloadFreeOffsets →
      PayloadWindow P s c pl cp sp high
        ⟨(word c Layout.sym_Caml_state).toNat + off, (word c Layout.sym_Caml_state).toNat + off + 8⟩

/-- **The separation principle**: a range apart from every payload window,
given what each kind of window needs. -/
theorem PayloadWindow.apart {P s c pl cp sp high} {w : W} {a n : Nat}
    (pw : PayloadWindow P s c pl cp sp high w)
    (separated : WindowSeparated w P s c pl cp high → OutWRange [w] a n)
    (below : high - Layout.stackBytes ≤ w.lo → w.hi ≤ sp → a + n ≤ w.lo ∨ w.hi ≤ a)
    (field : ∀ off ∈ payloadFreeOffsets,
      a + n ≤ (word c Layout.sym_Caml_state).toNat + off ∨ (word c Layout.sym_Caml_state).toNat + off + 8 ≤ a) :
    OutWRange [w] a n := by
  cases pw with
  | separated h => exact separated h
  | belowStack lo hi => exact ⟨below lo hi, trivial⟩
  | field member => exact ⟨field _ member, trivial⟩

/-- A range apart from the `Caml_state` record misses each of its fields. -/
theorem domain_apart_field {c : Config} {a n : Nat}
    (h : OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
      (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] a n) :
    ∀ off ∈ payloadFreeOffsets,
      a + n ≤ (word c Layout.sym_Caml_state).toNat + off ∨ (word c Layout.sym_Caml_state).toNat + off + 8 ≤ a := by
  intro off member
  have := (payload_free_offsets off member).1
  obtain ⟨h, -⟩ := h
  dsimp only at h
  omega

/-- A range inside the `Caml_state` record misses each payload-free field
when it misses every one of them by offset. -/
theorem stack_apart_field {c : Config} {high a n : Nat}
    (g : OutWRange [stackWindow high] (word c Layout.sym_Caml_state).toNat Layout.domainStateBytes)
    (inStack : high - Layout.stackBytes ≤ a) (top : a + n ≤ high) :
    ∀ off ∈ payloadFreeOffsets,
      a + n ≤ (word c Layout.sym_Caml_state).toNat + off ∨ (word c Layout.sym_Caml_state).toNat + off + 8 ≤ a := by
  intro off member
  have := (payload_free_offsets off member).1
  obtain ⟨g, -⟩ := g
  simp only [stackWindow] at g
  omega

/-- **A log in payload windows misses the represented payload.** -/
theorem PayloadOutside.of_windows {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {ws : List W} {log : List WEntry} (g : StackGeometry P s c pl cp high)
    (stack : sp + 8 * s.stack.length = high) (low : high - Layout.stackBytes ≤ sp)
    (inside : LogInW ws log) (each : ∀ w ∈ ws, PayloadWindow P s c pl cp sp high w) :
    PayloadOutside log P s c pl cp sp := by
  have dl := g.domainLow
  have st := g.statics
  have gd := g.domain
  simp only [stackWindow, OutWRange, and_true] at gd
  have out : ∀ a n, (∀ w ∈ ws, OutWRange [w] a n) → OutLRange log a n :=
    fun a n each => outLRange_of_windows inside (outWRange_of_each each)
  have static : ∀ a, a + 8 ≤ Layout.sym_bss_end → OutLRange log a 8 := by
    intro a ha
    refine out a 8 fun w hw => (each w hw).apart (fun h => window_static h.statics ha)
      (fun lo _ => ?_) (fun off _ => Or.inl (by omega))
    simp only [Layout.stackBytes] at lo st ⊢; omega
  have domainField : ∀ off ∈ [Layout.off_stack_high, Layout.off_trapsp],
      OutLRange log ((word c Layout.sym_Caml_state).toNat + off) 8 := by
    intro off member
    have fits : off + 8 ≤ Layout.domainStateBytes := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide
    refine out _ 8 fun w hw => (each w hw).apart (fun h => outW_sub h.domain (by omega) (by omega))
      (fun lo hi => ?_) (fun o member' => ?_)
    · have := g.top; simp only [Layout.stackBytes] at gd lo hi fits ⊢; omega
    · obtain ⟨-, sh, tr, -⟩ := payload_free_offsets o member'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> omega
  have stackSlot : ∀ i, i < s.stack.length → OutLRange log (sp + 8 * i) 8 := by
    intro i bound
    refine out _ 8 fun w hw => (each w hw).apart
      (fun h => outW_sub h.stack (by omega) (by omega)) (fun _ hi => Or.inr (by omega))
      (stack_apart_field g.domain (by omega) (by omega))
  have object : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o → ∀ b k, a - 8 ≤ b →
      b + k ≤ a - 8 + (8 * o.wosize + 8) → OutLRange log b k := by
    intro l a o placed obj b k lo hi
    have gh := g.heap l a o placed obj
    have dh := g.domainHeap l a o placed obj
    refine out _ k fun w hw => (each w hw).apart (fun h => outW_sub (h.heap l a o placed obj) lo hi)
      (fun wl wh => ?_) (fun off member => ?_)
    · obtain ⟨gh, -⟩ := gh
      simp only [stackWindow] at gh wl
      omega
    · have := (payload_free_offsets off member).1
      obtain ⟨dh, -⟩ := dh
      dsimp only at dh
      omega
  refine ⟨static _ (by decide), domainField _ (by simp), domainField _ (by simp),
    static _ (by decide), static _ (by decide), static _ (by decide), ?_, ?_, ?_, ?_⟩
  · intro i v hv
    have bound : i < P.code.size := (Array.getElem?_eq_some_iff.1 hv).1
    have dc := g.domainCode
    have gc := g.code i v hv
    refine out _ 4 fun w hw => (each w hw).apart (fun h => h.code i v hv) (fun wl wh => ?_)
      (fun off member => ?_)
    · obtain ⟨gc, -⟩ := gc
      simp only [stackWindow] at gc wl
      omega
    · have := (payload_free_offsets off member).1
      obtain ⟨dc, -⟩ := dc
      dsimp only at dc
      omega
  · intro i v hv
    exact stackSlot i (List.getElem?_eq_some_iff.1 hv).1
  · intro l a o _ placed obj
    exact ⟨object l a o placed obj _ _ (Nat.le_refl _) (by omega),
      object l a o placed obj _ _ (by omega) (by omega)⟩
  · intro id ch a hch hcp
    have gc := g.channels id ch a hch hcp
    have dc := g.domainChannels id ch a hch hcp
    refine out _ _ fun w hw => (each w hw).apart (fun h => h.channels id ch a hch hcp)
      (fun wl wh => ?_) (fun off member => ?_)
    · obtain ⟨gc, -⟩ := gc
      simp only [stackWindow] at gc wl
      omega
    · have := (payload_free_offsets off member).1
      obtain ⟨dc, -⟩ := dc
      dsimp only at dc
      omega

/-- **A log in payload windows misses the primitive bindings.** -/
theorem BindingsOutside.of_windows {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {ws : List W} {log : List WEntry} (g : StackGeometry P s c pl cp high)
    (top : sp ≤ high)
    (inside : LogInW ws log) (each : ∀ w ∈ ws, PayloadWindow P s c pl cp sp high w) :
    BindingsOutside log P c := by
  have dl := g.domainLow
  have st := g.statics
  have out : ∀ a n, (∀ w ∈ ws, OutWRange [w] a n) → OutLRange log a n :=
    fun a n each => outLRange_of_windows inside (outWRange_of_each each)
  have contents : Layout.sym_caml_prim_table + Layout.off_prim_contents + 8 ≤ Layout.sym_bss_end := by decide
  refine ⟨out _ 8 fun w hw => (each w hw).apart (fun h => window_static h.statics contents)
    (fun lo _ => ?_) (fun off _ => Or.inl (by omega)), ?_⟩
  · simp only [Layout.stackBytes] at lo st ⊢; omega
  · intro i name hi
    have gp := g.primitives i name hi
    have dp := g.domainPrims i name hi
    refine out _ 8 fun w hw => (each w hw).apart (fun h => h.primitives i name hi)
      (fun wl wh => ?_) (fun off member => ?_)
    · obtain ⟨gp, -⟩ := gp
      simp only [stackWindow] at gp wl
      omega
    · have := (payload_free_offsets off member).1
      obtain ⟨dp, -⟩ := dp
      dsimp only at dp
      omega

/-- **A log in payload windows misses the allocation pointers.** -/
theorem YoungOutside.of_payloadWindows {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {ws : List W} {log : List WEntry} (g : StackGeometry P s c pl cp high)
    (top : sp ≤ high)
    (inside : LogInW ws log) (each : ∀ w ∈ ws, PayloadWindow P s c pl cp sp high w) :
    YoungOutside log c := by
  have gd := g.domain
  simp only [stackWindow, OutWRange, and_true] at gd
  have young : ∀ off ∈ [Layout.off_young_limit, Layout.off_young_ptr],
      OutLRange log ((word c Layout.sym_Caml_state).toNat + off) 8 := by
    intro off member
    have fits := (young_field_offsets off member).1
    refine outLRange_of_windows inside (outWRange_of_each fun w hw => (each w hw).apart
      (fun h => outW_sub h.domain (by omega) (by omega)) (fun lo hi => ?_) (fun o member' => ?_))
    · simp only [Layout.stackBytes] at gd lo hi fits ⊢; have := g.top; omega
    · have := (payload_free_offsets o member').2.2.2 off member
      omega
  exact ⟨young _ (by simp), young _ (by simp)⟩

/-! ## Windows above the allocator arena -/

/-- The channel records and the program's primitive-table slots lie in the
allocator arena (named premise; a1-arms adds both to `StackGeometry`). -/
structure ArenaBounds (P : Prog) (s : St) (c : Config) (cp : ChanPlace) : Prop where
  channelArena : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    a + (chanOffBuff + ch.buffer.length) ≤ Vsa.Sim.DlHeap.heapEnd
  primsArena : ∀ i name, P.prims[i]? = some name →
    (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i + 8 ≤
      Vsa.Sim.DlHeap.heapEnd

/-- **A window above the allocator arena misses the whole payload.** -/
theorem WindowSeparated.of_above {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} {w : W} (g : StackGeometry P s c pl cp high) (arena : ArenaBounds P s c cp)
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
  channels id ch a hch hcp := ⟨Or.inl (by have := arena.channelArena id ch a hch hcp; omega), trivial⟩
  primitives i name hi := ⟨Or.inl (by have := arena.primsArena i name hi; omega), trivial⟩

end OCaml.Vm.Sim
