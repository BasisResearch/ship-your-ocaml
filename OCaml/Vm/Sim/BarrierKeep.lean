import OCaml.Vm.Sim.BarrierF1

/-!
# The represented barrier state across a frame

`BarrierState.separated_step` and `field_step` carry the represented state
across a write log. A call whose memory effect is a frame (malloc, realloc:
"every byte outside the allocator's blocks is kept") needs the frame form:
`BarrierObserved` is everything the represented state reads, and
`keep_frame` carries the state across any change that keeps those bytes.
`keep_field_step` is the growth path's shape: one frame over the whole call,
the slot word excepted, and the slot holding the stored value.
-/

set_option autoImplicit false

namespace OCaml.Vm.Sim

open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- The bytes `[a, a + n)`. -/
def InSpan (a n x : Nat) : Prop := a ≤ x ∧ x < a + n

/-- The static words the represented state reads. -/
def barrierStatics : List Nat :=
  [Layout.sym_Caml_state, Layout.sym_caml_start_code, Layout.sym_caml_atom_table,
   Layout.sym_caml_global_data, Layout.sym_oo_last_id, Layout.sym_caml_all_opened_channels,
   Layout.sym_caml_prim_table + Layout.off_prim_contents]

/-- **Every byte the represented barrier state reads** at `c`: the static
words, the domain record, the code, the VM stack, every placed heap object
(header and fields), the channel records, the primitive-table entries and
the native invocation's saved ranges. -/
inductive BarrierObserved (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace) (sp : Nat)
    (D : InvocationData) : Nat → Prop where
  | static {a x : Nat} : a ∈ barrierStatics → InSpan a 8 x → BarrierObserved P s c pl cp sp D x
  | domain {x : Nat} : InSpan (word c Layout.sym_Caml_state).toNat Layout.domainStateBytes x →
      BarrierObserved P s c pl cp sp D x
  | code {i : Nat} {w : BitVec 32} {x : Nat} : P.code[i]? = some w → InSpan (pl.codeBase + 4 * i) 4 x →
      BarrierObserved P s c pl cp sp D x
  | stack {i : Nat} {v : Val} {x : Nat} : s.stack[i]? = some v → InSpan (sp + 8 * i) 8 x →
      BarrierObserved P s c pl cp sp D x
  | header {l a : Nat} {o : Obj} {x : Nat} : s.heap.get? l = some o → pl.φ l = some a →
      InSpan (a - 8) 8 x → BarrierObserved P s c pl cp sp D x
  | fields {l a : Nat} {o : Obj} {x : Nat} : s.heap.get? l = some o → pl.φ l = some a →
      InSpan a (8 * o.wosize) x → BarrierObserved P s c pl cp sp D x
  | channel {id : Nat} {ch : Chan} {a x : Nat} : s.world.chans[id]? = some ch → cp id = some a →
      InSpan a (chanOffBuff + ioBufferSize) x → BarrierObserved P s c pl cp sp D x
  | prim {i : Nat} {name : String} {x : Nat} : P.prims[i]? = some name →
      InSpan ((word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i) 8 x →
      BarrierObserved P s c pl cp sp D x
  | native {r : Nat × Nat} {x : Nat} : r ∈ invocationRanges → InSpan (D.nativeSp + r.1) r.2 x →
      BarrierObserved P s c pl cp sp D x

section Keep

variable {P : Prog} {s : St} {c c' : Config} {pl : Place} {cp : ChanPlace} {sp : Nat} {D : InvocationData}

/-- A kept span is copied. -/
theorem kept_copied (keep : ∀ x, BarrierObserved P s c pl cp sp D x → byte c' x = byte c x)
    {a n : Nat} (obs : ∀ x, InSpan a n x → BarrierObserved P s c pl cp sp D x) :
    Reloc.Copied c c' a a n :=
  fun j hj => keep _ (obs _ ⟨Nat.le_add_right _ _, by omega⟩)

/-- A kept word reads the same. -/
theorem kept_word (keep : ∀ x, BarrierObserved P s c pl cp sp D x → byte c' x = byte c x)
    {a : Nat} (obs : ∀ x, InSpan a 8 x → BarrierObserved P s c pl cp sp D x) : word c' a = word c a :=
  Reloc.bytesT_congr (kept_copied keep obs)

theorem kept_static (keep : ∀ x, BarrierObserved P s c pl cp sp D x → byte c' x = byte c x)
    {a : Nat} (mem : a ∈ barrierStatics) : word c' a = word c a :=
  kept_word keep fun _ hx => .static mem hx

/-- A `Caml_state` field (offset `off`, 8 bytes inside the record) reads the same. -/
theorem kept_domainField (keep : ∀ x, BarrierObserved P s c pl cp sp D x → byte c' x = byte c x)
    {off : Nat} (fits : off + 8 ≤ Layout.domainStateBytes) :
    word c' ((word c' Layout.sym_Caml_state).toNat + off) = word c ((word c Layout.sym_Caml_state).toNat + off) := by
  have dom : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state :=
    kept_static keep (a := Layout.sym_Caml_state) (List.mem_cons_self ..)
  rw [dom]
  exact kept_word keep fun _ hx => .domain ⟨by have := hx.1; omega, by have := hx.2; omega⟩

/-- The VM payload across kept bytes. -/
theorem VmPayload.keep {high : Nat} (h : VmPayload P s c pl cp sp high)
    (keep : ∀ x, BarrierObserved P s c pl cp sp D x → byte c' x = byte c x)
    (outputEq : output c'.σ = output c.σ) : VmPayload P s c' pl cp sp high := by
  have st := fun {a : Nat} (mem : a ∈ barrierStatics) => kept_static keep mem
  constructor
  · rw [kept_domainField keep (by decide)]; exact h.stackHigh
  · rw [kept_domainField keep (by decide)]; exact h.trapsp
  · rw [st (by simp [barrierStatics])]; exact h.codeBase
  · intro i w hi
    have he : word32 c' (pl.codeBase + 4 * i) = word32 c (pl.codeBase + 4 * i) :=
      Reloc.bytesT_congr (kept_copied keep fun _ hx => .code hi hx)
    simpa only [he] using h.code i w hi
  · rw [st (by simp [barrierStatics])]; exact h.globals
  · refine ⟨h.stack.1, ?_⟩
    intro i v hi
    rw [kept_word keep fun _ hx => .stack hi hx]
    exact h.stack.2 i v hi
  · constructor
    · intro l hl
      obtain ⟨a, o, ha, ho, layout⟩ := h.heap.1 l hl
      exact ⟨a, o, ha, ho, object_copied layout (kept_copied keep fun _ hx => .header ho ha hx)
        (kept_copied keep fun _ hx => .fields ho ha hx)⟩
    · exact h.heap.2
  · refine ⟨?_, ?_, ?_⟩
    · rw [outputEq]; exact h.world.output
    · intro id ch hc
      obtain ⟨a, ha, layout⟩ := h.world.chans id ch hc
      exact ⟨a, ha, channel_copied_full layout (kept_copied keep fun _ hx => .channel hc ha hx)⟩
    · rw [st (by simp [barrierStatics])]; exact h.world.ooId
  · rw [st (by simp [barrierStatics])]; exact h.atomBase

/-- The primitive bindings across kept bytes. -/
theorem bindings_keep (h : PrimitiveBindings P c)
    (keep : ∀ x, BarrierObserved P s c pl cp sp D x → byte c' x = byte c x) : PrimitiveBindings P c' := by
  have contents := kept_static keep (a := Layout.sym_caml_prim_table + Layout.off_prim_contents)
    (by simp [barrierStatics])
  constructor
  intro i name hi
  obtain ⟨entry, he, target⟩ := h.targets i name hi
  refine ⟨entry, he, ?_⟩
  unfold primitiveTarget
  rw [contents]
  exact (kept_word keep fun _ hx => .prim hi hx).trans target

/-- The native invocation across kept bytes. -/
theorem Invocation.keep (h : Invocation D c)
    (keep : ∀ x, BarrierObserved P s c pl cp sp D x → byte c' x = byte c x) (stack : gpr c' 2 = gpr c 2) :
    Invocation D c' where
  stack := stack.trans h.stack
  domain := (kept_static keep (a := Layout.sym_Caml_state) (List.mem_cons_self ..)).trans h.domain
  region r hr i hi := by
    rw [← h.region r hr i hi]
    exact keep _ (.native hr ⟨Nat.le_add_right _ _, by omega⟩)
  externalRaise := by
    rw [← h.externalRaise, ← h.domain]
    have e := kept_domainField keep (off := Layout.off_external_raise) (by decide)
    rw [kept_static keep (a := Layout.sym_Caml_state) (List.mem_cons_self ..)] at e
    exact e

/-- The loop geometry across kept bytes (same heap and world). -/
theorem LoopGeometry.keep {L : OCaml.Layout} {high : Nat} (g : OCaml.LoopGeometry L P s c pl cp high)
    (keep : ∀ x, BarrierObserved P s c pl cp sp D x → byte c' x = byte c x) :
    OCaml.LoopGeometry L P s c' pl cp high := by
  have dom := kept_static keep (a := Layout.sym_Caml_state) (List.mem_cons_self ..)
  have limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit := by
    simp only [runtimeFields, domainWord]; rw [kept_domainField keep (by decide)]
  have ptr : (runtimeFields c').youngPtr = (runtimeFields c).youngPtr := by
    simp only [runtimeFields, domainWord]; rw [kept_domainField keep (by decide)]
  refine ⟨g.toArmGeometry.transport (fun l o' h => ⟨o', h, rfl⟩) rfl dom
    (kept_static keep (by simp [barrierStatics])) limit ptr (kept_static keep (by simp [barrierStatics]))
    (fun id ch a hc ha => kept_word keep fun _ hx =>
      .channel hc ha ⟨by have := hx.1; omega, by have := hx.2; simp only [Gc.chanOffNext, chanOffBuff] at *; omega⟩), ?_⟩
  constructor
  rw [limit, ptr]
  exact g.room.nursery

end Keep

/-! ## The represented state across a frame -/

/-- **A frame keeps the represented state**: every byte it reads is kept,
the image and the runtime hold afterwards, and the output and `sp` are kept. -/
theorem BarrierState.keep_step {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {D : InvocationData} {c c' : Config} (h : BarrierState L P s pl cp sp high D c)
    (keep : ∀ x, BarrierObserved P s c pl cp sp D x → byte c' x = byte c x)
    (image : ExecutableImage c') (runtime : L.runtimeOk c') (output : output c'.σ = output c.σ)
    (stack : gpr c' 2 = gpr c 2) : BarrierState L P s pl cp sp high D c' where
  data := VmPayload.keep h.data keep output
  primitives := bindings_keep h.primitives keep
  image := image
  runtime := runtime
  geometry := LoopGeometry.keep h.geometry keep
  invocation := h.invocation.keep keep stack
  low := h.low

/-- What the written state observes, away from the slot, the state before
observed. -/
theorem observed_of_written {P : Prog} {s : St} {c cm : Config} {pl : Place} {cp : ChanPlace}
    {sp : Nat} {D : InvocationData} {l i tag : Nat} {fields : List Val} {value : Val}
    (selected : s.heap.get? l = some (.block tag fields))
    (domain : word cm Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (contents : word cm (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents))
    {x : Nat} (obs : BarrierObserved P {s with heap := s.heap.set l (.block tag (fields.set i value))} cm pl cp sp D x) :
    BarrierObserved P s c pl cp sp D x := by
  have objects : ∀ q o', (s.heap.set l (.block tag (fields.set i value))).get? q = some o' →
      ∃ o, s.heap.get? q = some o ∧ o.wosize = o'.wosize := by
    intro q o' found
    by_cases equal : q = l
    · subst q
      rw [heap_set_here _ selected] at found
      cases found
      exact ⟨_, selected, by simp only [Obj.wosize, List.length_set]⟩
    · rw [heap_set_other _ _ _ _ (Ne.symm equal)] at found
      exact ⟨o', found, rfl⟩
  cases obs with
  | static mem hx => exact .static mem hx
  | domain hx => rw [domain] at hx; exact .domain hx
  | code hi hx => exact .code hi hx
  | stack hi hx => exact .stack hi hx
  | header ho ha hx =>
    obtain ⟨o, found, _⟩ := objects _ _ ho
    exact .header found ha hx
  | fields ho ha hx =>
    obtain ⟨o, found, size⟩ := objects _ _ ho
    rw [← size] at hx
    exact .fields found ha hx
  | channel hc ha hx => exact .channel hc ha hx
  | prim hi hx => rw [contents] at hx; exact .prim hi hx
  | native hr hx => exact .native hr hx

/-- **The growth path's shape**: one frame over a whole call that stores the
field. Every observed byte except the slot is kept, the slot word holds the
stored value; the state after is the written state. -/
theorem BarrierState.keep_field_step {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {D : InvocationData} {c c' : Config} {l a i tag : Nat} {fields : List Val}
    {value : Val} {w : BitVec 64}
    (h : BarrierState L P s pl cp sp high D c) (v : NativeValid D)
    (live : Live s.heap (roots P s) l) (placed : pl.φ l = some a)
    (selected : s.heap.get? l = some (.block tag fields)) (bound : i < fields.length)
    (represented : valWord pl value = some w)
    (root : ∀ loc, value.loc? = some loc → Live s.heap (roots P s) loc)
    (stable : WindowStable L.runtimeOk [⟨a + 8 * i, a + 8 * i + 8⟩])
    (keep : ∀ x, BarrierObserved P s c pl cp sp D x → ¬ InSpan (a + 8 * i) 8 x → byte c' x = byte c x)
    (slot : word c' (a + 8 * i) = w)
    (image : ExecutableImage c') (runtime : L.runtimeOk c') (output : output c'.σ = output c.σ)
    (stack : gpr c' 2 = gpr c 2) :
    BarrierState L P {s with heap := s.heap.set l (.block tag (fields.set i value))} pl cp sp high D c' := by
  let cm : Config := {c with σ := {c.σ with mem := writeLog c.σ.mem (fieldLog a i w)}}
  have mem : cm.σ.mem = writeLog c.σ.mem (fieldLog a i w) := rfl
  have hm := h.field_step v live placed selected bound represented root stable mem rfl rfl
  have hs := h.data.stack.1
  have space : 8 * s.stack.length ≤ Layout.stackBytes := by have := h.low; omega
  have ok := FieldWriteOk.of_geometry (w := w) h.geometry.toArmGeometry h.data.stack space placed selected bound
  have domain : word cm Layout.sym_Caml_state = word c Layout.sym_Caml_state := by
    rw [word, mem]; exact bytesT_writeLog_out _ ok.payload.domain
  have contents : word cm (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents) := by
    rw [word, mem]; exact bytesT_writeLog_out _ ok.bindings.contents
  have stored : word cm (a + 8 * i) = w := word_after_writeLog_at mem 0 _ _ rfl trivial
  refine hm.keep_step (fun x obs => ?_) image runtime output stack
  by_cases inSlot : InSpan (a + 8 * i) 8 x
  · obtain ⟨lo, hi⟩ := inSlot
    have e := Gc.byte_of_bytesT (slot.trans stored.symm) (i := x - (a + 8 * i)) (by omega)
    rw [Nat.add_sub_cancel' lo] at e
    rw [byte_total, byte_total]; exact e
  · rw [keep x (observed_of_written selected domain contents obs) inSlot]
    have out : OutL (fieldLog a i w) x := by
      simp only [fieldLog, OutL, and_true]
      simp only [InSpan, not_and, Nat.not_lt] at inSlot
      omega
    rw [byte_total, byte_total, mem, writeLog_out _ _ _ out]

end OCaml.Vm.Sim
