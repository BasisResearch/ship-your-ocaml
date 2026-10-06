import OCaml.Vm.Primitives.MemoryFrame

/-! The payload frame of a channel primitive: the footprint may write one
channel record (its `curr`/`offset` words and buffer), which then represents
the channel's new state; everything else is transported as in
`VmPayload.frame_obs`. -/
namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- `PayloadOutside` except for the record of channel `id`. -/
structure PayloadChanOutside (log : List WEntry) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (sp id : Nat) : Prop where
  domain : OutLRange log Layout.sym_Caml_state 8
  stackHigh : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) 8
  trapsp : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) 8
  codeBase : OutLRange log Layout.sym_caml_start_code 8
  atomBase : OutLRange log Layout.sym_caml_atom_table 8
  globals : OutLRange log Layout.sym_caml_global_data 8
  code : ∀ i w, P.code[i]? = some w → OutLRange log (pl.codeBase + 4 * i) 4
  stack : ∀ i v, s.stack[i]? = some v → OutLRange log (sp + 8 * i) 8
  heap : ∀ l a o, Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some o →
    ObjectOutside log a o
  /-- every other channel record -/
  others : ∀ id' ch a, id' ≠ id → s.world.chans[id']? = some ch → cp id' = some a →
    OutLRange log a (chanOffBuff + ioBufferSize)
  ooId : OutLRange log Layout.sym_oo_last_id 8

/-- **Transport the VM payload across a channel primitive's footprint**: the
world changes only channel `id` (now `ch'`, represented at its record) and
the console; roots and the object-ID counter are kept. -/
theorem VmPayload.frame_chan {P : Prog} {s : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {sp high id a : Nat} {log : List WEntry} {ch' : Chan} {w' : World}
    (h : VmPayload P s c pl cp sp high) (outside : PayloadChanOutside log P s c pl cp sp id)
    (memory : ∀ x, OutL log x → byte c' x = byte c x)
    (chans : w'.chans = s.world.chans.set id ch')
    (counter : w'.ooId = s.world.ooId)
    (rootsEq : roots P {s with world := w'} = roots P s)
    (place : cp id = some a) (repr : ChanAt c' a ch')
    (console : output c'.σ = bytesToString w'.console) :
    VmPayload P {s with world := w'} c' pl cp sp high := by
  have copy := fun a n (ho : OutLRange log a n) => copied_of_outsideLog memory ho
  have hw : ∀ a, OutLRange log a 8 → word c' a = word c a :=
    fun a ho => Reloc.bytesT_congr (copy a 8 ho)
  have domain := hw Layout.sym_Caml_state outside.domain
  constructor
  · rw [domain, hw _ outside.stackHigh]
    exact h.stackHigh
  · rw [domain, hw _ outside.trapsp]
    exact h.trapsp
  · rw [hw _ outside.codeBase]
    exact h.codeBase
  · intro i w hi
    have he : word32 c' (pl.codeBase + 4 * i) = word32 c (pl.codeBase + 4 * i) :=
      Reloc.bytesT_congr (copy _ 4 (outside.code i w hi))
    simpa only [he] using h.code i w hi
  · rw [hw _ outside.globals]
    exact h.globals
  · refine ⟨h.stack.1, ?_⟩
    intro i v hi
    rw [hw _ (outside.stack i v hi)]
    exact h.stack.2 i v hi
  · have moved : HeapRepr c' pl cp P s := by
      constructor
      · intro l hl
        obtain ⟨a, o, ha, ho, layout⟩ := h.heap.1 l hl
        have iso := outside.heap l a o hl ha ho
        exact ⟨a, o, ha, ho, object_copied layout (copy _ 8 iso.header) (copy _ _ iso.payload)⟩
      · exact h.heap.2
    unfold HeapRepr at moved ⊢
    rw [rootsEq]
    exact moved
  · refine ⟨console, ?_, ?_⟩
    · intro id' ch hc
      rw [chans, List.getElem?_set] at hc
      by_cases same : id = id'
      · subst same
        have hl : id < s.world.chans.length := by
          rcases Nat.lt_or_ge id s.world.chans.length with hl | hn
          · exact hl
          · simp [Nat.not_lt.mpr hn] at hc
        simp only [↓reduceIte, hl, Option.some.injEq] at hc
        subst hc
        exact ⟨a, place, repr⟩
      · simp only [same, ↓reduceIte] at hc
        obtain ⟨b, hb, layout⟩ := h.world.chans id' ch hc
        exact ⟨b, hb, channel_copied_full layout (copy _ _ (outside.others id' ch b (Ne.symm same) hc hb))⟩
    · rw [hw _ outside.ooId, counter]
      exact h.world.ooId
  · rw [hw _ outside.atomBase]
    exact h.atomBase

end OCaml.Vm.Primitives
