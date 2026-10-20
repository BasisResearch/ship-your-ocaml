import OCaml.Vm.Primitives.Channel.OpenRepr

/-!
# The bytes the VM payload reads

`PayloadObserved` is every byte `VmPayload` reads: its static words, two
`Caml_state` fields, the code, the VM stack, every placed object, and each
channel record outside its link words (`next`, `prev` at 48–63, which
`ChanAt` does not read and an opening rewrites in the old head).
`VmPayload.keep_observed` carries the payload across any change that keeps
those bytes (the barrier's `VmPayload.keep` is its instance).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The bytes `[a, a + n)`. -/
def InSpan (a n x : Nat) : Prop := a ≤ x ∧ x < a + n

/-- The static words `VmPayload` reads. -/
def payloadStatics : List Nat :=
  [Layout.sym_Caml_state, Layout.sym_caml_start_code, Layout.sym_caml_atom_table,
   Layout.sym_caml_global_data, Layout.sym_oo_last_id, Layout.sym_main_argv]

/-- **Every byte `VmPayload` reads** at `c`. -/
inductive PayloadObserved (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace) (sp : Nat) :
    Nat → Prop where
  | static {a x : Nat} : a ∈ payloadStatics → InSpan a 8 x → PayloadObserved P s c pl cp sp x
  | domainField {off x : Nat} : off ∈ [Layout.off_stack_high, Layout.off_trapsp] →
      InSpan ((word c Layout.sym_Caml_state).toNat + off) 8 x → PayloadObserved P s c pl cp sp x
  | code {i : Nat} {w : BitVec 32} {x : Nat} : P.code[i]? = some w → InSpan (pl.codeBase + 4 * i) 4 x →
      PayloadObserved P s c pl cp sp x
  | stack {i : Nat} {v : Val} {x : Nat} : s.stack[i]? = some v → InSpan (sp + 8 * i) 8 x →
      PayloadObserved P s c pl cp sp x
  | header {l a : Nat} {o : Obj} {x : Nat} : s.heap.get? l = some o → pl.φ l = some a →
      InSpan (a - 8) 8 x → PayloadObserved P s c pl cp sp x
  | fields {l a : Nat} {o : Obj} {x : Nat} : s.heap.get? l = some o → pl.φ l = some a →
      InSpan a (8 * o.wosize) x → PayloadObserved P s c pl cp sp x
  | chanFront {id : Nat} {ch : Chan} {a x : Nat} : s.world.chans[id]? = some ch → cp id = some a →
      InSpan a 48 x → PayloadObserved P s c pl cp sp x
  | chanBack {id : Nat} {ch : Chan} {a x : Nat} : s.world.chans[id]? = some ch → cp id = some a →
      InSpan (a + 64) (chanOffBuff + ioBufferSize - 64) x → PayloadObserved P s c pl cp sp x

section Keep

variable {P : Prog} {s : St} {c c' : Config} {pl : Place} {cp : ChanPlace} {sp : Nat}

theorem observed_copied (keep : ∀ x, PayloadObserved P s c pl cp sp x → byte c' x = byte c x)
    {a n : Nat} (obs : ∀ x, InSpan a n x → PayloadObserved P s c pl cp sp x) :
    Reloc.Copied c c' a a n :=
  fun j hj => keep _ (obs _ ⟨Nat.le_add_right _ _, by omega⟩)

theorem observed_word (keep : ∀ x, PayloadObserved P s c pl cp sp x → byte c' x = byte c x)
    {a : Nat} (obs : ∀ x, InSpan a 8 x → PayloadObserved P s c pl cp sp x) : word c' a = word c a :=
  Reloc.bytesT_congr (observed_copied keep obs)

theorem observed_static (keep : ∀ x, PayloadObserved P s c pl cp sp x → byte c' x = byte c x)
    {a : Nat} (mem : a ∈ payloadStatics) : word c' a = word c a :=
  observed_word keep fun _ hx => .static mem hx

theorem observed_domainField (keep : ∀ x, PayloadObserved P s c pl cp sp x → byte c' x = byte c x)
    {off : Nat} (mem : off ∈ [Layout.off_stack_high, Layout.off_trapsp]) :
    word c' ((word c' Layout.sym_Caml_state).toNat + off) = word c ((word c Layout.sym_Caml_state).toNat + off) := by
  rw [observed_static keep (a := Layout.sym_Caml_state) (by simp [payloadStatics])]
  exact observed_word keep fun _ hx => .domainField mem hx

/-- **The VM payload across kept bytes** (link words of the records excepted). -/
theorem VmPayload.keep_observed {high : Nat} (h : VmPayload P s c pl cp sp high)
    (keep : ∀ x, PayloadObserved P s c pl cp sp x → byte c' x = byte c x)
    (outputEq : output c'.σ = output c.σ) : VmPayload P s c' pl cp sp high := by
  have st := fun {a : Nat} (mem : a ∈ payloadStatics) => observed_static keep mem
  constructor
  · rw [observed_domainField keep (by simp)]; exact h.stackHigh
  · rw [observed_domainField keep (by simp)]; exact h.trapsp
  · rw [st (by simp [payloadStatics])]; exact h.codeBase
  · intro i w hi
    have he : word32 c' (pl.codeBase + 4 * i) = word32 c (pl.codeBase + 4 * i) :=
      Reloc.bytesT_congr (observed_copied keep fun _ hx => .code hi hx)
    simpa only [he] using h.code i w hi
  · rw [st (by simp [payloadStatics])]; exact h.globals
  · refine ⟨h.stack.1, ?_⟩
    intro i v hi
    rw [observed_word keep fun _ hx => .stack hi hx]
    exact h.stack.2 i v hi
  · constructor
    · intro l hl
      obtain ⟨a, o, ha, ho, layout⟩ := h.heap.1 l hl
      exact ⟨a, o, ha, ho, object_copied layout (observed_copied keep fun _ hx => .header ho ha hx)
        (observed_copied keep fun _ hx => .fields ho ha hx)⟩
    · exact h.heap.2
  · refine ⟨?_, ?_, ?_⟩
    · rw [outputEq]; exact h.world.output
    · intro id ch hc
      obtain ⟨a, ha, layout⟩ := h.world.chans id ch hc
      have le := layout.bufferLe
      refine ⟨a, ha, channel_copied_links layout (observed_copied keep fun _ hx => .chanFront hc ha hx) ?_⟩
      intro j hj
      exact keep _ (.chanBack hc ha ⟨Nat.le_add_right _ _, by unfold chanOffBuff at hj ⊢; omega⟩)
    · rw [st (by simp [payloadStatics])]; exact h.world.ooId
  · rw [st (by simp [payloadStatics])]; exact h.atomBase
  · rw [st (by simp [payloadStatics])]; exact h.argv

end Keep

end OCaml.Vm.Sim
