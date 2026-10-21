import OCaml.Vm.Primitives.Leaf
import OCaml.Vm.Reloc

/-! The VM data visible during a C call. `Setup_for_c_call` temporarily changes
sp and parks PC inside the primitive, so `VmReprAt.atHead` is not a callee
precondition. This record keeps its memory/world components; the ABI frame
and the caller's generated restoration segment supply the register components. -/
namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- **A named-table chain across memory** whose bytes agree on its nodes. -/
theorem _root_.OCaml.Vm.NamedChain.frame {c c' : Config} {pl : Place} :
    ∀ {head : Nat} {l : List (Nat × List (BitVec 8) × Val)}, NamedChain c pl head l →
      (∀ e ∈ l, ∀ a, e.1 ≤ a → a < e.1 + 16 + e.2.1.length + 1 → byte c' a = byte c a) →
      NamedChain c' pl head l
  | _, _, .nil, _ => .nil
  | _, _, @NamedChain.cons _ _ node next key v rest hnode hrest, agree => by
    have inNode (a : Nat) (lo : node ≤ a) (hi : a < node + 16 + key.length + 1) : byte c' a = byte c a :=
      agree _ List.mem_cons_self a lo hi
    have w0 : word c' node = word c node :=
      Reloc.bytesT_congr (x := node) (x' := node) fun j hj => inNode (node + j) (by omega) (by omega)
    have w8 : word c' (node + 8) = word c (node + 8) :=
      Reloc.bytesT_congr (x := node + 8) (x' := node + 8) fun j hj => inNode (node + 8 + j) (by omega) (by omega)
    refine .cons ⟨hnode.low, hnode.arena, hnode.aligned, ?_, ?_, fun i hi => ?_, ?_⟩
      (hrest.frame fun e he => agree e (List.mem_cons_of_mem _ he))
    · rw [w0]; exact hnode.value
    · rw [w8]; exact hnode.next
    · rw [inNode _ (by omega) (by omega)]; exact hnode.keyBytes i hi
    · rw [inNode _ (by omega) (by omega)]; exact hnode.nul

/-- **The named table across memory** whose bytes agree on its footprint. -/
theorem _root_.OCaml.Vm.NamedRepr.frame {c c' : Config} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (Nat × List (BitVec 8) × Val)} (h : NamedRepr c pl named chains)
    (agree : ∀ a, NamedReprFoot chains a → byte c' a = byte c a) : NamedRepr c' pl named chains where
  heads := fun b hb => by
    have head : word c' (Layout.sym_named_value_table + 8 * b) = word c (Layout.sym_named_value_table + 8 * b) :=
      Reloc.bytesT_congr fun j hj => agree _ (Or.inl ⟨by omega, by simp only [Layout.sym_named_value_table]; omega⟩)
    rw [head]
    exact (h.heads b hb).frame fun e he a lo hi => agree a (Or.inr ⟨b, hb, e, he, lo, hi⟩)
  placed := h.placed
  entries := h.entries
  unique := h.unique

structure VmPayload (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high : Nat) : Prop where
  stackHigh : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).toNat = high
  trapsp : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp)).toNat = high - 8 * s.trap
  codeBase : (word c Layout.sym_caml_start_code).toNat = pl.codeBase
  code : CodeRepr P.code pl.codeBase c
  globals : valWord pl P.globals = some (word c Layout.sym_caml_global_data)
  stack : StackRepr c pl sp high s.stack
  heap : HeapRepr c pl cp P s
  world : WorldRepr c cp s.world
  atomBase : (word c Layout.sym_caml_atom_table).toNat = pl.atomBase
  /-- `main_argv` holds the program arguments' value (`caml_sys_argv`) -/
  argv : valWord pl s.world.argv = some (word c Layout.sym_main_argv)
  /-- `named_value_table` represents `world.named` (`caml_register_named_value`) -/
  named : ∃ chains, NamedRepr c pl s.world.named chains

theorem payload_of_repr {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} (h : VmReprAt P s c pl cp sp high) : VmPayload P s c pl cp sp high :=
  ⟨h.stackHigh, h.trapsp, h.codeBase, h.code, h.globals, h.stack, h.heap, h.world, h.atomBase, h.argv, h.named⟩

/-- Frame all data observations at once; no machine execution is assumed. -/
theorem VmPayload.frame {P : Prog} {s : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} (h : VmPayload P s c pl cp sp high)
    (hm : c'.σ.mem = c.σ.mem) (ho : c'.σ.sailOutput = c.σ.sailOutput) :
    VmPayload P s c' pl cp sp high := by
  have hw : ∀ a, word c' a = word c a := fun _ => by simp only [word, hm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hw] using h.stackHigh
  · simpa only [hw] using h.trapsp
  · simpa only [hw] using h.codeBase
  · simpa only [CodeRepr, word32, hm] using h.code
  · simpa only [hw] using h.globals
  · simpa only [StackRepr, hw] using h.stack
  · simpa only [HeapRepr, ObjAt, word, word32, byte, hm] using h.heap
  · simpa only [WorldRepr, output, ChanAt, word, word32, byte, hm, ho] using h.world
  · simpa only [hw] using h.atomBase
  · simpa only [hw] using h.argv
  · obtain ⟨chains, r⟩ := h.named
    exact ⟨chains, r.frame fun a _ => by simp only [byte, hm]⟩

/-- A root replacement may discard a pointer, but cannot invent a new live block. -/
theorem live_of_roots {heap : Heap} {rs rs' : List Val} {l : Nat}
    (h : Live heap rs l)
    (roots : ∀ v l, v ∈ rs → v.loc? = some l → Live heap rs' l) : Live heap rs' l := by
  -- discipline: allow(O5-run-induction) induction on heap graph reachability Live, not a machine/bytecode run
  induction h with
  | root hv hl => exact roots _ _ hv hl
  | field h hg hv hl ih => exact Live.field ih hg hv hl

/-- Replacing the accumulator by an existing root cannot create new live objects. -/
theorem live_accu_of_root {P : Prog} {s : St} {v : Val} {l : Nat}
    (root : ∀ l, v.loc? = some l → Live s.heap (roots P s) l)
    (h : Live s.heap (roots P {s with accu := v}) l) : Live s.heap (roots P s) l := by
  apply live_of_roots h
  intro v' loc hv hl
  change v' ∈ (v :: _) at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact root loc hl
  · exact Live.root (List.mem_cons_of_mem _ hv) hl

theorem live_accu_int {P : Prog} {s : St} {n : BitVec 63} {l : Nat}
    (h : Live s.heap (roots P {s with accu := .int n}) l) : Live s.heap (roots P s) l :=
  live_accu_of_root (fun _ hl => by cases hl) h

/-- A read-only return may select an existing root and retain its representation. -/
theorem VmPayload.accu_of_root {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} (h : VmPayload P s c pl cp sp high) (v : Val)
    (root : ∀ l, v.loc? = some l → Live s.heap (roots P s) l) :
    VmPayload P {s with accu := v} c pl cp sp high := by
  refine { h with heap := ?_ }
  constructor
  · intro l hl
    exact h.heap.1 l (live_accu_of_root root hl)
  · intro l l' a a' o o' hl hl' hn hp hp' hg hg'
    exact h.heap.2 l l' a a' o o' (live_accu_of_root root hl) (live_accu_of_root root hl') hn hp hp' hg hg'

/-- Returning an immediate discards roots without inventing a live object. -/
theorem VmPayload.accu_int {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} (h : VmPayload P s c pl cp sp high) (n : BitVec 63) :
    VmPayload P {s with accu := .int n} c pl cp sp high :=
  h.accu_of_root (.int n) (fun _ hl => by cases hl)

/-- Resolve the unique placement and object of a live abstract location. -/
theorem VmPayload.object_at {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high l a : Nat} {o : Obj} (h : VmPayload P s c pl cp sp high)
    (live : Live s.heap (roots P s) l) (placed : pl.φ l = some a)
    (object : s.heap.get? l = some o) : ObjAt c pl cp a o := by
  obtain ⟨a', o', ha, ho, layout⟩ := h.heap.1 l live
  have hea : a' = a := Option.some.inj (ha.symm.trans placed)
  have heo : o' = o := Option.some.inj (ho.symm.trans object)
  simpa only [hea, heo] using layout

/-- Runtime predicates defined only by memory (such as collector bounds and
memory-based free-list invariants) satisfy this frame rule. It must be supplied
for the chosen `Layout.runtimeOk`; arbitrary Config predicates do not. -/
def MemoryStable (runtimeOk : Config → Prop) : Prop :=
  ∀ c c', c'.σ.mem = c.σ.mem → runtimeOk c → runtimeOk c'

end OCaml.Vm.Primitives
