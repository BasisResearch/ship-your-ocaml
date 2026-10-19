import OCaml.Vm.Primitives.Uncaught.FatalUncaught
import OCaml.Vm.Primitives.Uncaught.FatalNames
import OCaml.Vm.Primitives.Uncaught.FormatCopy
import OCaml.Vm.Primitives.GprsPersist

/-!
# `caml_fatal_uncaught_exception`: the prologue and the handler lookup

From the entry: the 48-byte frame and its four saves (`pro_fast`), then
`caml_named_value("Printexc.handle_uncaught_exception")` over the named-value
table (`named_value_table`), which returns `NULL` when no handler is
registered (`FatalInput.noHandler`). The native frames lie above `heapEnd`, so
the memory below it is unchanged (`LowSame`), and the table with it.
-/

namespace OCaml.Vm.Primitives.Uncaught.FatalUncaught
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Vsa.MemRepr LeanRV64DExecutable OCaml.Bytecode OCaml.Vm.Primitives
  OCaml.Vm.Boot.Startup OCaml.Vm.Sim
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of gpr_some gprReg_ne_htif NameAt TableShape LookupInput
  NamedFound named_value_table strOf strcmp_loaded_of mask_pinned_of fixedBytes_transport)

/-- The memory below `heapEnd` is unchanged from `m` to `m'`. -/
def LowSame (m m' : Mem) : Prop := ∀ a, a < heapEnd → m'[a]? = m[a]?

theorem LowSame.refl (m : Mem) : LowSame m m := fun _ _ => rfl

theorem LowSame.trans {m m' m'' : Mem} (h : LowSame m m') (g : LowSame m' m'') : LowSame m m'' :=
  fun a ha => (g a ha).trans (h a ha)

/-- A store log in a native frame leaves the memory below `heapEnd`. -/
theorem low_writeLog {sp : BitVec 64} {n : Nat} (frame : NativeFrame sp n) (m : Mem) {log : List WEntry}
    (inside : LogInW [⟨nativeFrameBase sp n, sp.toNat⟩] log) : LowSame m (writeLog m log) := by
  intro a ha
  apply frameOn_writeLog _ m log inside a
  have := frame.lower
  refine ⟨Or.inl ?_, trivial⟩
  show a < sp.toNat - n
  omega

/-- **`caml_fatal_uncaught_exception(exn)` on the default path**: the caller's
registers, 128 bytes of native stack (the 48-byte frame and the lookup's and
`caml_memprof_set_suspended`'s frames below it), and the named-value table
without a `Printexc` handler. -/
structure FatalInput (ra sp exn s0 s1 s2 s3 : BitVec 64) (pl : Place) (named : List (String × Val))
    (chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)) (c : Config) : Prop where
  leaf : LeafInput ra c
  ready : LibraryReady c
  pc : PCAt 0x8000df50#64 c
  frame : NativeFrame sp 128
  stack : gprGet c.σ 2 = some sp
  arg : gprGet c.σ 10 = some exn
  saved0 : gprGet c.σ 8 = some s0
  saved1 : gprGet c.σ 9 = some s1
  saved2 : gprGet c.σ 18 = some s2
  saved3 : gprGet c.σ 19 = some s3
  table : TableShape c.σ.mem pl named chains
  /-- no `Printexc.set_uncaught_exception_handler` (Printexc not linked) -/
  noHandler : named.lookup "Printexc.handle_uncaught_exception" = none

/-- The fatal frame's base is `sp - 48`. -/
theorem fatal_sp {sp : BitVec 64} (frame : NativeFrame sp 128) :
    (sp + 18446744073709551568#64).toNat = nativeFrameBase sp 128 + 80 := by
  have lo : 128 ≤ sp.toNat := Nat.le_trans (Nat.le_add_left _ _) frame.lower
  have hi := sp.isLt
  unfold nativeFrameBase
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A word slot below `sp - 48 + 48`. -/
theorem fatal_slot {sp : BitVec 64} (frame : NativeFrame sp 128) {a : BitVec 64} {off : Nat}
    (ha : a.toNat = nativeFrameBase sp 128 + off) (bound : off + 8 ≤ 128) (al : off % 8 = 0) : WriteWindow a 8 := by
  have eq : a = BitVec.ofNat 64 (nativeFrameBase sp 128 + off) := by
    apply BitVec.eq_of_toNat_eq; rw [ha, frame.slot_nat (by omega)]
  rw [eq]; exact frame.word bound al

/-- After the handler lookup returned `NULL`: at `0x8000df78`. -/
structure Looked (before : Config) (sp exn s0 s2 s3 : BitVec 64) (d : Config) : Prop where
  leaf : LeafInput 0x8000df78#64 d
  ready : LibraryReady d
  pc : PCAt 0x8000df78#64 d
  result : gprGet d.σ 10 = some 0#64
  exn : gprGet d.σ 9 = some exn
  stack : gprGet d.σ 2 = some (sp + 18446744073709551568#64)
  saved0 : gprGet d.σ 8 = some s0
  saved2 : gprGet d.σ 18 = some s2
  saved3 : gprGet d.σ 19 = some s3
  callee : ∀ k, 20 ≤ k → k ≤ 27 → gprGet d.σ k = gprGet before.σ k
  low : LowSame before.σ.mem d.σ.mem
  output : Vsa.Machine.output d.σ = Vsa.Machine.output before.σ

/-- The memory of a frame log in the lookup's frame, below the fatal frame. -/
theorem lookup_slot {sp : BitVec 64} (frame : NativeFrame sp 128) (k : Nat) (hk : k ≤ 32) :
    (sp + 18446744073709551568#64 - 32#64 + BitVec.ofNat 64 k).toNat = nativeFrameBase sp 128 + (48 + k) := by
  have base := fatal_sp frame
  have hiS := frame.upper
  have hB : nativeFrameBase sp 128 + 128 = sp.toNat := by
    have := Nat.le_trans (Nat.le_add_left _ _) frame.lower; unfold nativeFrameBase; omega
  simp only [Layout.sym_stack_top] at hiS
  rw [BitVec.toNat_add, BitVec.toNat_sub, base, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- **The prologue and the handler lookup**: `caml_named_value` returns `NULL`. -/
theorem fatal_lookup (persist : GprsPersist_Statement) {ra sp exn s0 s1 s2 s3 : BitVec 64} {pl : Place}
    {named : List (String × Val)} {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} {c : Config}
    (h : FatalInput ra sp exn s0 s1 s2 s3 pl named chains c) :
    ∃ d, Steps c d ∧ Looked c sp exn s0 s2 s3 d := by
  have r1 := regsAt_of h.leaf.raReg
  have r2 := regsAt_of h.stack
  have r8 := regsAt_of h.saved0
  have r9 := regsAt_of h.saved1
  have r10 := regsAt_of h.arg
  have r18 := regsAt_of h.saved2
  have r19 := regsAt_of h.saved3
  have l0 : LeafInput (regsAt c 1) c := by rw [r1]; exact h.leaf
  have fp := fatal_sp h.frame
  have hiS := h.frame.upper
  have hB : nativeFrameBase sp 128 + 128 = sp.toNat := by
    have := Nat.le_trans (Nat.le_add_left _ _) h.frame.lower; unfold nativeFrameBase; omega
  have hE : heapEnd ≤ nativeFrameBase sp 128 := by have := h.frame.lower; omega
  simp only [Layout.sym_stack_top] at hiS
  have slot (k : Nat) (hk : k ≤ 48) :
      (sp + 18446744073709551568#64 + BitVec.ofNat 64 k).toNat = nativeFrameBase sp 128 + (80 + k) := by
    rw [BitVec.toNat_add, fp, BitVec.toNat_ofNat]; omega
  have subEq : sp - 48#64 = sp + 18446744073709551568#64 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  have win (k : Nat) (hk : k ≤ 40) (al : k % 8 = 0) : WriteWindow (sp + 18446744073709551568#64 + BitVec.ofNat 64 k) 8 :=
    fatal_slot h.frame (slot k (by omega)) (by omega) (by omega)
  have proIn : LogInW [⟨nativeFrameBase sp 128, sp.toNat⟩] (proLog (regsAt c) (pro_loads c.σ.mem (regsAt c))) := by
    simp only [proLog, LogInW, InsideW, r2, subEq, slot 24 (by decide), slot 32 (by decide), slot 40 (by decide),
      slot 16 (by decide), slot 8 (by decide)]
    refine ⟨Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega
  obtain ⟨c1, run1, p1⟩ := (pro_fast c (regsAt c) l0
    (by simp only [pro_input, GHolds, r1, r2, r8, r9, r10, r18, r19]
        exact ⟨h.leaf.raReg, h.stack, h.saved0, h.saved1, h.arg, h.saved2, h.saved3, trivial⟩)
    (by rw [r2]; exact win 24 (by decide) (by decide)) (by rw [r2]; exact win 32 (by decide) (by decide))
    (by rw [r2]; exact win 40 (by decide) (by decide)) (by rw [r2]; exact win 16 (by decide) (by decide))
    (by rw [r2]; exact win 8 (by decide) (by decide)) (h.frame.image_outside proIn)).run c ⟨h.pc, rfl⟩
  have o1 := p1.regs
  simp only [pro_regs, pro_loads, r1, r2, r8, r10, r18, r19, GHolds] at o1
  obtain ⟨g10, g9, g2, g1, g8, g18, g19, -⟩ := o1
  obtain ⟨c2, run2, p2⟩ := (call_registers_summary pro_call_shape pro_call_decode c1 (pro_call_pins p1.image)
    p1.good p1.image p1.tick p1.minstret
    [(10, 2147837296#64), (9, exn), (2, sp + 18446744073709551568#64), (8, s0), (18, s2), (19, s3)]
    ⟨g10, g9, g2, g8, g18, g19, trivial⟩ (by change KeysOK [10, 9, 2, 8, 18, 19]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl).run c1 ⟨p1.pc, rfl⟩
  have lslot (k : Nat) (hk : k ≤ 32) :
      (sp + 18446744073709551568#64 - 32#64 + BitVec.ofNat 64 k).toNat = nativeFrameBase sp 128 + (48 + k) :=
    lookup_slot h.frame k hk
  have saveIn : LogInW [⟨nativeFrameBase sp 128, sp.toNat⟩]
      (Named.NamedValue.saveLog (sp + 18446744073709551568#64) 0x8000df78#64 s0 exn) := by
    simp only [Named.NamedValue.saveLog, LogInW, InsideW, lslot 8 (by decide), lslot 24 (by decide), lslot 16 (by decide)]
    refine ⟨Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega
  have lookupWin (k : Nat) (hk : k ≤ 24) (al : k % 8 = 0) :
      WriteWindow (sp + 18446744073709551568#64 - 32#64 + BitVec.ofNat 64 k) 8 :=
    fatal_slot h.frame (lslot k (by omega)) (by omega) (by omega)
  have lookup : LookupInput 0x8000df78#64 (sp + 18446744073709551568#64) 2147837296#64 s0 exn handlerName c2 :=
    { leaf := ⟨p2.good, p2.image, p2.minstret, gholds_lookup (n := 1) _ p2.regs rfl, by decide, p2.tick⟩
      pc := by have := p2.pc; rw [pro_call_target] at this; exact this
      stack := gholds_lookup (n := 2) _ p2.regs rfl
      arg := gholds_lookup (n := 10) _ p2.regs rfl
      saved0 := gholds_lookup (n := 8) _ p2.regs rfl
      saved1 := gholds_lookup (n := 9) _ p2.regs rfl
      slot8 := lookupWin 8 (by decide) (by decide)
      slot24 := lookupWin 24 (by decide) (by decide)
      slot16 := lookupWin 16 (by decide) (by decide)
      named := handlerName_at p2.image
      apart := fun i hi => by
        have addr : (2147837296#64 + BitVec.ofNat 64 i).toNat = 2147837296 + i := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
          simp only [handlerName, List.length_cons, List.length_nil] at hi
          omega
        simp only [handlerName, List.length_cons, List.length_nil] at hi
        simp only [Named.NamedValue.saveLog, OutLRange, addr, lslot 8 (by decide), lslot 24 (by decide), lslot 16 (by decide)]
        have : (2256535552 : Nat) ≤ nativeFrameBase sp 128 := hE
        refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_, trivial⟩ <;> omega
      image := h.frame.image_outside saveIn }
  have low1 : LowSame c.σ.mem c2.σ.mem := fun a ha => by
    rw [p2.memory, p1.memory]; exact low_writeLog h.frame _ proIn a ha
  have lowS : LowSame c.σ.mem (writeLog c2.σ.mem (Named.NamedValue.saveLog (sp + 18446744073709551568#64) 0x8000df78#64 s0 exn)) :=
    low1.trans (low_writeLog h.frame _ saveIn)
  have textEnd : Image.textBase + Image.textSize ≤ heapEnd := by decide
  have rodataEnd : Image.rodataBase + Image.rodataSize ≤ heapEnd := by decide
  have rodataS := fixedBytes_transport h.leaf.image.rodata (fun a ha => lowS a (by omega))
  have query := rodata_cstring rodataS handlerName_rodata
  have qAddr : (2147837296#64 : BitVec 64).toNat = Image.rodataBase + 13296 := rfl
  rw [← qAddr] at query
  obtain ⟨d, r, run3, nf, absent, -⟩ := named_value_table lookup
    (h.table.transport lowS (strcmp_loaded_of (fixedBytes_transport h.leaf.image.text (fun a ha => lowS a (by omega))))
      (mask_pinned_of rodataS))
    query
    (fun cs str => by
      obtain ⟨cs0, str0, e⟩ := query
      have eq : cs = cs0 := str.unique str0
      subst eq
      have len := congrArg String.length e
      rw [Named.NamedValue.strOf_length, String.length_ofList] at len
      simp only [handlerName, List.length_cons, List.length_nil] at len
      rw [← len]
      constructor <;> decide)
  have r0 : r = 0#64 := absent (by
    rw [show strOf handlerName = "Printexc.handle_uncaught_exception" by decide]; exact h.noHandler)
  subst r0
  have run := run1.trans (run2.trans run3)
  have keep (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]) :
      gprGet d.σ k = gprGet c.σ k :=
    (nf.frame k lo hi out).trans ((p2.gpr_frame (by decide) k lo hi (fun m => out (by simp at m; simp [m]))).trans
      (p1.gpr_frame (by decide) k lo hi (fun m => out (by simp at m; rcases m with rfl | rfl | rfl <;> simp))))
  refine ⟨d, run, ?_⟩
  exact
    { leaf := ⟨nf.good, nf.image, nf.minstret, nf.returned, by decide, nf.tick⟩
      ready := h.ready.carry (GprsKept.of_steps persist run (keep 3 (by decide) (by decide) (by decide)))
        (nf.htif.trans ((p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans
          (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide))))
      pc := nf.pc
      result := nf.result
      exn := nf.saved1
      stack := nf.stack
      saved0 := nf.saved0
      saved2 := (keep 18 (by decide) (by decide) (by decide)).trans h.saved2
      saved3 := (keep 19 (by decide) (by decide) (by decide)).trans h.saved3
      callee := fun k lo hi => keep k (by omega) (by omega) (by simp; omega)
      low := fun a ha => by rw [nf.memory]; exact lowS a ha
      output := by simp only [Vsa.Machine.output]; rw [nf.output, p2.output, p1.output] }

end OCaml.Vm.Primitives.Uncaught.FatalUncaught
