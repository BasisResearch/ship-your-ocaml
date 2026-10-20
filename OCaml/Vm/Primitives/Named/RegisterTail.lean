import OCaml.Vm.Primitives.Named.RegisterFront
import OCaml.Vm.Primitives.Named.NamedTableUpdate
import OCaml.Vm.Primitives.GprsPersist
import OCaml.Vm.Boot.Startup.RuntimeKept
import OCaml.Vm.Boot.Startup.NativeRead
import OCaml.Vm.Boot.Startup.NativeNested
import OCaml.Vm.Boot.Startup.ClearReady
import OCaml.Vm.Boot.Startup.LeafReady
import OCaml.Vm.Boot.Startup.MemcpyFresh
import OCaml.Vm.Boot.Startup.CallerFrame
import OCaml.Vm.Primitives.Channel.OpenDescriptorCall
import OCaml.Vm.Sim.CopyStringInput
import OCaml.Vm.Primitives.Named.GenRoots

/-!
# `caml_register_named_value` after the found/new split

Both paths end in the epilogue at `0x800214d0`, which reloads the six saves
of the prologue from the 64-byte frame and returns `Val_unit`
(`epilogue`). The found path stores the new value through
`caml_modify_generational_global_root(&nv->val, v)`; the new-node path
copies the key into a fresh `caml_stat_alloc` block, links it at the bucket's
head and files its value slot with `caml_register_generational_global_root`.

The two global-root callees are `GenRoots.RootCallsG` (proved from their
machine runs, `rootCallsG`). The caller carries the roots' invariant
`RootsAt` with the table's value slots registered (`RegisterTable.roots`,
`registered`); both paths return `Registered`, whose post is `NamedRootsAt` on
newlib's new blocks. Every byte outside the lists, `random_seed` (`RootsG`),
the allocator's footprint, the path's writes and the stack window is kept.
-/

namespace OCaml.Vm.Primitives.Named.NamedRegister
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Vsa.MemRepr LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Sim
  OCaml.Vm.Boot.Startup VsaIris VsaIris.Inst VsaIris.VsaHeap
open NamedValue (regsAt regsAt_of gpr_some gpr_some_of gprReg_ne_htif wl_nil)

/-! ### The frame's saves -/

theorem frame64 {sp : BitVec 64} {size : Nat} (frame : NativeFrame sp size) (big : 64 ≤ size) :
    sp + 18446744073709551552#64 = BitVec.ofNat 64 (sp.toNat - 64) := by
  have lower := frame.lower
  have hE : heapEnd = 0x86800000 := rfl
  have l : 64 ≤ sp.toNat := by omega
  bv_omega

theorem slot_toNat {sp : BitVec 64} {size : Nat} (frame : NativeFrame sp size) (big : 64 ≤ size) {k : Nat}
    (hk : k ≤ 64) : (sp - 64#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 64 + k := by
  have lower := frame.lower
  have upper := frame.upper
  have hE : heapEnd = 0x86800000 := rfl
  have hT : Layout.sym_stack_top = 0x88000000 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- **The prologue's saves read back** from its log. -/
theorem saveLog_words (m : Mem) (R : Nat → BitVec 64) {size : Nat} (frame : NativeFrame (R 2) size)
    (big : 64 ≤ size) :
    bytesT (writeLog m (saveLog R)) ((R 2).toNat - 64 + 56) 8 = R 1 ∧
    bytesT (writeLog m (saveLog R)) ((R 2).toNat - 64 + 48) 8 = R 8 ∧
    bytesT (writeLog m (saveLog R)) ((R 2).toNat - 64 + 40) 8 = R 9 ∧
    bytesT (writeLog m (saveLog R)) ((R 2).toNat - 64 + 32) 8 = R 18 ∧
    bytesT (writeLog m (saveLog R)) ((R 2).toNat - 64 + 24) 8 = R 19 ∧
    bytesT (writeLog m (saveLog R)) ((R 2).toNat - 64 + 16) 8 = R 20 := by
  have s := fun k hk => slot_toNat (k := k) frame big hk
  have e16 := s 16 (by decide); have e24 := s 24 (by decide); have e32 := s 32 (by decide)
  have e40 := s 40 (by decide); have e48 := s 48 (by decide); have e56 := s 56 (by decide)
  have lower := frame.lower
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Gc.word_writeLog_at m (saveLog R) 2 _ _ (by simp [saveLog, proLog, e56])
      (by simp only [saveLog, proLog, List.drop, OutLRange, e48, e32, e24, and_true]; omega)
  · exact Gc.word_writeLog_at m (saveLog R) 3 _ _ (by simp [saveLog, proLog, e48])
      (by simp only [saveLog, proLog, List.drop, OutLRange, e32, e24, and_true]; omega)
  · exact Gc.word_writeLog_at m (saveLog R) 0 _ _ (by simp [saveLog, proLog, e40])
      (by simp only [saveLog, proLog, List.drop, OutLRange, e16, e56, e48, e32, e24, and_true]; omega)
  · exact Gc.word_writeLog_at m (saveLog R) 4 _ _ (by simp [saveLog, proLog, e32])
      (by simp only [saveLog, proLog, List.drop, OutLRange, e24, and_true]; omega)
  · exact Gc.word_writeLog_at m (saveLog R) 5 _ _ (by simp [saveLog, proLog, e24]) True.intro
  · exact Gc.word_writeLog_at m (saveLog R) 1 _ _ (by simp [saveLog, proLog, e16])
      (by simp only [saveLog, proLog, List.drop, OutLRange, e56, e48, e32, e24, and_true]; omega)

/-! ### The epilogue -/

/-- At the return: `Val_unit`, the caller's registers, readiness at the
caller's `sp` and `ra`, memory and output unchanged by the epilogue. -/
structure Epilogued (live : Nat → Prop) (H : List (Nat × Nat)) (cap : Nat) (R : Nat → BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt (R 1) after
  result : gprGet after.σ 10 = some 1#64
  saved : ∀ n ∈ [8, 9, 18, 19, 20], gprGet after.σ n = some (R n)
  ready : RuntimeReadyL live H cap (R 2) (R 1) after
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput

/-- **The epilogue at `0x800214d0`**: the frame's six slots hold the
prologue's saves; it restores them and returns `Val_unit`. -/
theorem epilogue {live : Nat → Prop} {H : List (Nat × Nat)} {cap : Nat} {R : Nat → BitVec 64} {ra : BitVec 64}
    {m : Mem} {e : Config} {size : Nat}
    (ready : RuntimeReadyL live H cap (R 2 + 18446744073709551552#64) ra e) (pc : PCAt 0x800214d0#64 e)
    (aligned : (R 1).toNat % 4 = 0)
    (frame : NativeFrame (R 2) size) (big : 64 ≤ size)
    (slots : ∀ k, 16 ≤ k → k < 64 → (e.σ.mem[(R 2).toNat - 64 + k]?).getD 0 =
      ((writeLog m (saveLog R))[(R 2).toNat - 64 + k]?).getD 0) :
    ∃ f, Steps e f ∧ Epilogued live H cap R e f := by
  have f64 := frame64 frame big
  have lower := frame.lower
  have upper := frame.upper
  have hE : heapEnd = 0x86800000 := rfl
  have hT : Layout.sym_stack_top = 0x88000000 := rfl
  let D := regsAt e
  have d2 : D 2 = R 2 + 18446744073709551552#64 := regsAt_of ready.stack
  have regs : GHolds e.σ (done_input D) := ⟨by rw [d2]; exact ready.stack, trivial⟩
  have at_k (k : Nat) (hk : k ≤ 64) : (D 2 + BitVec.ofNat 64 k).toNat = (R 2).toNat - 64 + k := by
    rw [d2, f64, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have win (k : Nat) (hk : k + 8 ≤ 64) (al : k % 8 = 0) : ReadWindow (D 2 + BitVec.ofNat 64 k) 8 := by
    have w := (frame.resize (small := 64) big (by decide)).read_slot (off := k) hk al
    rwa [nativeStack, show -BitVec.ofNat 64 64 = (18446744073709551552#64 : BitVec 64) by decide, ← d2] at w
  have word (k : Nat) (lo : 16 ≤ k) (hk : k + 8 ≤ 64) :
      bytesVal .ld (read8 e.σ.mem (D 2 + BitVec.ofNat 64 k).toNat) =
        bytesT (writeLog m (saveLog R)) ((R 2).toNat - 64 + k) 8 := by
    rw [read8_value, at_k k (by omega)]
    exact word_observed _ fun i hi => by
      rw [show (R 2).toNat - 64 + k + i = (R 2).toNat - 64 + (k + i) by omega]
      exact slots _ (by omega) (by omega)
  obtain ⟨w56, w48, w40, w32, w24, w16⟩ := saveLog_words m R frame big
  have savedRa : bytesVal .ld (read8 e.σ.mem (D 2 + 56#64).toNat) = R 1 := (word 56 (by decide) (by decide)).trans w56
  have leaf : LeafInput (D 1) e := by
    rw [show D 1 = ra from regsAt_of ready.raReg]
    exact ready.toLeafInput
  obtain ⟨f, run, post⟩ := (done_fast e (R 1) D leaf regs (win 56 (by decide) (by decide))
    (win 48 (by decide) (by decide)) (win 40 (by decide) (by decide)) (win 32 (by decide) (by decide))
    (win 24 (by decide) (by decide)) (win 16 (by decide) (by decide)) savedRa aligned).run e ⟨pc, rfl⟩
  have r (n : Nat) (v : BitVec 64) (h : lookupG n (done_regs D (done_loads e.σ.mem D)) = some v) :
      gprGet f.σ n = some v := gholds_lookup _ post.regs h
  have sp' : gprGet f.σ 2 = some (R 2) := by
    rw [r 2 _ rfl, d2, BitVec.add_assoc]
    rw [show (18446744073709551552#64 : BitVec 64) + 64#64 = 0#64 by decide, BitVec.add_zero]
  have ra' : gprGet f.σ 1 = some (R 1) := by
    rw [r 1 _ rfl]; exact congrArg some savedRa
  refine ⟨f, run, { pc := post.pc, result := r 10 _ rfl, saved := ?_, ready := ?_,
                    memory := by rw [post.memory, wl_nil], output := post.output }⟩
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · rw [r 8 _ rfl]; exact congrArg some ((word 48 (by decide) (by decide)).trans w48)
    · rw [r 9 _ rfl]; exact congrArg some ((word 40 (by decide) (by decide)).trans w40)
    · rw [r 18 _ rfl]; exact congrArg some ((word 32 (by decide) (by decide)).trans w32)
    · rw [r 19 _ rfl]; exact congrArg some ((word 24 (by decide) (by decide)).trans w24)
    · rw [r 20 _ rfl]; exact congrArg some ((word 16 (by decide) (by decide)).trans w16)
  · apply ready.effect post (by decide) (by simp only [done_regs, keysG]; decide) (by decide) sp' ra' aligned
    · intro a _; rw [wl_nil]
    · intro a _; rw [wl_nil]
    · intro a h; rw [wl_nil]; exact h


/-! ### The found path -/

/-- The bytes a roots call may change besides newlib's: the lists' footprints
at `m` and `random_seed`. -/
def RootsG (Shape : Mem → Nat → List (BitVec 64) → Prop) (foot : Mem → Nat → List (BitVec 64) → Nat → Prop)
    (m : Mem) (a : Nat) : Prop :=
  OCaml.Vm.Gc.Skiplist.ListsFoot Shape foot m a ∨ (OCaml.Vm.Gc.Skiplist.randomSeed ≤ a ∧
    a < OCaml.Vm.Gc.Skiplist.randomSeed + 4)

/-- **Readiness after either path**, on newlib's blocks `H'`: newlib's
footprint within the old one and `G`, and `Post H'` of the memory. -/
structure ReadyAfter (live : Nat → Prop) (G : Nat → Prop) (Post : List (Nat × Nat) → Mem → Prop)
    (H H' : List (Nat × Nat)) (cap' : Nat) (sp ra : BitVec 64) (after : Config) : Prop where
  ready : RuntimeReadyL live H' cap' sp ra after
  heap : ∀ a, vsaFoot H' a → vsaFoot H a ∨ G a
  post : Post H' after.σ.mem

/-- **At the return of either path**: `Val_unit`, the caller's registers,
readiness on newlib's new blocks with `Post`, and every byte kept outside `G`,
the allocator's footprint, the path's own writes `own` and the stack window
below the caller's `sp`. -/
structure Returned (live : Nat → Prop) (G : Nat → Prop) (Post : List (Nat × Nat) → Mem → Prop) (depth : Nat)
    (H : List (Nat × Nat)) (R : Nat → BitVec 64) (own : Nat → Prop) (before after : Config) : Prop where
  pc : PCAt (R 1) after
  result : gprGet after.σ 10 = some 1#64
  saved : ∀ n ∈ [8, 9, 18, 19, 20], gprGet after.σ n = some (R n)
  ready : ∃ H' cap', ReadyAfter live G Post H H' cap' (R 2) (R 1) after
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  kept : ∀ x, ¬ G x → ¬ vsaFoot H x → ¬ own x → (x < (R 2).toNat - (64 + depth) ∨ (R 2).toNat ≤ x) →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

/-- A byte at or above the arena's end is no allocator byte. -/
theorem not_foot_high {H : List (Nat × Nat)} {a : Nat} (ha : heapEnd ≤ a) : ¬ vsaFoot H a := by
  rintro (g | ⟨_, l, _⟩)
  · unfold allocGlobal InRange at g; unfold heapEnd at ha; omega
  · omega

/-- The prologue's saves lie in the 64 bytes below the caller's `sp`. -/
theorem saveLog_inside {R : Nat → BitVec 64} {size : Nat} (frame : NativeFrame (R 2) size) (big : 64 ≤ size) :
    LogInW [⟨(R 2).toNat - 64, (R 2).toNat⟩] (saveLog R) := by
  have s := fun k hk => slot_toNat (k := k) frame big hk
  have e16 := s 16 (by decide); have e24 := s 24 (by decide); have e32 := s 32 (by decide)
  have e40 := s 40 (by decide); have e48 := s 48 (by decide); have e56 := s 56 (by decide)
  have lower := frame.lower
  simp only [saveLog, proLog, LogInW, InsideW, e16, e24, e32, e40, e48, e56, and_true]
  omega

/-- Readiness at a callee's entry, from the caller's entry readiness: the
run wrote only the prologue's saves and kept register presence. -/
theorem ready_at_call {live : Nat → Prop} {H : List (Nat × Nat)} {cap : Nat} {R : Nat → BitVec 64}
    {c d : Config} {sp ra : BitVec 64} {size : Nat} (persist : GprsPersist_Statement)
    (ready : RuntimeReadyL live H cap (R 2) (R 1) c) (frame : NativeFrame (R 2) size) (big : 64 ≤ size)
    (run : Steps c d) (leaf : LeafInput ra d) (stack : gprGet d.σ 2 = some sp) (gp : gpr d 3 = gpr c 3)
    (htif : d.σ.regs.get? Register.htif_payload_writes = c.σ.regs.get? Register.htif_payload_writes)
    (memory : d.σ.mem = writeLog c.σ.mem (saveLog R)) : RuntimeReadyL live H cap sp ra d := by
  have lower := frame.lower
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have out (a : Nat) (ha : a < heapEnd) : OutW [⟨(R 2).toNat - 64, (R 2).toNat⟩] a :=
    ⟨Or.inl (show a < (R 2).toNat - 64 by omega), trivial⟩
  refine ready.of_kept leaf stack (GprsKept.of_steps persist run gp) htif memory (saveLog_inside frame big)
    (fun pin hp => out _ (by have := (allocator_sources pin hp).geometry.high; omega))
    (by simp only [OutWRange, Layout.sym_Caml_state, and_true]; omega)
    (by simp only [OutWRange, Layout.sym_pool, and_true]; omega)
    (fun a foot => out a ?_)
  rcases foot with g | ⟨_, l, _⟩
  · unfold allocGlobal InRange at g; omega
  · exact l

/-- **The found path**, from the split at `0x80021470` with the query's node
`n0` in `s0`, a registered slot: `caml_modify_generational_global_root(&n0->val,
v)` stores the value (`RootCallsG.modify`), then the epilogue returns
`Val_unit`; the roots after it are at `S` with new lists. -/
theorem found_tail {live : Nat → Prop} {depth : Nat}
    {Shape : Mem → Nat → List (BitVec 64) → Prop} {foot : Mem → Nat → List (BitVec 64) → Nat → Prop}
    {Table : Mem → (Nat → Nat) → Prop} {tfoot : Mem → Nat → Prop}
    (ops : OCaml.Vm.Gc.Skiplist.Ops Shape foot) (tf : OCaml.Vm.Gc.PageTableFrame Table tfoot)
    (roots : GenRoots.RootCallsG Shape foot Table tfoot)
    (persist : GprsPersist_Statement) {H : List (Nat × Nat)} {cap : Nat} {R : Nat → BitVec 64}
    {name : List (BitVec 8)} {n0 : BitVec 64} {S : GenRoots.RootsState} {c d : Config}
    (ready : RuntimeReadyL live H cap (R 2) (R 1) c) (frame : NativeFrame (R 2) (64 + depth))
    (deepR : 32 + OCaml.Vm.Gc.Skiplist.opStack ≤ depth)
    (depthAligned : depth % 16 = 0) (run : Steps c d) (looked : Looked R name n0 c d) (nz : n0 ≠ 0#64)
    (I : GenRoots.RootsAt Shape foot Table tfoot H S c.σ.mem) (registered : n0 ∈ S.slots) :
    ∃ f, Steps d f ∧
      Returned live (RootsG Shape foot c.σ.mem)
        (fun H' m => ∃ ys' os', GenRoots.RootsAt Shape foot Table tfoot H' { S with ys := ys', os := os' } m)
        depth H R (VsaIris.InExt (n0.toNat, 8)) c f ∧
      bytesT f.σ.mem n0.toNat 8 = R 11 := by
  have big : 64 ≤ 64 + depth := Nat.le_add_right _ _
  have lower := frame.lower
  have upper := frame.upper
  have hE : heapEnd = 0x86800000 := rfl
  have nodeHigh := I.slotHigh n0 registered
  have pc0 : PCAt 0x80021470#64 d := by have := looked.pc; rwa [if_neg nz] at this
  let D := regsAt d
  obtain ⟨r1, hr1, al1⟩ := looked.link
  have leaf0 : LeafInput (D 1) d := by
    rw [show D 1 = r1 from regsAt_of hr1]; exact ⟨looked.good, looked.image, looked.minstret, hr1, al1, looked.tick⟩
  have regs0 : GHolds d.σ (found_input D) :=
    ⟨gpr_some (gpr_some_of hr1), gpr_some (gpr_some_of looked.node), gpr_some looked.a0,
      gpr_some (gpr_some_of looked.value), trivial⟩
  obtain ⟨d1, run1, p1⟩ := (found_fast d D leaf0 regs0).run d ⟨pc0, rfl⟩
  have d8 : D 8 = n0 := regsAt_of looked.node
  have d20 : D 20 = R 11 := regsAt_of looked.value
  have d1_10 : gprGet d1.σ 10 = some n0 := by rw [← d8]; exact gholds_lookup _ p1.regs rfl
  have d1_11 : gprGet d1.σ 11 = some (R 11) := by rw [← d20]; exact gholds_lookup _ p1.regs rfl
  have d1_2 : gprGet d1.σ 2 = some (R 2 + 18446744073709551552#64) :=
    (p1.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans looked.stack
  let args : GRegs := [(10, n0), (11, R 11), (2, R 2 + 18446744073709551552#64)]
  obtain ⟨d2, run2, p2⟩ := (call_registers_summary found_call_shape found_call_decode d1 (found_call_pins p1.image)
    p1.good p1.image p1.tick p1.minstret args ⟨d1_10, d1_11, d1_2, trivial⟩ (by change KeysOK [10, 11, 2]; decide)
    (by simp [KeysAvoidRa, args, keysG]) rfl).run d1 ⟨p1.pc, rfl⟩
  have mem2 : d2.σ.mem = writeLog c.σ.mem (saveLog R) := by
    rw [p2.memory, p1.memory, wl_nil, looked.memory]
  have gp2 : gpr d2 3 = gpr c 3 :=
    (p2.toEffectPost.gpr_frame (by decide) 3 (by decide) (by decide) (by decide)).trans
      ((p1.toEffectPost.gpr_frame (by decide) 3 (by decide) (by decide) (by decide)).trans
        (looked.frame 3 (by decide) (by decide) (by decide)))
  have htif2 : d2.σ.regs.get? Register.htif_payload_writes = c.σ.regs.get? Register.htif_payload_writes :=
    (p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans
      ((p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans looked.htif)
  have leaf2 : LeafInput found_call.link d2 :=
    ⟨p2.good, p2.image, p2.minstret, gholds_lookup _ p2.regs rfl, by decide, p2.tick⟩
  have sp2 : gprGet d2.σ 2 = some (R 2 + 18446744073709551552#64) := gholds_lookup _ p2.regs rfl
  have ready2 := ready_at_call persist ready frame big (run.trans (run1.trans run2)) leaf2 sp2 gp2 htif2 mem2
  have frame2 : NativeFrame (R 2 + 18446744073709551552#64) depth := by
    have n := frame.nested (front := 64) (by decide)
    rwa [nativeStack, show -BitVec.ofNat 64 64 = (18446744073709551552#64 : BitVec 64) by decide] at n
  have sp2Nat : (R 2 + 18446744073709551552#64).toNat = (R 2).toNat - 64 := by
    rw [frame64 frame big, BitVec.toNat_ofNat]; omega
  -- the roots at the call
  have low2 : ∀ a, a < heapEnd → (d2.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := fun a ha => by
    rw [mem2, frameOn_writeLog _ _ _ (saveLog_inside frame big) a ⟨Or.inl (show a < (R 2).toNat - 64 by omega),
      trivial⟩]
  have I2 := I.of_low ops tf low2
  have lists2 : ∀ a, OCaml.Vm.Gc.Skiplist.ListsFoot Shape foot d2.σ.mem a ↔
      OCaml.Vm.Gc.Skiplist.ListsFoot Shape foot c.σ.mem a :=
    I.roots.listsFoot_keep ops fun a ⟨_, _, _, sh, f⟩ => low2 a (ops.low _ _ _ sh a f)
  have entry : GenRoots.ModifyEntry H cap (R 2 + 18446744073709551552#64) found_call.link n0 (R 11) d2 :=
    { leaf := leaf2
      slot := gholds_lookup _ p2.regs rfl
      value := gholds_lookup _ p2.regs rfl
      stack := sp2
      heap := ready2.heap
      frame := frame2.resize deepR (by decide)
      s0 := ready2.platform.gpr 8 (by decide) (by decide)
      s1 := ready2.platform.gpr 9 (by decide) (by decide) }
  obtain ⟨d3, run3, rp, slot, H3, cap3, ys', os', next⟩ :=
    (roots.modify d2 H cap S _ _ n0 (R 11) I2 registered entry).run d2 ⟨p2.pc, rfl⟩
  have ready3 := rp.ready ready2 run3 (by decide) next.heap
  let J := regsAt d3
  have leaf3 : LeafInput (J 1) d3 := by rw [show J 1 = _ from regsAt_of ready3.raReg]; exact ready3.toLeafInput
  obtain ⟨d4, run4, p4⟩ := (foundJoin_fast d3 J leaf3 ⟨gpr_some (ready3.gpr_some 10 (by decide) (by decide)), trivial⟩).run
    d3 ⟨rp.pc, rfl⟩
  have ready4 : RuntimeReadyL live H3 cap3 (R 2 + 18446744073709551552#64) found_call.link d4 :=
    ready3.effect p4 (by decide) (by simp [foundJoin_regs, keysG]) (by decide)
      ((p4.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready3.stack)
      ((p4.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready3.raReg) (by decide)
      (fun a _ => by rw [wl_nil]) (fun a _ => by rw [wl_nil]) (fun a h => by rw [wl_nil]; exact h)
  have mem4 : d4.σ.mem = d3.σ.mem := by rw [p4.memory, wl_nil]
  -- the bytes the call keeps, in the caller's terms
  have offOf (x : Nat) (nG : ¬ RootsG Shape foot c.σ.mem x) (nF : ¬ vsaFoot H x) :
      GenRoots.Off Shape foot H d2.σ.mem x :=
    ⟨fun l => nG (Or.inl ((lists2 x).1 l)), nF, by
      rcases Nat.lt_or_ge x OCaml.Vm.Gc.Skiplist.randomSeed with h | h
      · exact Or.inl h
      · exact Or.inr (Nat.le_of_not_lt fun l => nG (Or.inr ⟨h, l⟩))⟩
  have keep3 (x : Nat) (nG : ¬ RootsG Shape foot c.σ.mem x) (nF : ¬ vsaFoot H x)
      (nOwn : ¬ VsaIris.InExt (n0.toNat, 8) x)
      (win : x < (R 2).toNat - (64 + depth) ∨ (R 2).toNat - 64 ≤ x) :
      (d3.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 ∨ (R 2).toNat - 64 ≤ x := by
    rcases win with lo | hi
    · left
      rw [next.kept x (offOf x nG nF) (fun i => nOwn i) (Or.inl (by rw [sp2Nat]; unfold OCaml.Vm.Gc.Skiplist.opStack at deepR ⊢; omega)), mem2,
        frameOn_writeLog _ _ _ (saveLog_inside frame big) x ⟨Or.inl (show x < (R 2).toNat - 64 by omega), trivial⟩]
    · exact Or.inr hi
  have high (x : Nat) (hx : heapEnd ≤ x) : ¬ RootsG Shape foot c.σ.mem x := by
    rintro (⟨_, _, _, sh, f⟩ | ⟨-, l⟩)
    · have := ops.low _ _ _ sh x f; omega
    · unfold OCaml.Vm.Gc.Skiplist.randomSeed at l; omega
  have slots : ∀ k, 16 ≤ k → k < 64 → (d4.σ.mem[(R 2).toNat - 64 + k]?).getD 0 =
      ((writeLog c.σ.mem (saveLog R))[(R 2).toNat - 64 + k]?).getD 0 := by
    intro k lo hi
    rw [mem4, next.kept _ (offOf _ (high _ (by omega)) (not_foot_high (by omega)))
      (fun i => by unfold GenRoots.InWord at i; omega) (Or.inr (by rw [sp2Nat]; omega)), mem2]
  obtain ⟨f, run5, ep⟩ := epilogue ready4 p4.pc ready.aligned frame big slots
  refine ⟨f, run1.trans (run2.trans (run3.trans (run4.trans run5))), ?_, ?_⟩
  · refine { pc := ep.pc, result := ep.result, saved := ep.saved,
             ready := ⟨H3, cap3, ep.ready, fun a v => (next.heapIn a v).imp id fun l => Or.inl ((lists2 a).1 l),
               ys', os', by rw [ep.memory, mem4]; exact next.roots⟩,
             output := ?_, kept := ?_ }
    · have a : Vsa.Machine.output f.σ = Vsa.Machine.output d3.σ := by
        simp only [Vsa.Machine.output, ep.output, p4.output]
      have b : Vsa.Machine.output d2.σ = Vsa.Machine.output c.σ := by
        simp only [Vsa.Machine.output, p2.output, p1.output, looked.output]
      have e3 : Vsa.Machine.output d3.σ = Vsa.Machine.output d2.σ := by
        simp only [Vsa.Machine.output, rp.output]
      rw [a, e3, b]
    · intro x nG nF nOwn win
      rw [ep.memory, mem4]
      rcases win with lo | hi
      · rcases keep3 x nG nF nOwn (Or.inl lo) with e | e
        · exact e
        · omega
      · rw [next.kept x (offOf x nG nF) (fun i => nOwn i) (Or.inr (by rw [sp2Nat]; omega)), mem2,
          frameOn_writeLog _ _ _ (saveLog_inside frame big) x ⟨Or.inr hi, trivial⟩]
  · rw [ep.memory, mem4]; exact slot

/-! ### The new-node path: the key's length and the node's block -/

/-- **The new node's block** at `caml_stat_alloc`'s return: the fresh block
`p` of `len + 24` bytes, the length saved at `sp + 8`, and `s1`–`s4` still
the key, the bucket index, the table and the value. -/
structure MissAllocated (live : Nat → Prop) (depth : Nat) (H : List (Nat × Nat)) (cap : Nat)
    (R : Nat → BitVec 64) (name : List (BitVec 8)) (p : BitVec 64) (c d : Config) : Prop where
  ready : RuntimeReadyL live ((p.toNat, name.length + 24) :: H) cap (R 2 + 18446744073709551552#64)
    alloc_call.link d
  pc : PCAt alloc_call.link d
  result : gprGet d.σ 10 = some p
  nonzero : p ≠ 0#64
  low : heapStart ≤ p.toNat
  high : p.toNat + (name.length + 24) ≤ heapEnd
  align : p.toNat % 16 = 0
  fresh : ∀ e ∈ H, ∀ y, InExt (p.toNat, name.length + 24) y → ¬ InExt e y
  key : gprGet d.σ 9 = some (R 10)
  bucket : gprGet d.σ 18 = some (BitVec.ofNat 64 ((NamedValue.hashBytes name).toNat % 13))
  table : gprGet d.σ 19 = some tableReg
  value : gprGet d.σ 20 = some (R 11)
  length : bytesT d.σ.mem ((R 2).toNat - 64 + 8) 8 = BitVec.ofNat 64 name.length
  slots : ∀ k, 16 ≤ k → k < 64 → (d.σ.mem[(R 2).toNat - 64 + k]?).getD 0 =
    ((writeLog c.σ.mem (saveLog R))[(R 2).toNat - 64 + k]?).getD 0
  kept : ∀ x, ¬ vsaFoot H x → (x < (R 2).toNat - (64 + depth) ∨ (R 2).toNat ≤ x) →
    (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ

/-- **The new-node path to its block**: from the split at `0x80021480`,
`strlen(name)`, then `caml_stat_alloc(len + 24)`. -/
theorem miss_allocate {live : Nat → Prop} [LibraryLive live] {depth : Nat}
    (persist : GprsPersist_Statement) {H : List (Nat × Nat)} {cap charge : Nat} {R : Nat → BitVec 64}
    {name : List (BitVec 8)} {c d : Config}
    (ready : RuntimeReadyL live H (cap + charge) (R 2) (R 1) c) (frame : NativeFrame (R 2) (64 + depth))
    (deep : 544 ≤ depth) (depthAligned : depth % 16 = 0)
    (named : NamedValue.NameAt c.σ.mem (R 10) name) (keyLow : heapStart ≤ (R 10).toNat)
    (keyHigh : (R 10).toNat + name.length + 8 ≤ heapEnd) (charged : vsaChg (name.length + 24) charge)
    (run : Steps c d) (looked : Looked R name 0#64 c d) :
    ∃ e p, Steps d e ∧ MissAllocated live depth H cap R name p c e := by
  have big : 64 ≤ 64 + depth := Nat.le_add_right _ _
  have lower := frame.lower
  have upper := frame.upper
  have spAl := frame.aligned
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have hT : Layout.sym_stack_top = 0x88000000 := rfl
  have pc0 : PCAt 0x80021480#64 d := by have := looked.pc; rwa [if_pos rfl] at this
  let D := regsAt d
  obtain ⟨r1, hr1, al1⟩ := looked.link
  have leaf0 : LeafInput (D 1) d := by
    rw [show D 1 = r1 from regsAt_of hr1]; exact ⟨looked.good, looked.image, looked.minstret, hr1, al1, looked.tick⟩
  have regs0 : GHolds d.σ (miss_input D) :=
    ⟨gpr_some (gpr_some_of hr1), gpr_some (gpr_some_of looked.query), gpr_some looked.a0, trivial⟩
  obtain ⟨d1, run1, p1⟩ := (miss_fast d D leaf0 regs0).run d ⟨pc0, rfl⟩
  have d9 : D 9 = R 10 := regsAt_of looked.query
  have d1_10 : gprGet d1.σ 10 = some (R 10) := by rw [← d9]; exact gholds_lookup _ p1.regs rfl
  have d1_2 : gprGet d1.σ 2 = some (R 2 + 18446744073709551552#64) :=
    (p1.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans looked.stack
  let args : GRegs := [(10, R 10), (2, R 2 + 18446744073709551552#64)]
  obtain ⟨d2, run2, p2⟩ := (call_registers_summary miss_call_shape miss_call_decode d1 (miss_call_pins p1.image)
    p1.good p1.image p1.tick p1.minstret args ⟨d1_10, d1_2, trivial⟩ (by change KeysOK [10, 2]; decide)
    (by simp [KeysAvoidRa, args, keysG]) rfl).run d1 ⟨p1.pc, rfl⟩
  have mem2 : d2.σ.mem = writeLog c.σ.mem (saveLog R) := by
    rw [p2.memory, p1.memory, wl_nil, looked.memory]
  have gp2 : gpr d2 3 = gpr c 3 :=
    (p2.toEffectPost.gpr_frame (by decide) 3 (by decide) (by decide) (by decide)).trans
      ((p1.toEffectPost.gpr_frame (by decide) 3 (by decide) (by decide) (by decide)).trans
        (looked.frame 3 (by decide) (by decide) (by decide)))
  have htif2 : d2.σ.regs.get? Register.htif_payload_writes = c.σ.regs.get? Register.htif_payload_writes :=
    (p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans
      ((p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans looked.htif)
  have leaf2 : LeafInput miss_call.link d2 :=
    ⟨p2.good, p2.image, p2.minstret, gholds_lookup _ p2.regs rfl, by decide, p2.tick⟩
  have sp2 : gprGet d2.σ 2 = some (R 2 + 18446744073709551552#64) := gholds_lookup _ p2.regs rfl
  have ready2 := ready_at_call persist ready frame big (run.trans (run1.trans run2)) leaf2 sp2 gp2 htif2 mem2
  -- the key, as `strlen` reads it
  have keyAt (i : Nat) (hi : i ≤ name.length) : (R 10 + BitVec.ofNat 64 i).toNat = (R 10).toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have keep2 (x : Nat) (hx : x < heapEnd) : d2.σ.mem[x]? = c.σ.mem[x]? := by
    rw [mem2]
    exact frameOn_writeLog _ _ _ (saveLog_inside frame big) x ⟨Or.inl (show x < (R 2).toNat - 64 by omega), trivial⟩
  have cbytes : CBytes d2.σ.mem (R 10).toNat name.length :=
    { nz := fun i hi => by
        simp only [VsaIris.MallocFast.imgM]
        rw [keep2 _ (by omega), ← keyAt i (by omega), named.bytes i hi]
        exact named.nonzero i hi
      nul := by
        simp only [VsaIris.MallocFast.imgM]
        rw [keep2 _ (by omega), ← keyAt _ (Nat.le_refl _)]
        exact named.nul
      lo := by omega
      hi := by omega
      htif := Or.inr (by omega) }
  obtain ⟨d3, run3, ⟨post3, ready3⟩⟩ := (OCaml.Vm.Boot.Startup.strlen_ready d2 H (cap + charge) _ _ (R 10) name.length ready2 cbytes
    (gholds_lookup _ p2.regs rfl)).run d2 ⟨p2.pc, rfl⟩
  -- the length's slot and the request
  let A := regsAt d3
  have a1 : A 1 = miss_call.link := regsAt_of post3.raReg
  have a2 : A 2 = R 2 + 18446744073709551552#64 := regsAt_of ready3.stack
  have a10 : A 10 = BitVec.ofNat 64 name.length := regsAt_of post3.result
  have leaf3 : LeafInput (A 1) d3 := by rw [a1]; exact post3.toLeafInput
  have regs3 : GHolds d3.σ (alloc_input A) :=
    ⟨gpr_some (gpr_some_of post3.raReg), gpr_some (gpr_some_of ready3.stack), gpr_some (gpr_some_of post3.result),
      trivial⟩
  have f64 := frame64 frame big
  have slot8 : A 2 + 8#64 = BitVec.ofNat 64 ((R 2).toNat - 64 + 8) := by
    rw [a2, f64, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ofNat_add_small]
  have w8 : WriteWindow (A 2 + 8#64) 8 := by
    rw [slot8]; exact window_of_nat (by simp only [Layout.sym_tohost]; omega) (by omega) (by omega)
  have slot8Nat : (A 2 + 8#64).toNat = (R 2).toNat - 64 + 8 := by
    rw [slot8, BitVec.toNat_ofNat]; omega
  have out3 : ImageOutside (allocLog A (alloc_loads d3.σ.mem A)) := imageOutside_of_above fun e he => by
    simp only [allocLog, List.mem_singleton] at he
    subst he
    simp only [slot8Nat, Layout.sym_bss_end]; omega
  have pc3 : PCAt 0x80021488#64 d3 := by
    have h := post3.pc; rwa [show miss_call.link = 0x80021488#64 by decide] at h
  obtain ⟨d4, run4, p4⟩ := (alloc_fast d3 A leaf3 regs3 w8 out3).run d3 ⟨pc3, rfl⟩
  have frame64' : NativeFrame (R 2) 64 := frame.resize big (by decide)
  have inside4 : LogInW [⟨nativeFrameBase (R 2) 64, (R 2).toNat⟩] (allocLog A (alloc_loads d3.σ.mem A)) := by
    simp only [allocLog, LogInW, InsideW, slot8Nat, nativeFrameBase, and_true]; omega
  have sp4 : gprGet d4.σ 2 = some (R 2 + 18446744073709551552#64) := by rw [← a2]; exact gholds_lookup _ p4.regs rfl
  have ra4 : gprGet d4.σ 1 = some miss_call.link := by rw [← a1]; exact gholds_lookup _ p4.regs rfl
  have ready4 := ready3.stack_log p4 (by decide) (by simp only [alloc_regs, keysG]; decide) (by decide) sp4 ra4
    (by decide) frame64' inside4
  let s0 := regsAt d4 8
  let args5 : GRegs := [(10, BitVec.ofNat 64 name.length + 24#64), (2, R 2 + 18446744073709551552#64), (8, s0)]
  have d4_10 : gprGet d4.σ 10 = some (BitVec.ofNat 64 name.length + 24#64) := by
    rw [← a10]; exact gholds_lookup _ p4.regs rfl
  obtain ⟨d5, run5, p5⟩ := (call_registers_summary alloc_call_shape alloc_call_decode d4 (alloc_call_pins p4.image)
    p4.good p4.image p4.tick p4.minstret args5 ⟨d4_10, sp4, gpr_some (ready4.gpr_some 8 (by decide) (by decide)), trivial⟩
    (by change KeysOK [10, 2, 8]; decide) (by simp [KeysAvoidRa, args5, keysG]) rfl).run d4 ⟨p4.pc, rfl⟩
  have ready5 : RuntimeReadyL live H (cap + charge) (R 2 + 18446744073709551552#64) alloc_call.link d5 :=
    ready4.effect p5 (by decide) (by simp [args5, keysG]) (by decide) (gholds_lookup _ p5.regs rfl)
      (gholds_lookup _ p5.regs rfl) (by decide) (fun a _ => rfl) (fun a _ => rfl) (fun a h => h)
  have frame2 : NativeFrame (R 2 + 18446744073709551552#64) depth := by
    have n := frame.nested (front := 64) (by decide)
    rwa [nativeStack, show -BitVec.ofNat 64 64 = (18446744073709551552#64 : BitVec 64) by decide] at n
  have frameS : NativeFrame (R 2 + 18446744073709551552#64) 544 := frame2.resize deep (by decide)
  have request : (BitVec.ofNat 64 name.length + 24#64).toNat = name.length + 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have pc5 : PCAt 0x8000bb2c#64 d5 := by
    have h := p5.pc; rwa [alloc_call_target] at h
  obtain ⟨d6, run6, ⟨w⟩⟩ := (stat_checkedL d5 H cap charge _ alloc_call.link s0 _ ready5 frameS
    (gholds_lookup _ p5.regs rfl) (gholds_lookup _ p5.regs rfl) (by rw [request]; exact charged)).run d5 ⟨pc5, rfl⟩
  obtain ⟨pNz, pLow, pHigh, pFresh⟩ := FreshBlock.destruct w.allocation.allocation.result.fresh
  change (vsaReg w.allocated 10).toNat ≠ 0 at pNz
  change heapStart ≤ (vsaReg w.allocated 10).toNat at pLow
  change (vsaReg w.allocated 10).toNat + (BitVec.ofNat 64 name.length + 24#64).toNat ≤ heapEnd at pHigh
  change ∀ e ∈ H, ∀ a, InExt ((vsaReg w.allocated 10).toNat, (BitVec.ofNat 64 name.length + 24#64).toNat) a →
    ¬ InExt e a at pFresh
  rw [request] at pHigh pFresh
  have ready6 := w.ready
  rw [request] at ready6
  have pReg : gprGet d6.σ 10 = some (vsaReg w.allocated 10) := gholds_lookup (n := 10) _ w.returned.regs (by rfl)
  have pAlign : (vsaReg w.allocated 10).toNat % 16 = 0 := w.allocation.allocation.result.align
  generalize hp : vsaReg w.allocated 10 = p at pLow pHigh pFresh pReg ready6 pNz pAlign
  -- registers carried from the split
  have toD5 (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1, 2, 8, 10, 11, 12, 13, 14, 15]) :
      gprGet d5.σ k = gprGet d.σ k := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    change gpr d5 k = gpr d k
    rw [p5.toEffectPost.gpr_frame (by decide) k lo hi (by simp; omega),
      p4.toEffectPost.gpr_frame (by decide) k lo hi (by simp; omega),
      post3.registers k lo hi (by simp; omega),
      p2.toEffectPost.gpr_frame (by decide) k lo hi (by simp; omega),
      p1.toEffectPost.gpr_frame (by decide) k lo hi (by simp; omega)]
  -- the frame across the allocation
  have callerFrame := w.caller_frame frameS
  have sp2Nat : (R 2 + 18446744073709551552#64).toNat = (R 2).toNat - 64 := by rw [f64, BitVec.toNat_ofNat]; omega
  have mem5 : d5.σ.mem = writeLog d3.σ.mem (allocLog A (alloc_loads d3.σ.mem A)) := by rw [p5.memory, p4.memory]
  have eqv3 (x : Nat) : (d3.σ.mem[x]?).getD 0 = (d2.σ.mem[x]?).getD 0 := by
    have := post3.memory x
    simpa only [Std.ExtHashMap.get?_eq_getElem?] using this
  have inside8 : LogInW [⟨(R 2).toNat - 64 + 8, (R 2).toNat - 64 + 16⟩] (allocLog A (alloc_loads d3.σ.mem A)) := by
    simp only [allocLog, LogInW, InsideW, slot8Nat, and_true]; omega
  have to2 (x : Nat) (out : x < (R 2).toNat - 64 + 8 ∨ (R 2).toNat - 64 + 16 ≤ x) :
      (d5.σ.mem[x]?).getD 0 = (d2.σ.mem[x]?).getD 0 := by
    rw [mem5, frameOn_writeLog _ _ _ inside8 x ⟨out, trivial⟩, eqv3]
  have length6 : bytesT d6.σ.mem ((R 2).toNat - 64 + 8) 8 = BitVec.ofNat 64 name.length := by
    rw [word_observed (m := d5.σ.mem) _ fun i hi => callerFrame.byte _ (by rw [sp2Nat]; omega), mem5, ← slot8Nat,
      Gc.word_writeLog_at d3.σ.mem (allocLog A (alloc_loads d3.σ.mem A)) 0 (A 2 + 8#64).toNat (A 10)
        (by simp [allocLog]) (by simp [allocLog, OutLRange]), a10]
  have slots6 : ∀ k, 16 ≤ k → k < 64 → (d6.σ.mem[(R 2).toNat - 64 + k]?).getD 0 =
      ((writeLog c.σ.mem (saveLog R))[(R 2).toNat - 64 + k]?).getD 0 := fun k lo hi => by
    rw [callerFrame.byte _ (by rw [sp2Nat]; omega), to2 _ (Or.inr (by omega)), mem2]
  have kept6 : ∀ x, ¬ vsaFoot H x → (x < (R 2).toNat - (64 + depth) ∨ (R 2).toNat ≤ x) →
      (d6.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    intro x foot win
    have apart : x < nativeFrameBase (R 2 + 18446744073709551552#64) 544 ∨
        (R 2 + 18446744073709551552#64).toNat ≤ x := by
      unfold nativeFrameBase; rw [sp2Nat]; rcases win with h | h <;> omega
    have out : x < (R 2).toNat - 64 ∨ (R 2).toNat ≤ x := by rcases win with h | h <;> omega
    rw [w.kept_byte frameS apart foot, to2 _ (by rcases out with h | h <;> omega), mem2,
      frameOn_writeLog _ _ _ (saveLog_inside frame big) x ⟨out, trivial⟩]
  have k9 : gprGet d6.σ 9 = some (R 10) :=
    w.keep_saved (by decide) ((toD5 9 (by decide) (by decide) (by decide)).trans looked.query)
  have k18 := w.keep_saved (k := 18) (by decide) ((toD5 18 (by decide) (by decide) (by decide)).trans looked.bucket)
  have k19 := w.keep_saved (k := 19) (by decide) ((toD5 19 (by decide) (by decide) (by decide)).trans looked.table)
  have k20 := w.keep_upper (k := 20) (by decide) (by decide)
    ((toD5 20 (by decide) (by decide) (by decide)).trans looked.value)
  have out6 : Vsa.Machine.output d6.σ = Vsa.Machine.output c.σ := by
    have a : Vsa.Machine.output d6.σ = Vsa.Machine.output w.allocated.σ := by
      simp only [Vsa.Machine.output, w.returned.output]
    have b : Vsa.Machine.output w.allocated.σ = Vsa.Machine.output w.allocation.atMalloc.σ :=
      w.allocation.allocation.output
    have c' : Vsa.Machine.output w.allocation.atMalloc.σ = Vsa.Machine.output d5.σ := by
      simp only [Vsa.Machine.output, w.allocation.call.output, w.allocation.setup.output]
    have e : Vsa.Machine.output d5.σ = Vsa.Machine.output d3.σ := by
      simp only [Vsa.Machine.output, p5.output, p4.output]
    have g : Vsa.Machine.output d2.σ = Vsa.Machine.output c.σ := by
      simp only [Vsa.Machine.output, p2.output, p1.output, looked.output]
    rw [a, b, c', e, post3.output, g]
  refine ⟨d6, p, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))),
    { ready := ready6, pc := w.returned.pc, result := pReg, nonzero := ?_, low := pLow, high := pHigh, align := pAlign,
      fresh := pFresh, key := k9, bucket := k18, table := k19, value := k20, length := length6, slots := slots6,
      kept := kept6, output := out6 }⟩
  intro z; apply pNz; rw [z]; rfl

/-! ### The new-node path: the key, the links and the root -/

/-- A log at or above `.rodata`'s end misses the image. -/
theorem imageOutside_of_rodata {log : List WEntry} (above : ∀ e ∈ log, 0x80061fb0 ≤ e.1) : ImageOutside log := by
  have t : Image.textBase + Image.textSize ≤ 0x80061fb0 := by decide
  have r : Image.rodataBase + Image.rodataSize ≤ 0x80061fb0 := by decide
  refine ⟨Gc.outLRange_of_forall fun e he => .inl ?_, Gc.outLRange_of_forall fun e he => .inl ?_⟩
  · have := above e he; omega
  · have := above e he; omega

/-- The bucket word of index `k`. -/
def BucketWord (k a : Nat) : Prop :=
  Layout.sym_named_value_table + 8 * k ≤ a ∧ a < Layout.sym_named_value_table + 8 * k + 8

theorem vsaFoot_cons {H : List (Nat × Nat)} {e : Nat × Nat} {a : Nat} (h : vsaFoot (e :: H) a) : vsaFoot H a := by
  rcases h with g | ⟨lo, hi, out⟩
  · exact Or.inl g
  · exact Or.inr ⟨lo, hi, fun x hx => out x (List.mem_cons_of_mem _ hx)⟩

/-- A byte of a block fresh for `H` is the allocator's in `H`. -/
theorem foot_of_fresh {H : List (Nat × Nat)} {p n a : Nat}
    (fresh : ∀ e ∈ H, ∀ y, InExt (p, n) y → ¬ InExt e y) (low : heapStart ≤ p) (high : p + n ≤ heapEnd)
    (lo : p ≤ a) (hi : a < p + n) : vsaFoot H a :=
  Or.inr ⟨by omega, by omega, fun e he i => fresh e he a ⟨lo, hi⟩ i⟩

/-- The bucket array is none of the allocator's bytes. -/
theorem bucket_not_foot {H : List (Nat × Nat)} {a : Nat}
    (h : Layout.sym_named_value_table ≤ a ∧ a < Layout.sym_named_value_table + 104) : ¬ vsaFoot H a := by
  rintro (g | ⟨l, _, _⟩)
  · unfold allocGlobal InRange at g; simp only [Layout.sym_named_value_table] at h; omega
  · simp only [Layout.sym_named_value_table] at h; unfold heapStart at l; omega

/-- **The new node linked and filed**, at the join `0x800214d0`: the bucket
head is the node, whose value word is `v`, next word the old head, key the
query's bytes; the frame's saves and every byte outside the roots' statics,
the allocator's footprint and the bucket word are kept. -/
structure MissLinked (live : Nat → Prop) (G : Nat → Prop) (Post : List (Nat × Nat) → Mem → Prop) (depth : Nat)
    (H : List (Nat × Nat)) (R : Nat → BitVec 64) (name : List (BitVec 8)) (p : BitVec 64) (c d : Config) : Prop where
  ready : ∃ H' cap', ReadyAfter live G Post ((p.toNat, name.length + 24) :: H) H' cap'
    (R 2 + 18446744073709551552#64) link_call.link d
  pc : PCAt link_call.link d
  slots : ∀ k, 16 ≤ k → k < 64 → (d.σ.mem[(R 2).toNat - 64 + k]?).getD 0 =
    ((writeLog c.σ.mem (saveLog R))[(R 2).toNat - 64 + k]?).getD 0
  head : bytesT d.σ.mem (Layout.sym_named_value_table + 8 * ((NamedValue.hashBytes name).toNat % 13)) 8 = p
  valueWord : bytesT d.σ.mem p.toNat 8 = R 11
  nextWord : bytesT d.σ.mem (p.toNat + 8) 8 =
    bytesT c.σ.mem (Layout.sym_named_value_table + 8 * ((NamedValue.hashBytes name).toNat % 13)) 8
  keyBytes : ∀ k, k < name.length + 1 →
    (d.σ.mem[p.toNat + 16 + k]?).getD 0 = (c.σ.mem[(R 10).toNat + k]?).getD 0
  kept : ∀ x, ¬ G x → ¬ vsaFoot H x → ¬ BucketWord ((NamedValue.hashBytes name).toNat % 13) x →
    (x < (R 2).toNat - (64 + depth) ∨ (R 2).toNat ≤ x) → (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0
  output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ

/-- **The new-node path from its block to the join**: `memcpy(nv->name, name,
len + 1)`, the three link stores, `caml_register_generational_global_root(&nv->val)`. -/
theorem miss_link {live : Nat → Prop} [LibraryLive live] {depth : Nat}
    {Shape : Mem → Nat → List (BitVec 64) → Prop} {foot : Mem → Nat → List (BitVec 64) → Nat → Prop}
    {Table : Mem → (Nat → Nat) → Prop} {tfoot : Mem → Nat → Prop}
    (ops : OCaml.Vm.Gc.Skiplist.Ops Shape foot) (tf : OCaml.Vm.Gc.PageTableFrame Table tfoot)
    (roots : GenRoots.RootCallsG Shape foot Table tfoot) {H : List (Nat × Nat)} {cap : Nat} {R : Nat → BitVec 64}
    {name : List (BitVec 8)} {p : BitVec 64} {S : GenRoots.RootsState} {c d : Config}
    (frame : NativeFrame (R 2) (64 + depth)) (deepR : 32 + OCaml.Vm.Gc.Skiplist.opStack ≤ depth)
    (M : MissAllocated live depth H cap R name p c d)
    (keyLow : heapStart ≤ (R 10).toNat) (keyHigh : (R 10).toNat + name.length + 8 ≤ heapEnd)
    (keyBlock : ∃ e ∈ H, heapStart ≤ e.1 ∧ e.1 ≤ (R 10).toNat ∧ (R 10).toNat + name.length + 1 ≤ e.1 + e.2)
    (I : GenRoots.RootsAt Shape foot Table tfoot H S c.σ.mem)
    (listsLive : ∀ a, OCaml.Vm.Gc.Skiplist.ListsFoot Shape foot c.σ.mem a → ¬ vsaFoot H a)
    (bucketG : ∀ a, Layout.sym_named_value_table ≤ a → a < Layout.sym_named_value_table + 104 →
      ¬ RootsG Shape foot c.σ.mem a ∧ ¬ tfoot c.σ.mem a ∧ ¬ GenRoots.StateWord S a) :
    ∃ e, Steps d e ∧ MissLinked live (RootsG Shape foot c.σ.mem)
      (fun H' m => ∃ ys' os', GenRoots.RootsAt Shape foot Table tfoot H'
        { S with ys := ys', os := os', slots := p :: S.slots } m)
      depth H R name p c e := by
  have big : 64 ≤ 64 + depth := Nat.le_add_right _ _
  have lower := frame.lower
  have upper := frame.upper
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have hT : Layout.sym_stack_top = 0x88000000 := rfl
  have f64 := frame64 frame big
  have sp2Nat : (R 2 + 18446744073709551552#64).toNat = (R 2).toNat - 64 := by rw [f64, BitVec.toNat_ofNat]; omega
  have pLow := M.low
  have pHigh := M.high
  have pAl := M.align
  have kLt : (NamedValue.hashBytes name).toNat % 13 < 13 := Nat.mod_lt _ (by decide)
  generalize hk : (NamedValue.hashBytes name).toNat % 13 = k at kLt ⊢
  have mBucket := M.bucket
  rw [hk] at mBucket
  have tbl : Layout.sym_named_value_table = 0x8006bff0 := rfl
  have frame2 : NativeFrame (R 2 + 18446744073709551552#64) depth := by
    have n := frame.nested (front := 64) (by decide)
    rwa [nativeStack, show -BitVec.ofNat 64 64 = (18446744073709551552#64 : BitVec 64) by decide] at n
  -- the copy block
  let C := regsAt d
  have c1 : C 1 = alloc_call.link := regsAt_of M.ready.raReg
  have c2 : C 2 = R 2 + 18446744073709551552#64 := regsAt_of M.ready.stack
  have c9 : C 9 = R 10 := regsAt_of M.key
  have c10 : C 10 = p := regsAt_of M.result
  have c18 : C 18 = BitVec.ofNat 64 k := regsAt_of mBucket
  have leafC : LeafInput (C 1) d := by rw [c1]; exact M.ready.toLeafInput
  have regsC : GHolds d.σ (copy_input C) :=
    ⟨gpr_some (gpr_some_of M.ready.raReg), gpr_some (gpr_some_of M.ready.stack), gpr_some (gpr_some_of M.key),
      gpr_some (gpr_some_of M.result), gpr_some (gpr_some_of mBucket), trivial⟩
  have slot8 : C 2 + 8#64 = BitVec.ofNat 64 ((R 2).toNat - 64 + 8) := by
    rw [c2, f64, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ofNat_add_small]
  have w8 : ReadWindow (C 2 + 8#64) 8 := by
    rw [slot8]; exact (window_of_nat (by simp only [Layout.sym_tohost]; omega) (by omega)
      (by have := frame.aligned; omega)).read
  have pcC : PCAt 0x80021498#64 d := by have h := M.pc; rwa [show alloc_call.link = 0x80021498#64 by decide] at h
  obtain ⟨d7, run7, p7⟩ := (copy_fast d C leafC regsC w8).run d ⟨pcC, rfl⟩
  have loaded : bytesVal .ld ((copy_loads d.σ.mem C).getD 0 []) = BitVec.ofNat 64 name.length := by
    simp only [copy_loads, List.getD_cons_zero]
    rw [read8_value, slot8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact M.length
  have r7 (n : Nat) (v : BitVec 64) (h : lookupG n (copy_regs C (copy_loads d.σ.mem C)) = some v) :
      gprGet d7.σ n = some v := gholds_lookup _ p7.regs h
  have d7_10 : gprGet d7.σ 10 = some (p + 16#64) := by rw [← c10]; exact r7 10 _ rfl
  have d7_11 : gprGet d7.σ 11 = some (R 10) := by rw [← c9]; exact r7 11 _ rfl
  have d7_12 : gprGet d7.σ 12 = some (BitVec.ofNat 64 (name.length + 1)) := by
    rw [r7 12 _ rfl, loaded, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_add_small]
  have d7_2 : gprGet d7.σ 2 = some (R 2 + 18446744073709551552#64) := by rw [← c2]; exact r7 2 _ rfl
  have d7_1 : gprGet d7.σ 1 = some alloc_call.link := by rw [← c1]; exact r7 1 _ rfl
  have d7_8 : gprGet d7.σ 8 = some p := by rw [← c10]; exact r7 8 _ rfl
  have d7_18 : gprGet d7.σ 18 = some (BitVec.ofNat 64 k <<< 3) := by rw [← c18]; exact r7 18 _ rfl
  have d7_19 : gprGet d7.σ 19 = some tableReg :=
    (p7.toEffectPost.gpr_frame (by decide) 19 (by decide) (by decide) (by decide)).trans M.table
  have d7_20 : gprGet d7.σ 20 = some (R 11) :=
    (p7.toEffectPost.gpr_frame (by decide) 20 (by decide) (by decide) (by decide)).trans M.value
  have ready7 := M.ready.effect p7 (by decide) (by simp only [copy_regs, keysG]; decide) (by decide) d7_2 d7_1
    (by decide) (fun a _ => by rw [wl_nil]) (fun a _ => by rw [wl_nil]) (fun a h => by rw [wl_nil]; exact h)
  -- the call to `memcpy`
  let args8 : GRegs := [(10, p + 16#64), (11, R 10), (12, BitVec.ofNat 64 (name.length + 1)),
    (2, R 2 + 18446744073709551552#64), (8, p), (18, BitVec.ofNat 64 k <<< 3), (19, tableReg), (20, R 11)]
  obtain ⟨d8, run8, p8⟩ := (call_registers_summary copy_call_shape copy_call_decode d7 (copy_call_pins p7.image)
    p7.good p7.image p7.tick p7.minstret args8
    ⟨d7_10, d7_11, d7_12, d7_2, d7_8, d7_18, d7_19, d7_20, trivial⟩ (by change KeysOK [10, 11, 12, 2, 8, 18, 19, 20]; decide)
    (by simp [KeysAvoidRa, args8, keysG]) rfl).run d7 ⟨p7.pc, rfl⟩
  have ready8 := ready7.effect p8 (by decide) (by simp [args8, keysG]) (by decide) (gholds_lookup _ p8.regs rfl)
    (gholds_lookup _ p8.regs rfl) (by decide) (fun a _ => rfl) (fun a _ => rfl) (fun a h => h)
  have pc8 : PCAt 0x80042848#64 d8 := by have h := p8.pc; rwa [copy_call_target] at h
  have p16 : (p + 16#64).toNat = p.toNat + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have member : (p.toNat, name.length + 24) ∈ (p.toNat, name.length + 24) :: H := List.mem_cons_self
  obtain ⟨e0, he0, e0Low, e0lo, e0hi⟩ := keyBlock
  obtain ⟨d9, run9, D9⟩ := (memcpy_window d8 _ cap _ copy_call.link (p + 16#64) (R 10) (name.length + 1) ready8
    (by rw [p16]; omega) (by rw [p16]; omega)
    (fun a foot => by
      rw [p16]; rcases allocator_payload_outside member pLow foot with h | h <;> omega)
    ⟨gholds_lookup _ p8.regs rfl, gholds_lookup _ p8.regs rfl, gholds_lookup _ p8.regs rfl, trivial⟩
    (fun i hi inside => by
      have ins : p.toNat + 16 ≤ (R 10).toNat + i ∧ (R 10).toNat + i < p.toNat + 16 + (name.length + 1) := by
        rw [p16] at inside; exact inside
      exact M.fresh e0 he0 ((R 10).toNat + i) ⟨by omega, by dsimp only; omega⟩ ⟨by omega, by omega⟩)
    (by omega) (by omega) (Or.inr (by simp only [Layout.sym_tohost]; omega))).run d8 ⟨pc8, rfl⟩
  -- the link block
  have keep9 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ VsaIris.Memcpy.mRegs) (v : BitVec 64)
      (h : gprGet d8.σ n = some v) : gprGet d9.σ n = some v := (D9.registers n lo hi out).trans h
  have d9_8 : gprGet d9.σ 8 = some p := keep9 8 (by decide) (by decide) (by decide) _ (gholds_lookup _ p8.regs rfl)
  have d9_18 : gprGet d9.σ 18 = some (BitVec.ofNat 64 k <<< 3) :=
    keep9 18 (by decide) (by decide) (by decide) _ (gholds_lookup _ p8.regs rfl)
  have d9_19 : gprGet d9.σ 19 = some tableReg := keep9 19 (by decide) (by decide) (by decide) _ (gholds_lookup _ p8.regs rfl)
  have d9_20 : gprGet d9.σ 20 = some (R 11) := keep9 20 (by decide) (by decide) (by decide) _ (gholds_lookup _ p8.regs rfl)
  let K := regsAt d9
  have k1 : K 1 = copy_call.link := regsAt_of D9.ready.raReg
  have k8 : K 8 = p := regsAt_of d9_8
  have k18 : K 18 = BitVec.ofNat 64 k <<< 3 := regsAt_of d9_18
  have k19 : K 19 = tableReg := regsAt_of d9_19
  have k20 : K 20 = R 11 := regsAt_of d9_20
  have leafK : LeafInput (K 1) d9 := by rw [k1]; exact D9.ready.toLeafInput
  have regsK : GHolds d9.σ (link_input K) :=
    ⟨gpr_some (gpr_some_of D9.ready.raReg), gpr_some (gpr_some_of d9_8), gpr_some (gpr_some_of d9_18),
      gpr_some (gpr_some_of d9_19), gpr_some (gpr_some_of d9_20), trivial⟩
  have shift : BitVec.ofNat 64 k <<< 3 = BitVec.ofNat 64 (8 * k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have bucketEq : K 19 + K 18 = BitVec.ofNat 64 (Layout.sym_named_value_table + 8 * k) := by
    rw [k19, k18, shift, show tableReg = BitVec.ofNat 64 Layout.sym_named_value_table from rfl, ofNat_add_small]
  have bucketNat : (K 19 + K 18).toNat = Layout.sym_named_value_table + 8 * k := by
    rw [bucketEq, BitVec.toNat_ofNat, tbl]; omega
  have pEq : K 8 = BitVec.ofNat 64 p.toNat := by rw [k8]; simp
  have p8Eq : K 8 + 8#64 = BitVec.ofNat 64 (p.toNat + 8) := by
    rw [pEq, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ofNat_add_small]
  have p8Nat : (K 8 + 8#64).toNat = p.toNat + 8 := by rw [p8Eq, BitVec.toNat_ofNat]; omega
  have p8Nat' : (p + 8#64).toNat = p.toNat + 8 := by
    have h := p8Nat; rw [k8] at h; exact h
  have bucketW : WriteWindow (K 19 + K 18) 8 := by
    rw [bucketEq]; exact window_of_nat (by simp only [Layout.sym_tohost, tbl]; omega) (by rw [tbl]; omega)
      (by rw [tbl]; omega)
  have outK : ImageOutside (linkLog K (link_loads d9.σ.mem K)) := imageOutside_of_rodata fun e he => by
    simp only [linkLog, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · simp only [k8]; omega
    · simp only [p8Nat]; omega
    · simp only [bucketNat, tbl]; omega
  have pcK : PCAt 0x800214b4#64 d9 := by have h := D9.pc; rwa [show copy_call.link = 0x800214b4#64 by decide] at h
  obtain ⟨d10, run10, p10⟩ := (link_fast d9 K leafK regsK bucketW.read
    (by rw [pEq]; exact window_of_nat (by simp only [Layout.sym_tohost]; omega) (by omega) (by omega))
    (by rw [p8Eq]; exact window_of_nat (by simp only [Layout.sym_tohost]; omega) (by omega) (by omega))
    bucketW outK).run d9 ⟨pcK, rfl⟩
  have r10 (n : Nat) (v : BitVec 64) (h : lookupG n (link_regs K (link_loads d9.σ.mem K)) = some v) :
      gprGet d10.σ n = some v := gholds_lookup _ p10.regs h
  -- the link stores keep readiness: they lie in the node's block and the bucket word
  have insideL : LogInW [⟨p.toNat, p.toNat + 16⟩, ⟨Layout.sym_named_value_table + 8 * k,
      Layout.sym_named_value_table + 8 * k + 8⟩] (linkLog K (link_loads d9.σ.mem K)) := by
    simp only [linkLog, LogInW, InsideW, bucketNat, k8, p8Nat', and_true]; omega
  have ready10 : RuntimeReadyL live ((p.toNat, name.length + 24) :: H) cap (R 2 + 18446744073709551552#64)
      copy_call.link d10 := by
    refine D9.ready.of_kept ⟨p10.good, p10.image, p10.minstret, by rw [← k1]; exact r10 1 _ rfl, by decide, p10.tick⟩
      ((p10.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans D9.ready.stack)
      (GprsKept.of_written (W := [10, 15, 19]) (by decide)
        (fun n hn => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl | rfl
          · exact gpr_some_of (r10 10 _ rfl)
          · exact gpr_some_of (r10 15 _ rfl)
          · exact gpr_some_of (r10 19 _ rfl))
        (fun n lo hi out => p10.gpr_frame (by decide) n lo hi out))
      (p10.frame _ (fun n _ => gprReg_ne_htif n) (by decide)) p10.memory insideL ?_ ?_ ?_ ?_
    · intro pin hp
      have high := (allocator_sources pin hp).geometry.high
      have src := allocator_sources pin hp
      unfold AllocatorByteSource at src
      have notBucket : pin.1 < Layout.sym_named_value_table + 8 * k ∨
          Layout.sym_named_value_table + 8 * k + 8 ≤ pin.1 := by
        split at src <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr, tbl] at * <;> omega
      exact ⟨Or.inl (show pin.1 < p.toNat by omega), notBucket, trivial⟩
    · simp only [OutWRange, Layout.sym_Caml_state, tbl, and_true]; omega
    · simp only [OutWRange, Layout.sym_pool, tbl, and_true]; omega
    · intro a foot
      refine ⟨?_, ?_, trivial⟩
      · rcases allocator_payload_outside member pLow foot with h | h
        · exact Or.inl h
        · exact Or.inr (show p.toNat + 16 ≤ a by omega)
      · rcases Nat.lt_or_ge a (Layout.sym_named_value_table + 8 * k) with h | h
        · exact Or.inl h
        · rcases Nat.lt_or_ge a (Layout.sym_named_value_table + 8 * k + 8) with h' | h'
          · exact absurd foot (bucket_not_foot (by rw [tbl] at h h' ⊢; omega))
          · exact Or.inr h'
  -- the root call
  let args11 : GRegs := [(10, p), (2, R 2 + 18446744073709551552#64)]
  have d10_10 : gprGet d10.σ 10 = some p := by rw [← k8]; exact r10 10 _ rfl
  have d10_2 : gprGet d10.σ 2 = some (R 2 + 18446744073709551552#64) :=
    (p10.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans D9.ready.stack
  obtain ⟨d11, run11, p11⟩ := (call_registers_summary link_call_shape link_call_decode d10 (link_call_pins p10.image)
    p10.good p10.image p10.tick p10.minstret args11 ⟨d10_10, d10_2, trivial⟩ (by change KeysOK [10, 2]; decide)
    (by simp [KeysAvoidRa, args11, keysG]) rfl).run d10 ⟨p10.pc, rfl⟩
  have ready11 := ready10.effect p11 (by decide) (by simp [args11, keysG]) (by decide) (gholds_lookup _ p11.regs rfl)
    (gholds_lookup _ p11.regs rfl) (by decide) (fun a _ => rfl) (fun a _ => rfl) (fun a h => h)
  have pc11 : PCAt 0x8000ca04#64 d11 := by have h := p11.pc; rwa [link_call_target] at h
  -- the memory at the root call
  have mem11 : d11.σ.mem = writeLog d9.σ.mem (linkLog K (link_loads d9.σ.mem K)) := by
    rw [p11.memory, p10.memory]
  have linkOut (x : Nat) (nb : x < p.toNat ∨ p.toNat + 16 ≤ x)
      (nw : x < Layout.sym_named_value_table + 8 * k ∨ Layout.sym_named_value_table + 8 * k + 8 ≤ x) :
      (writeLog d9.σ.mem (linkLog K (link_loads d9.σ.mem K)))[x]? = d9.σ.mem[x]? :=
    frameOn_writeLog _ _ _ insideL x ⟨nb, nw, trivial⟩
  have toD (x : Nat) (out : ¬ InExt ((p + 16#64).toNat, name.length + 1) x) :
      (d9.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0 := by
    rw [D9.kept x out, p8.memory, p7.memory, wl_nil]
  have blockFoot (x : Nat) (lo : p.toNat ≤ x) (hi : x < p.toNat + (name.length + 24)) : vsaFoot H x :=
    foot_of_fresh M.fresh pLow pHigh lo hi
  -- what the root call may own: the bucket word and the node's block
  let own : Nat → Prop := fun x => BucketWord k x ∨ InExt (p.toNat, name.length + 24) x
  have keep11 (x : Nat) (hx : x < heapEnd) (nF : ¬ vsaFoot H x) (nOwn : ¬ own x) :
      (d11.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    have nb : x < p.toNat ∨ p.toNat + (name.length + 24) ≤ x := by
      rcases Nat.lt_or_ge x p.toNat with h | h
      · exact Or.inl h
      · rcases Nat.lt_or_ge x (p.toNat + (name.length + 24)) with h' | h'
        · exact absurd (Or.inr ⟨h, h'⟩) nOwn
        · exact Or.inr h'
    have nw : x < Layout.sym_named_value_table + 8 * k ∨ Layout.sym_named_value_table + 8 * k + 8 ≤ x := by
      rcases Nat.lt_or_ge x (Layout.sym_named_value_table + 8 * k) with h | h
      · exact Or.inl h
      · rcases Nat.lt_or_ge x (Layout.sym_named_value_table + 8 * k + 8) with h' | h'
        · exact absurd (Or.inl ⟨h, h'⟩) nOwn
        · exact Or.inr h'
    rw [mem11, linkOut _ (by omega) nw, toD _ (fun h => by rw [p16] at h; unfold InExt at h; dsimp only at h; omega)]
    exact M.kept x nF (Or.inl (by omega))
  have listAgree : ∀ x, OCaml.Vm.Gc.Skiplist.ListsFoot Shape foot c.σ.mem x →
      (d11.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := fun x l => by
    obtain ⟨_, _, _, sh, f⟩ := id l
    refine keep11 x (ops.low _ _ _ sh x f) (listsLive x l) ?_
    rintro (b | ⟨lo, hi⟩)
    · exact (bucketG x (by unfold BucketWord at b; rw [tbl] at *; omega)
        (by unfold BucketWord at b; rw [tbl] at *; omega)).1 (Or.inl l)
    · exact listsLive x l (blockFoot x lo (by dsimp only at hi; omega))
  have lists11 : ∀ x, OCaml.Vm.Gc.Skiplist.ListsFoot Shape foot d11.σ.mem x ↔
      OCaml.Vm.Gc.Skiplist.ListsFoot Shape foot c.σ.mem x := I.roots.listsFoot_keep ops listAgree
  have cr : GenRoots.Carry Shape foot H ((p.toNat, name.length + 24) :: H) own c.σ.mem d11.σ.mem :=
    { heap := fun x f => Or.inl (vsaFoot_cons f)
      feet := fun x l => Or.inl ((lists11 x).1 l)
      kept := fun x hx o n => keep11 x hx o.heap n }
  have ownApart : ∀ x, own x → ¬ tfoot c.σ.mem x ∧ ¬ GenRoots.StateWord S x ∧ ¬ GenRoots.InSlots S.slots x := by
    rintro x (b | ⟨lo, hi⟩)
    · unfold BucketWord at b
      obtain ⟨-, nt, ns⟩ := bucketG x (by rw [tbl] at *; omega) (by rw [tbl] at *; omega)
      refine ⟨nt, ns, fun ⟨r, hr, iw⟩ => ?_⟩
      have := I.slotLow r hr; unfold GenRoots.InWord at iw; rw [tbl] at *; omega
    · have v := blockFoot x lo (by dsimp only at hi; omega)
      exact ⟨fun t => (I.env.tableOff x t).1.heap v, fun sw => (I.env.stateOff x sw).1.heap v,
        fun ⟨r, hr, iw⟩ => (I.slotOff r hr x iw).heap v⟩
  have I11 := I.keep tf cr ownApart (I.roots.keep ops fun _ _ list sh x f => listAgree x ⟨_, _, list, sh, f⟩)
  -- the node's value word is a fresh slot
  have pWord (x : Nat) (iw : GenRoots.InWord p.toNat x) : vsaFoot H x :=
    blockFoot x iw.1 (by unfold GenRoots.InWord at iw; omega)
  have tf11 : ∀ x, tfoot d11.σ.mem x ↔ tfoot c.σ.mem x :=
    (tf.frame c.σ.mem d11.σ.mem S.cls I.env.table fun x t => keep11 x (tf.low _ _ I.env.table x t)
      (I.env.tableOff x t).1.heap fun o => (ownApart x o).1 t).2
  have fresh : GenRoots.Fresh Shape foot tfoot ((p.toNat, name.length + 24) :: H) S d11.σ.mem p :=
    { notSlot := fun hr => (I.slotOff p hr p.toNat ⟨Nat.le_refl _, by omega⟩).heap
        (pWord _ ⟨Nat.le_refl _, by omega⟩)
      notGlobal := fun hr => (I.globalOff p hr p.toNat ⟨Nat.le_refl _, by omega⟩).heap
        (pWord _ ⟨Nat.le_refl _, by omega⟩)
      low := pLow
      high := by omega
      aligned := by omega
      off := fun x iw => ⟨fun l => listsLive x ((lists11 x).1 l) (pWord x iw),
        fun f => by
          rcases f with g | ⟨-, -, out⟩
          · rcases VsaIris.VsaHeap.allocGlobal_off_arena x g with l | l <;>
              (unfold GenRoots.InWord at iw; omega)
          · exact out _ member ⟨iw.1, by unfold GenRoots.InWord at iw; dsimp only; omega⟩,
        Or.inr (by unfold GenRoots.InWord at iw; unfold OCaml.Vm.Gc.Skiplist.randomSeed; omega)⟩
      apart := fun r hr => by
        rcases Nat.lt_or_ge (r.toNat + 8) (p.toNat + 1) with h | h
        · exact Or.inr (by omega)
        · rcases Nat.lt_or_ge (p.toNat + 8) (r.toNat + 1) with h' | h'
          · exact Or.inl (by omega)
          · exfalso
            rcases Nat.le_total r.toNat p.toNat with o | o
            · exact (I.slotOff r hr p.toNat ⟨o, by omega⟩).heap (pWord _ ⟨Nat.le_refl _, by omega⟩)
            · exact (I.slotOff r hr r.toNat ⟨Nat.le_refl _, by omega⟩).heap (pWord _ ⟨o, by omega⟩)
      notTable := fun x iw t => (I.env.tableOff x ((tf11 x).1 t)).1.heap (pWord x iw)
      notState := fun x iw sw => (I.env.stateOff x sw).1.heap (pWord x iw) }
  have entry : GenRoots.RegisterEntry ((p.toNat, name.length + 24) :: H) cap (R 2 + 18446744073709551552#64)
      link_call.link p d11 :=
    { leaf := ready11.toLeafInput
      slot := gholds_lookup _ p11.regs rfl
      stack := ready11.stack
      heap := ready11.heap
      frame := frame2.resize (by unfold OCaml.Vm.Gc.Skiplist.opStack at deepR ⊢; omega) (by decide) }
  obtain ⟨d12, run12, rp, H'', cap'', ys', os', next⟩ :=
    (roots.register d11 _ cap S _ link_call.link p I11 fresh entry).run d11 ⟨pc11, rfl⟩
  -- the memory across the root call
  have sp'Low := frame2.lower
  have through12 (x : Nat) (nG : ¬ RootsG Shape foot c.σ.mem x) (nF : ¬ vsaFoot ((p.toNat, name.length + 24) :: H) x)
      (win : x < (R 2).toNat - 64 - depth ∨ (R 2).toNat - 64 ≤ x) :
      (d12.σ.mem[x]?).getD 0 = ((writeLog d9.σ.mem (linkLog K (link_loads d9.σ.mem K)))[x]?).getD 0 := by
    have off : GenRoots.Off Shape foot ((p.toNat, name.length + 24) :: H) d11.σ.mem x :=
      ⟨fun l => nG (Or.inl ((lists11 x).1 l)), nF, by
        rcases Nat.lt_or_ge x OCaml.Vm.Gc.Skiplist.randomSeed with h | h
        · exact Or.inl h
        · exact Or.inr (Nat.le_of_not_lt fun l => nG (Or.inr ⟨h, l⟩))⟩
    rw [next.kept x off (fun f => f) (by
        rw [sp2Nat]; unfold OCaml.Vm.Gc.Skiplist.opStack at deepR ⊢; rcases win with h | h <;> omega), mem11]
  have blockNotG (x : Nat) (lo : p.toNat ≤ x) (hi : x < p.toNat + (name.length + 24)) :
      ¬ RootsG Shape foot c.σ.mem x := by
    rintro (l | ⟨-, l⟩)
    · exact listsLive x l (blockFoot x lo hi)
    · unfold OCaml.Vm.Gc.Skiplist.randomSeed at l; omega
  have highNotG (x : Nat) (hx : heapEnd ≤ x) : ¬ RootsG Shape foot c.σ.mem x := by
    rintro (⟨_, _, _, sh, f⟩ | ⟨-, l⟩)
    · have := ops.low _ _ _ sh x f; omega
    · unfold OCaml.Vm.Gc.Skiplist.randomSeed at l; omega
  have blockLive (x : Nat) (lo : p.toNat ≤ x) (hi : x < p.toNat + (name.length + 24)) :
      ¬ vsaFoot ((p.toNat, name.length + 24) :: H) x := fun foot => by
    rcases allocator_payload_outside member pLow foot with h | h <;> omega
  have entries := Gc.word_writeLog_at d9.σ.mem (linkLog K (link_loads d9.σ.mem K))
  refine ⟨d12, run7.trans (run8.trans (run9.trans (run10.trans (run11.trans run12)))), ?_⟩
  refine { ready := ⟨H'', cap'', rp.ready ready11 run12 (by decide) next.heap,
             fun x v => (next.heapIn x v).imp id fun l => Or.inl ((lists11 x).1 l), ys', os', next.roots⟩,
           pc := rp.pc, slots := ?_, head := ?_, valueWord := ?_, nextWord := ?_, keyBytes := ?_, kept := ?_,
           output := ?_ }
  · intro j lo hi
    rw [through12 _ (highNotG _ (by omega)) (not_foot_high (by omega)) (Or.inr (by omega)),
      linkOut _ (Or.inr (by omega)) (Or.inr (by rw [tbl]; omega)),
      toD _ (fun i => by rw [p16] at i; unfold InExt at i; dsimp only at i; omega)]
    exact M.slots j lo hi
  · rw [hk, word_observed (m := writeLog d9.σ.mem (linkLog K (link_loads d9.σ.mem K))) _ fun i hi => through12 _
      (bucketG _ (by omega) (by omega)).1 (bucket_not_foot (by omega)) (Or.inl (by rw [tbl]; omega))]
    rw [← bucketNat, entries 2 _ (K 8) (by simp [linkLog]) (by simp [linkLog, OutLRange]), k8]
  · rw [word_observed (m := writeLog d9.σ.mem (linkLog K (link_loads d9.σ.mem K))) _ fun i hi => through12 _
      (blockNotG _ (by omega) (by omega)) (blockLive _ (by omega) (by omega)) (Or.inl (by omega))]
    rw [show p.toNat = (K 8).toNat by rw [k8],
      entries 0 _ (K 20) (by simp [linkLog]) (by
        simp only [linkLog, List.drop, OutLRange, p8Nat, bucketNat, k8, and_true]; omega), k20]
  · rw [word_observed (m := writeLog d9.σ.mem (linkLog K (link_loads d9.σ.mem K))) _ fun i hi => through12 _
      (blockNotG _ (by omega) (by omega)) (blockLive _ (by omega) (by omega)) (Or.inl (by omega))]
    rw [hk, ← p8Nat, entries 1 _ (bytesVal .ld ((link_loads d9.σ.mem K).getD 0 [])) (by simp [linkLog]) (by
        simp only [linkLog, List.drop, OutLRange, bucketNat, and_true]; rw [p8Nat, tbl]; omega)]
    simp only [link_loads, List.getD_cons_zero]
    rw [read8_value, bucketNat]
    apply word_observed
    intro i hi
    rw [toD _ (fun h => by rw [p16] at h; unfold InExt at h; dsimp only at h; rw [tbl] at *; omega),
      M.kept _ (bucket_not_foot (by omega)) (Or.inl (by rw [tbl]; omega))]
  · intro j hj
    rw [through12 _ (blockNotG _ (by omega) (by omega)) (blockLive _ (by omega) (by omega)) (Or.inl (by omega)),
      linkOut _ (Or.inr (by omega)) (Or.inr (by rw [tbl]; omega))]
    have b := D9.bytes j hj
    rw [p16] at b
    rw [show p.toNat + 16 + j = p.toNat + 16 + j from rfl, b, p8.memory, p7.memory, wl_nil]
    exact M.kept _ (fun foot => by
      rcases allocator_payload_outside he0 e0Low foot with h | h <;> omega) (Or.inl (by omega))
  · intro x nG nF nW win
    rw [hk] at nW
    have nF' : ¬ vsaFoot ((p.toNat, name.length + 24) :: H) x := fun f => nF (vsaFoot_cons f)
    have outBlock : x < p.toNat ∨ p.toNat + (name.length + 24) ≤ x := by
      rcases Nat.lt_or_ge x p.toNat with h | h
      · exact Or.inl h
      · rcases Nat.lt_or_ge x (p.toNat + (name.length + 24)) with h' | h'
        · exact absurd (foot_of_fresh M.fresh pLow pHigh h h') nF
        · exact Or.inr h'
    have nW' : x < Layout.sym_named_value_table + 8 * k ∨ Layout.sym_named_value_table + 8 * k + 8 ≤ x := by
      unfold BucketWord at nW; omega
    rw [through12 _ nG nF' (by rcases win with h | h <;> omega), linkOut _ (by omega) nW',
      toD _ (fun h => by rw [p16] at h; unfold InExt at h; dsimp only at h; omega)]
    exact M.kept x nF win
  · have a : Vsa.Machine.output d12.σ = Vsa.Machine.output d9.σ := by
      rw [show Vsa.Machine.output d12.σ = Vsa.Machine.output d11.σ by simp only [Vsa.Machine.output, rp.output]]
      simp only [Vsa.Machine.output, p11.output, p10.output]
    have b : Vsa.Machine.output d8.σ = Vsa.Machine.output d.σ := by
      simp only [Vsa.Machine.output, p8.output, p7.output]
    rw [a, D9.output, b, M.output]


/-! ### The whole call -/

open OCaml.Bytecode (Val registerNamedValue)
open OCaml.Vm (Place valWord)
open NamedValue (TableShape TableBlocks TableFoot NodeAt strOf chainFind Entry setNode insertNode
  table_bucket strcmp_loaded_of mask_pinned_of fixedBytes_transport)

/-- The bytes either path writes in the table: the bucket word of the key,
the value slots of the nodes. -/
def TableWrite (chains : Nat → List Entry) (k x : Nat) : Prop :=
  BucketWord k x ∨ ∃ b, b < 13 ∧ ∃ e ∈ chains b, InExt (e.1.toNat, 8) x

theorem chainFind_mem {qs : String} :
    ∀ {l : List (BitVec 64 × String)}, chainFind qs l ≠ 0#64 → ∃ e ∈ l, e.2 = qs ∧ e.1 = chainFind qs l
  | [], h => absurd rfl h
  | (n, k) :: rest, h => by
    by_cases e : qs = k
    · exact ⟨(n, k), List.mem_cons_self, e.symm, by simp [chainFind, e]⟩
    · have h' : chainFind qs rest ≠ 0#64 := by simpa [chainFind, e] using h
      obtain ⟨x, hx, k', f⟩ := chainFind_mem h'
      exact ⟨x, List.mem_cons_of_mem _ hx, k', by simp [chainFind, e, f]⟩

/-- The table's blocks stay allocated when newlib's footprint shrinks. -/
theorem _root_.OCaml.Vm.Primitives.Named.NamedValue.TableBlocks.shrink {H H' : List (Nat × Nat)}
    {chains : Nat → List Entry} (h : TableBlocks H chains) (sub : ∀ a, vsaFoot H' a → vsaFoot H a) :
    TableBlocks H' chains :=
  ⟨h.keys, h.low, h.apart, fun b hb e he a na f => h.live b hb e he a na (sub a f)⟩

/-- The table's blocks stay allocated when newlib's new footprint lies in the
old one and bytes `X` the nodes avoid. -/
theorem _root_.OCaml.Vm.Primitives.Named.NamedValue.TableBlocks.carry {H H' : List (Nat × Nat)}
    {chains : Nat → List Entry} {X : Nat → Prop} (h : TableBlocks H chains)
    (sub : ∀ a, vsaFoot H' a → vsaFoot H a ∨ X a)
    (apart : ∀ b, b < 13 → ∀ e ∈ chains b, ∀ a, NamedValue.NodeBytes e.1 e.2.1 a → ¬ X a) :
    TableBlocks H' chains :=
  ⟨h.keys, h.low, h.apart, fun b hb e he a na f =>
    (sub a f).elim (h.live b hb e he a na) (apart b hb e he a na)⟩

/-- A grown block list has a smaller footprint. -/
theorem vsaFoot_grown {H H' : List (Nat × Nat)} (grown : ∀ e ∈ H, e ∈ H') : ∀ a, vsaFoot H' a → vsaFoot H a := by
  rintro a (g | ⟨h1, h2, h3⟩)
  · exact .inl g
  · exact .inr ⟨h1, h2, fun e he => h3 e (grown e he)⟩

theorem _root_.OCaml.Vm.Primitives.Named.NamedValue.TableBlocks.mono {H H' : List (Nat × Nat)} {chains : Nat → List Entry} (h : TableBlocks H chains)
    (grown : ∀ e ∈ H, e ∈ H') : TableBlocks H' chains :=
  h.shrink (vsaFoot_grown grown)

/-- Total reads and presence on both sides give the partial read. -/
theorem opt_of_getD {m m' : Vsa.MemRepr.Mem} {a b : Nat} (same : (m'[b]?).getD 0 = (m[a]?).getD 0)
    (p : (m[a]?).isSome) (p' : (m'[b]?).isSome) : m'[b]? = m[a]? := by
  cases h : m[a]? with
  | none => rw [h] at p; cases p
  | some x =>
    cases h' : m'[b]? with
    | none => rw [h'] at p'; cases p'
    | some y => rw [h, h'] at same; simp at same; rw [same]

/-- A C string copied byte for byte to another address. -/
theorem _root_.Vsa.MemRepr.CStr.shift {m m' : Vsa.MemRepr.Mem} {a b : Nat} {cs : List Char} (h : CStr m a cs)
    (same : ∀ i, i ≤ cs.length → m'[b + i]? = m[a + i]?) : CStr m' b cs := by
  -- discipline: allow(O5-run-induction) induction on a C string, not a run relation
  induction h generalizing b with
  | nil z => exact .nil (by have := same 0 (Nat.le_refl _); simp only [Nat.add_zero] at this; rw [this]; exact z)
  | @cons a x cs hx ne lt _ ih =>
    refine .cons (by have := same 0 (Nat.zero_le _); simp only [Nat.add_zero] at this; rw [this]; exact hx) ne lt
      (ih fun i hi => ?_)
    have := same (i + 1) (by simp only [List.length_cons]; omega)
    rwa [show b + (i + 1) = b + 1 + i by omega, show a + (i + 1) = a + 1 + i by omega] at this

/-- **A call of `caml_register_named_value(name, v)` on the table**: the
prologue's input, readiness with room for the node, a frame for the deepest
callee, the table and its blocks, the key as a C string in a live block, the
value's word, RAM below the arena's end live, the roots' statics apart from
the table. -/
structure RegisterTable (live : Nat → Prop) (Shape : Mem → Nat → List (BitVec 64) → Prop)
    (foot : Mem → Nat → List (BitVec 64) → Nat → Prop) (Table : Mem → (Nat → Nat) → Prop)
    (tfoot : Mem → Nat → Prop) (depth : Nat) (H : List (Nat × Nat))
    (cap charge : Nat) (R : Nat → BitVec 64) (name : List (BitVec 8)) (pl : Place)
    (named : List (String × Val)) (chains : Nat → List Entry) (v : Val) (S : GenRoots.RootsState) (c : Config) :
    Prop where
  input : RegisterInput R name c
  ready : RuntimeReadyL live H (cap + charge) (R 2) (R 1) c
  charged : vsaChg (name.length + 24) charge
  frame : NativeFrame (R 2) (64 + depth)
  deepR : 32 + OCaml.Vm.Gc.Skiplist.opStack ≤ depth
  depthAligned : depth % 16 = 0
  table : TableShape c.σ.mem pl named chains
  blocks : TableBlocks H chains
  /-- the generational roots, with the table's value slots registered -/
  roots : GenRoots.RootsAt Shape foot Table tfoot H S c.σ.mem
  registered : ∀ b, b < 13 → ∀ e ∈ chains b, e.1 ∈ S.slots
  query : CString c.σ.mem (R 10).toNat (strOf name)
  qslack : ∀ cs, CStr c.σ.mem (R 10).toNat cs → StrcmpWSlack (R 10) cs.length
  value : valWord pl v = some (R 11)
  keyLow : heapStart ≤ (R 10).toNat
  keyHigh : (R 10).toNat + name.length + 8 ≤ heapEnd
  keyBlock : ∃ e ∈ H, heapStart ≤ e.1 ∧ e.1 ≤ (R 10).toNat ∧ (R 10).toNat + name.length + 1 ≤ e.1 + e.2
  ramLive : ∀ a, 0x80000000 ≤ a → a < heapEnd → live a
  /-- the table is off the lists, `random_seed`, the page table and the state words -/
  tableOff : ∀ a, TableFoot chains a →
    ¬ RootsG Shape foot c.σ.mem a ∧ ¬ tfoot c.σ.mem a ∧ ¬ GenRoots.StateWord S a

/-- **The named table with registered value slots** at `m`: the table, its
blocks allocated in `H`, the generational roots, every node's value slot
registered. -/
structure NamedRootsAt (Shape : Mem → Nat → List (BitVec 64) → Prop)
    (foot : Mem → Nat → List (BitVec 64) → Nat → Prop) (Table : Mem → (Nat → Nat) → Prop)
    (tfoot : Mem → Nat → Prop) (H : List (Nat × Nat)) (pl : Place) (named : List (String × Val))
    (chains : Nat → List Entry) (S : GenRoots.RootsState) (m : Mem) : Prop where
  table : TableShape m pl named chains
  blocks : TableBlocks H chains
  roots : GenRoots.RootsAt Shape foot Table tfoot H S m
  registered : ∀ b, b < 13 → ∀ e ∈ chains b, e.1 ∈ S.slots

/-- **`caml_register_named_value` returned**: `Val_unit` at the caller with
its registers; readiness on newlib's new blocks, with the table representing
`registerNamedValue` of the key and `v` and the roots' invariant; every byte
outside the lists, `random_seed`, the allocator's footprint, the table's bucket
word and value slots and the stack window is kept. -/
structure Registered (live : Nat → Prop) (Shape : Mem → Nat → List (BitVec 64) → Prop)
    (foot : Mem → Nat → List (BitVec 64) → Nat → Prop) (Table : Mem → (Nat → Nat) → Prop)
    (tfoot : Mem → Nat → Prop) (depth : Nat) (H : List (Nat × Nat))
    (R : Nat → BitVec 64) (name : List (BitVec 8)) (pl : Place) (named : List (String × Val))
    (chains : Nat → List Entry) (v : Val) (c f : Config) : Prop where
  returned : Returned live (RootsG Shape foot c.σ.mem)
    (fun H' m => ∃ chains' S', NamedRootsAt Shape foot Table tfoot H' pl (registerNamedValue (strOf name) v named)
      chains' S' m)
    depth H R (TableWrite chains ((NamedValue.hashBytes name).toNat % 13)) c f

/-- **`caml_register_named_value(name, v)`** from its entry: the prologue,
the hash and the walk (`look`), then the found path (`found_tail`, the node's
value through `caml_modify_generational_global_root`) or the new-node path
(`miss_allocate`, `miss_link`, the epilogue). The table then represents
`registerNamedValue (strOf name) v named`. -/
theorem register_named_value_run {live : Nat → Prop} [LibraryLive live] {depth : Nat}
    {Shape : Mem → Nat → List (BitVec 64) → Prop} {foot : Mem → Nat → List (BitVec 64) → Nat → Prop}
    {Table : Mem → (Nat → Nat) → Prop} {tfoot : Mem → Nat → Prop}
    (ops : OCaml.Vm.Gc.Skiplist.Ops Shape foot) (tf : OCaml.Vm.Gc.PageTableFrame Table tfoot)
    (roots : GenRoots.RootCallsG Shape foot Table tfoot) (persist : GprsPersist_Statement)
    {H : List (Nat × Nat)} {cap charge : Nat} {R : Nat → BitVec 64} {name : List (BitVec 8)} {pl : Place}
    {named : List (String × Val)} {chains : Nat → List Entry} {v : Val} {S : GenRoots.RootsState} {c : Config}
    (h : RegisterTable live Shape foot Table tfoot depth H cap charge R name pl named chains v S c) :
    ∃ f, Steps c f ∧ Registered live Shape foot Table tfoot depth H R name pl named chains v c f := by
  have frame := h.frame
  have big : 64 ≤ 64 + depth := Nat.le_add_right _ _
  have lower := frame.lower
  have upper := frame.upper
  have hE : heapEnd = 0x86800000 := rfl
  have hS : heapStart = 0x8007d140 := rfl
  have tbl : Layout.sym_named_value_table = 0x8006bff0 := rfl
  have keyLow := h.keyLow
  have keyHigh := h.keyHigh
  have kLt : (NamedValue.hashBytes name).toNat % 13 < 13 := Nat.mod_lt _ (by decide)
  -- the table on the memory after the prologue
  have same1 : ∀ a, a < heapEnd → (writeLog c.σ.mem (saveLog R))[a]? = c.σ.mem[a]? := fun a ha =>
    frameOn_writeLog _ _ _ (saveLog_inside frame big) a ⟨Or.inl (show a < (R 2).toNat - 64 by omega), trivial⟩
  have image := h.input.leaf.image
  have code1 : Code.StrcmpLoaded (writeLog c.σ.mem (saveLog R)) :=
    strcmp_loaded_of (fixedBytes_transport image.text fun a ha => same1 a (by
      simp only [Image.textBase, Image.textSize] at ha; omega))
  have mask1 : MaskPinned (writeLog c.σ.mem (saveLog R)) :=
    mask_pinned_of (fixedBytes_transport image.rodata fun a ha => same1 a (by
      simp only [Image.rodataBase, Image.rodataSize] at ha; omega))
  have shape1 := h.table.transport_low same1 code1 mask1
  obtain ⟨cs0, str0, e0⟩ := h.query
  have len0 : cs0.length = name.length := by
    have := congrArg String.length e0
    rw [NamedValue.strOf_length, String.length_ofList] at this
    exact this.symm
  have strSame : ∀ i, i ≤ cs0.length →
      (writeLog c.σ.mem (saveLog R))[(R 10).toNat + i]? = c.σ.mem[(R 10).toNat + i]? :=
    fun i hi => same1 _ (by omega)
  have query1 : CString (writeLog c.σ.mem (saveLog R)) (R 10).toNat (strOf name) :=
    ⟨cs0, str0.transport (fun i hi b hb => (strSame i hi).trans hb), e0⟩
  have qslack1 : ∀ cs, CStr (writeLog c.σ.mem (saveLog R)) (R 10).toNat cs → StrcmpWSlack (R 10) cs.length := by
    intro cs str
    have eq : cs0 = cs := (str0.transport (fun i hi b hb => (strSame i hi).trans hb)).unique str
    subst eq
    exact h.qslack cs0 str0
  obtain ⟨d, run, looked⟩ := look h.input (table_bucket shape1 query1 qslack1)
  -- the table bytes the paths keep
  have tableFoot : ∀ a, TableFoot chains a → ¬ vsaFoot H a := by
    intro a ha foot
    rcases ha with bucket | ⟨b, hb, e, he, node⟩
    · exact bucket_not_foot bucket foot
    · exact h.blocks.live b hb e he a node foot
  have tableLow : ∀ a, TableFoot chains a → a < heapEnd := by
    intro a ha
    rcases ha with bucket | ⟨b, hb, e, he, node⟩
    · rw [tbl] at bucket; omega
    · obtain ⟨nx, nd⟩ := (h.table.heads b hb).node_of_mem e he
      have := nd.arena
      unfold NamedValue.NodeBytes at node; omega
  have presentC : ∀ a, a < heapEnd → 0x80000000 ≤ a → (c.σ.mem[a]?).isSome := fun a hi lo =>
    h.ready.platform.live a (h.ramLive a lo hi)
  have tableHigh : ∀ a, TableFoot chains a → 0x80000000 ≤ a := by
    intro a ha
    rcases ha with bucket | ⟨b, hb, e, he, node⟩
    · rw [tbl] at bucket; omega
    · have := h.blocks.low b hb e he; unfold NamedValue.NodeBytes at node; omega
  have window : ∀ a, a < heapEnd → a < (R 2).toNat - (64 + depth) := fun a ha => by omega
  have listsLive : ∀ a, OCaml.Vm.Gc.Skiplist.ListsFoot Shape foot c.σ.mem a → ¬ vsaFoot H a :=
    fun a ⟨_, _, _, sh, f⟩ => (ops.live _ _ _ sh H _ c rfl h.ready.heap a f).1
  have deep : 544 ≤ depth := by have := h.deepR; unfold OCaml.Vm.Gc.Skiplist.opStack at this; omega
  by_cases r0 : chainFind (strOf name) ((chains ((NamedValue.hashBytes name).toNat % 13)).map
      fun e => (e.1, strOf e.2.1)) = 0#64
  · -- the new node
    rw [r0] at looked
    obtain ⟨e6, p, run6, M⟩ := miss_allocate persist h.ready frame deep h.depthAligned h.input.named keyLow keyHigh
      h.charged run looked
    obtain ⟨e12, run12, L⟩ := miss_link ops tf roots frame h.deepR M keyLow keyHigh h.keyBlock h.roots listsLive
      (fun a lo hi => h.tableOff a (Or.inl ⟨lo, hi⟩))
    obtain ⟨H'', cap'', ⟨r12, heapB, ys', os', rootsP⟩⟩ := L.ready
    have pc12 : PCAt 0x800214d0#64 e12 := by have h' := L.pc; rwa [show link_call.link = 0x800214d0#64 by decide] at h'
    obtain ⟨f, runE, ep⟩ := epilogue (m := c.σ.mem) r12 pc12 h.ready.aligned frame big L.slots
    -- the key is absent
    suffices post : ∃ chains' S', NamedRootsAt Shape foot Table tfoot H'' pl
        (registerNamedValue (strOf name) v named) chains' S' f.σ.mem by
      refine ⟨f, run.trans (run6.trans (run12.trans runE)), ⟨?_⟩⟩
      refine { pc := ep.pc, result := ep.result, saved := ep.saved,
               ready := ⟨H'', cap'', ep.ready, fun a v => (heapB a v).imp vsaFoot_cons id, post⟩,
               output := ?_, kept := ?_ }
      · rw [show Vsa.Machine.output f.σ = Vsa.Machine.output e12.σ by simp only [Vsa.Machine.output, ep.output]]
        exact L.output
      · intro x nG nF nOwn win
        rw [ep.memory]
        exact L.kept x nG nF (fun w => nOwn (Or.inl w)) win
    · -- the key is absent
      have absent : ∀ y, (strOf name, y) ∉ named := by
        intro y hy
        have look := NamedValue.lookup_of_mem h.table.unique hy
        obtain ⟨n, kb, v', mem, -, find, -⟩ := (NamedValue.table_find h.table).2 y look
        obtain ⟨nx, nd⟩ := (h.table.heads _ kLt).node_of_mem _ mem
        exact nd.nonnull (find.symm.trans r0)
      have presentF : ∀ a, a < heapEnd → 0x80000000 ≤ a → (f.σ.mem[a]?).isSome := fun a hi lo =>
        ep.ready.platform.live a (h.ramLive a lo hi)
      have p16 : (p + 16#64).toNat = p.toNat + 16 := by
        have := M.high; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have pHigh := M.high
      have pLow := M.low
      have keyByte : ∀ i, i ≤ cs0.length → f.σ.mem[(p + 16#64).toNat + i]? = c.σ.mem[(R 10).toNat + i]? := by
        intro i hi
        rw [p16]
        apply opt_of_getD _ (presentC _ (by omega) (by omega)) (presentF _ (by omega) (by omega))
        rw [ep.memory]; exact L.keyBytes i (by omega)
      have node : NodeAt f.σ.mem pl p
          (bytesVal .ld (read8 c.σ.mem (NamedValue.bucketAddr ((NamedValue.hashBytes name).toNat % 13)).toNat))
          name v := by
        have tohost : (tohostAddr : Nat) + 8 ≤ heapStart := by decide
        refine { nonnull := M.nonzero, value := ?_, next := ?_, nextWindow := ?_, name := ⟨cs0, str0.shift keyByte, e0⟩,
                 slack := ?_, arena := by omega }
        · rw [ep.memory, L.valueWord]; exact h.value
        · rw [read8_value, read8_value, NamedValue.bucketAddr_toNat _ kLt, ep.memory]
          have p8 : (p + 8#64).toNat = p.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
          rw [p8]; exact L.nextWord
        · have p8 : p + 8#64 = BitVec.ofNat 64 (p.toNat + 8) := by
            apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] <;> omega
          rw [p8]; exact (window_of_nat (by simp only [Layout.sym_tohost]; omega) (by omega)
            (by have := M.align; omega)).read
        · intro cs str
          have eq : cs0 = cs := (str0.shift keyByte).unique str
          subst eq
          rw [len0]
          refine ⟨by rw [p16] <;> omega, by rw [p16] <;> omega, by rw [p16] <;> omega, Or.inr (by rw [p16] <;> omega),
            Or.inr (by rw [p16] <;> omega)⟩
      obtain ⟨shape', blocks'⟩ := h.table.insert h.blocks absent
        (fun a ta out => by
          apply NamedValue.agree_of_getD _ (fun _ => presentF _ (tableLow a ta) (tableHigh a ta))
          rw [ep.memory]
          refine L.kept a (h.tableOff a ta).1 (tableFoot a ta) ?_ (Or.inl (window a (tableLow a ta)))
          rw [NamedValue.bucketAddr_toNat _ kLt] at out; unfold BucketWord; omega)
        (by rw [read8_value, NamedValue.bucketAddr_toNat _ kLt, ep.memory]; exact L.head)
        node M.low M.fresh (by omega) (NamedValue.strcmp_loaded ep.ready.image) (NamedValue.mask_pinned ep.ready.image)
      have rootsF : GenRoots.RootsAt Shape foot Table tfoot H''
          { S with ys := ys', os := os', slots := p :: S.slots } f.σ.mem := by
        rw [ep.memory]; exact rootsP
      refine ⟨_, _, ⟨shape', blocks'.carry heapB ?_, rootsF, ?_⟩⟩
      · intro b hb e he a na g
        simp only [NamedValue.insertNode] at he
        split at he
        · rcases List.mem_cons.1 he with rfl | t
          · have hi : a < p.toNat + (name.length + 24) := by
              unfold NamedValue.NodeBytes at na; dsimp only at na; omega
            have lo : p.toNat ≤ a := na.1
            rcases g with l | ⟨-, l⟩
            · exact listsLive a l (foot_of_fresh M.fresh pLow pHigh lo hi)
            · unfold OCaml.Vm.Gc.Skiplist.randomSeed at l; omega
          · exact (h.tableOff a (Or.inr ⟨b, hb, e, t, na⟩)).1 g
        · exact (h.tableOff a (Or.inr ⟨b, hb, e, he, na⟩)).1 g
      · intro b hb e he
        simp only [NamedValue.insertNode] at he
        split at he
        · rcases List.mem_cons.1 he with rfl | t
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (h.registered b hb e t)
        · exact List.mem_cons_of_mem _ (h.registered b hb e he)
  · -- the found node
    obtain ⟨e, he, ek, efst⟩ := chainFind_mem r0
    obtain ⟨⟨n0, kb0, v0⟩, mem0, rfl⟩ := List.mem_map.1 he
    simp only at ek efst
    rw [← efst] at looked
    obtain ⟨nx, nd⟩ := (h.table.heads _ kLt).node_of_mem _ mem0
    have nLow := h.blocks.low _ kLt _ mem0
    have arena := nd.arena
    simp only at nLow arena
    obtain ⟨f, runF, ret, slot⟩ := found_tail ops tf roots persist h.ready frame h.deepR h.depthAligned run looked
      nd.nonnull h.roots (h.registered _ kLt _ mem0)
    have own : ∀ x, ¬ TableWrite chains ((NamedValue.hashBytes name).toNat % 13) x → ¬ InExt (n0.toNat, 8) x :=
      fun x n i => n (Or.inr ⟨_, kLt, _, mem0, i⟩)
    obtain ⟨H3, cap3, ⟨r3, heapB, ys', os', rootsP⟩⟩ := ret.ready
    have presentF : ∀ a, a < heapEnd → 0x80000000 ≤ a → (f.σ.mem[a]?).isSome := fun a hi lo =>
      r3.platform.live a (h.ramLive a lo hi)
    obtain ⟨shape', blocks'⟩ := h.table.update h.blocks mem0 ek
      (fun a ta out => by
        apply NamedValue.agree_of_getD _ (fun _ => presentF _ (tableLow a ta) (tableHigh a ta))
        exact ret.kept a (h.tableOff a ta).1 (tableFoot a ta) (fun i => by unfold InExt at i; dsimp only at i; omega)
          (Or.inl (window a (tableLow a ta))))
      slot h.value (NamedValue.strcmp_loaded r3.image) (NamedValue.mask_pinned r3.image)
    refine ⟨f, run.trans runF, ⟨{ ret with
      kept := fun x nG nF nOwn win => ret.kept x nG nF (own x nOwn) win
      ready := ⟨H3, cap3, r3, heapB, _, _, ⟨shape', blocks'.carry heapB ?_, rootsP, ?_⟩⟩ }⟩⟩
    · intro b hb e he a na g
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      rw [NamedValue.setNode_fst, NamedValue.setNode_key] at na
      exact (h.tableOff a (Or.inr ⟨b, hb, e0, he0, na⟩)).1 g
    · intro b hb e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      rw [NamedValue.setNode_fst]
      exact h.registered b hb e0 he0

end OCaml.Vm.Primitives.Named.NamedRegister
