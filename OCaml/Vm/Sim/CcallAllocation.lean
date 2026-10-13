import OCaml.Vm.Sim.Ccall
import OCaml.Vm.Sim.CcallWriting
import OCaml.Vm.Sim.AllocInput
import OCaml.Vm.Sim.MakeblockRows
import OCaml.Vm.Sim.LoopGeometry

/-!
# Allocating primitives at the C_CALL boundary

An allocating primitive reserves one object below `young_ptr` and fills it:
its write log is the young-pointer store (`grabReserveLog`) followed by
stores inside the reserved block. At the callee entry, the fresh location is
placed at that block (`allocPlaces`); the post-call heap fits the budget. From
these, `ccall_allocation_entry` builds the primitive's `AllocationInput` and
runtime frame (`AllocLogOk.of_block`, `AllocFrame`) and adapts its
represented summary to the C_CALL return, with the loop geometry of the
grown heap (`LoopGeometry.alloc_log`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **Adapt a primitive summary with an exact write log to the C_CALL
return boundary**: the geometry after the call may use the exact memory. -/
theorem ccall_logged_summary {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {name : String} {v : Val}
    {heap : Heap} {world : World} {domain frameSp result env entry ra : BitVec 64} {pc : Nat}
    {args : List Val} {writes : List Nat} {footprint : List WEntry} {before : Config}
    (S : FnSummary entry (fun c => c = before)
      (PrimitivePost L.runtimeOk P s pl cp sp high name args v result heap world writes
        (writeLog before.σ.mem footprint) before ra))
    (preserved : ∀ r ∈ callSavedRegs, ∀ n ∈ writes, gprReg n ≠ r)
    (saved : Ccall1Saved {s with pc := pc} pl sp domain frameSp env before)
    (outside : CcallSavedOutside footprint domain frameSp)
    (arena : LogInW [arenaWindow] footprint)
    (geometry : ∀ after : Config, after.σ.mem = writeLog before.σ.mem footprint →
      OCaml.LoopGeometry L P {s with accu := v, heap := heap, world := world} after pl cp high)
    (native : NativePlaced before) :
    FnSummary entry (fun c => c = before)
      (CcallReturn ra L P {s with pc := pc, accu := v, heap := heap, world := world}
        pl cp sp high domain frameSp result env) := by
  apply S.weaken (fun _ h => h)
  intro after post
  have frame : ∀ x, OutL footprint x → byte after x = byte before x := fun x hx => by
    simp only [byte, bytesT, post.call.memory, writeLog_out _ _ _ hx]
  have regs : ∀ r ∈ callSavedRegs, after.σ.regs.get? r = before.σ.regs.get? r :=
    fun r hr => post.call.frame r (preserved r hr) (by revert r; decide)
  exact ccall_primitive_return post (saved.frame_outside outside frame regs) (geometry after post.call.memory)
    (native.frame_outside arena outside.domainPtr (saved.domainWord ▸ outside.externalRaise) frame
      (regs _ (by decide)))

/-- The log of an allocation of `n` words at `a` from the domain at `c`. -/
abbrev allocLog (c : Config) (a : Nat) (block : List WEntry) : List WEntry :=
  grabReserveLog (word c Layout.sym_Caml_state).toNat a ++ block

/-- **An allocating primitive at the callee entry.** `summary` is the
primitive's represented contract for the reservation at `a`; the fresh
location `loc` is placed at the block below the entry's young pointer. -/
theorem ccall_allocation_entry {ra : BitVec 64} {args : List Val} {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high domain entry : Nat} {env : BitVec 64} {name : String} {o : Obj}
    {writes : List Nat} {c : Config} (allocFrame : AllocFrame L)
    (budget : (s.heap.alloc o).1.words ≤ L.budget.heapWords)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes)
    (roots : AllocationRoots P s o)
    (preserved : ∀ r ∈ callSavedRegs, ∀ n ∈ writes, gprReg n ≠ r)
    (block : Nat → List WEntry)
    (inside : ∀ a, ReservedBlock c a o.wosize → LogInW [⟨a - 8, a + 8 * o.wosize⟩] (block a))
    (summary : ∀ a, AllocationInput L.runtimeOk P s pl cp sp high ra args o a (allocLog c a (block a)) c →
      ReservedBlock c a o.wosize → AllocationRuntime L.runtimeOk c (allocLog c a (block a)) →
      FnSummary (BitVec.ofNat 64 entry) (fun x => x = c)
        (PrimitivePost L.runtimeOk P s pl cp sp high name args (.ptr (s.heap.alloc o).2 0) (BitVec.ofNat 64 a)
          (s.heap.alloc o).1 s.world writes (writeLog c.σ.mem (allocLog c a (block a))) c ra))
    (setup : CcallSetupPost ra args L P s pl cp sp high domain entry env c)
    (placed : pl.φ (s.heap.alloc o).2 = some ((runtimeFields c).youngPtr - 8 * o.wosize)) :
    FnSummary (BitVec.ofNat 64 entry) (fun x => x = c)
      (CcallReturn ra L P { s with pc := s.pc + 2, accu := Val.ptr (s.heap.alloc o).2 0, heap := (s.heap.alloc o).1, world := s.world }
        pl cp sp high (BitVec.ofNat 64 domain) (BitVec.ofNat 64 (sp - 16))
        (BitVec.ofNat 64 ((runtimeFields c).youngPtr - 8 * o.wosize)) env) := by
  have g := setup.geometry
  have ng := g.nursery
  have sg := g.toStackGeometry
  have stack := setup.input.data.stack
  have space : high - Layout.stackBytes ≤ sp := stack_space stack (by omega)
  have words : s.heap.words + (o.wosize + 1) ≤ L.budget.heapWords := by
    rw [Heap.words_alloc] at budget; omega
  have b := ReservedBlock.of_reservation ng (⟨g.room, words⟩ : Reservation L s c o.wosize)
  generalize ha : (runtimeFields c).youngPtr - 8 * o.wosize = a at b placed ⊢
  have ok := AllocLogOk.of_block b ng sg stack space (inside a b)
  have input : AllocationInput L.runtimeOk P s pl cp sp high ra args o a (allocLog c a (block a)) c :=
    { setup.input with
      fields := roots, placed := placed
      separate := ng.allocationOutside b.young b.capacity b.room (Nat.le_refl _)
      payloadOutside := ok.payload, bindingsOutside := ok.bindings }
  have runtime : AllocationRuntime L.runtimeOk c (allocLog c a (block a)) :=
    allocFrame.alloc P s c pl cp high a (block a) setup.input.runtime ng (b.free (inside a b))
      b.capacity (by have := b.young; omega) (by have := b.aligned; have := b.room; omega)
  have saved := setup.saved
  have hs := stack.1
  have apart := b.stackApart ng
  have dom := b.domainApart ng
  have room := b.room
  have statics := sg.statics
  have hd := sg.domain.1
  simp only [stackWindow] at hd
  have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  have he : Layout.off_extern_sp + 8 ≤ Layout.domainStateBytes := by decide
  have hx : Layout.off_external_raise + 8 ≤ Layout.domainStateBytes := by decide
  have blockMiss : ∀ off, off + 8 ≤ Layout.domainStateBytes →
      OutLRange (block a) ((word c Layout.sym_Caml_state).toNat + off) 8 := fun off hoff =>
    outLRange_of_windows (inside a b) ⟨by dsimp only; omega, trivial⟩
  have domainNat : (BitVec.ofNat 64 domain : BitVec 64) = word c Layout.sym_Caml_state := saved.domainWord
  have frameNat : (BitVec.ofNat 64 (sp - 16) : BitVec 64).toNat = sp - 16 := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt
    have := sg.top; omega
  have outside : CcallSavedOutside (allocLog c a (block a)) (BitVec.ofNat 64 domain)
      (BitVec.ofNat 64 (sp - 16)) :=
    { domainPtr := ok.payload.domain
      externSp := by
        rw [domainNat]
        have e : (word c Layout.sym_Caml_state + BitVec.ofNat 64 Layout.off_extern_sp).toNat =
            (word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp := by
          have := sg.domainArena; have := ng.arena
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [Layout.off_extern_sp] at *
          simp only [Vsa.Sim.DlHeap.heapEnd] at *; omega
        rw [e]
        exact outLRange_append (grab_out (by simp only [Layout.off_young_ptr, Layout.off_extern_sp]; omega))
          (blockMiss _ he)
      env := by
        rw [frameNat]
        refine outLRange_append (grab_out ?_) (outLRange_of_windows (inside a b) ⟨by dsimp only; omega, trivial⟩)
        simp only [Layout.off_young_ptr] at hy ⊢
        omega
      externalRaise := by rw [domainNat]; exact ok.external }
  apply ccall_logged_summary (summary a input b runtime) preserved saved outside ok.arena
    (fun after memory => g.alloc_log placed ok.reserve rfl rfl ok.payload.domain ok.bindings.contents
      ok.payload.channels ok.payload.openHead memory) setup.native

/-- Configurations agreeing on every byte agree on every word. -/
theorem word_of_bytes {c c' : Config} (same : ∀ x, byte c' x = byte c x) (a : Nat) : word c' a = word c a :=
  Reloc.bytesT_congr fun j _ => same (a + j)

/-- **The loop geometry depends only on the bytes**: an observation post
(every byte as predicted) carries the geometry of the predicted memory. -/
theorem _root_.OCaml.LoopGeometry.bytes {L : OCaml.Layout} {P : Prog} {s : St} {c c' : Config} {pl : Place}
    {cp : ChanPlace} {high : Nat} (g : OCaml.LoopGeometry L P s c pl cp high) (same : ∀ x, byte c' x = byte c x) :
    OCaml.LoopGeometry L P s c' pl cp high := by
  have w := word_of_bytes same
  exact g.transport (fun l o h => ⟨o, h, rfl⟩) rfl (w _) (w _)
    (by simp only [runtimeFields, domainWord, w]) (by simp only [runtimeFields, domainWord, w]) (w _)
    (fun _ _ _ _ _ => w _) rfl

end OCaml.Vm.Sim
