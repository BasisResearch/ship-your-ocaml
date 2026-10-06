import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Sim.WriteGeometry
import Vsa.Sim.DlHeap
import Vsa.Sim.Boot.Bytes

/-!
# `caml_interprete`'s caller at the Layer A cut

`Loaded` describes the machine at `caml_interprete`'s entry, called by
`caml_main`. The bytecode's `STOP` returns through caml_interprete's and
caml_main's epilogues into `caml_do_exit`, so the cut must also name that
caller: the return address, the native stack and caml_main's saved frame,
the RAM windows the interpreter prologue writes, and the separation of those
writes from everything the VM representation observes.

`InterpCaller P c pl cp high sp callerRegs mainSaved` is that named premise.
It becomes a field of `LoadedAt` together with its proof for the captured
whileMin cut (bprime, with a0-boot).
a0-boot supplies it from the reset run's caml_main frame: the native stack
lies above `heapEnd` and below `__stack_top`, and the VM's code, heap, stack
and channels lie in the allocator arena below `heapEnd`.
-/

namespace OCaml.Vm
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Sim

/-- caml_interprete's native frame size (the prologue's `addi sp, sp, -528`). -/
abbrev interpFrame : Nat := Layout.interpFrameBytes

/-- Every window entry writes, as a footprint (values are irrelevant): the
interpreter's native frame below the caller's sp, `caml_callback_depth`, and
`Caml_state->external_raise`. -/
def entryFootprint (sp domain : Nat) : List WEntry :=
  [(sp - interpFrame, interpFrame, 0), (Layout.sym_caml_callback_depth, 4, 0),
   (domain + Layout.off_external_raise, 8, 0)]

/-- **The caller of `caml_interprete` at the cut** (named premise of `Loaded`). -/
structure InterpCaller (P : Prog) (c : Config) (pl : Place) (cp : ChanPlace) (high : Nat)
    (sp : Nat) (callerRegs mainSaved : Nat → BitVec 64) : Prop where
  /-- the callee-saved registers caml_interprete's prologue saves hold `callerRegs` -/
  regs : ∀ r ∈ Layout.interpSavedRegs, gpr c r = some (callerRegs r)
  /-- with ra = caml_main's return site after its `jal caml_interprete` -/
  ra : callerRegs 1 = 0x80004ff8#64
  /-- `sp` is the caller's native stack pointer -/
  stack : gpr c 2 = some (BitVec.ofNat 64 sp)
  /-- the native frames lie above the allocator arena and below the stack top -/
  frameLow : Vsa.Sim.DlHeap.heapEnd + interpFrame ≤ sp
  frameHigh : sp + Layout.camlMainFrameBytes ≤ Layout.sym_stack_top
  aligned : sp % 16 = 0
  /-- caml_main's saved registers `mainSaved`, with its own return into `main` -/
  mainFrame : ∀ r ∈ Layout.camlMainSavedRegs, word c (sp + Layout.camlMainSaveOffset r) = mainSaved r
  mainReturn : mainSaved 1 = 0x80001df0#64
  /-- the `Caml_state` record lies in the allocator arena, word aligned -/
  domainLow : Vsa.Sim.DlHeap.heapStart ≤ (word c Layout.sym_Caml_state).toNat
  domainHigh : (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes ≤ Vsa.Sim.DlHeap.heapEnd
  domainAligned : (word c Layout.sym_Caml_state).toNat % 8 = 0
  /-- entry's writes miss everything the initial VM representation observes -/
  outside : PayloadOutside (entryFootprint sp (word c Layout.sym_Caml_state).toNat) P P.init c pl cp high
  /-- and the primitive table -/
  primTable : OutLRange (entryFootprint sp (word c Layout.sym_Caml_state).toNat)
    (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8
  primEntries : ∀ i name, P.prims[i]? = some name →
    OutLRange (entryFootprint sp (word c Layout.sym_Caml_state).toNat)
      ((word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat + 8 * i) 8
  /-- the dispatch clock at the cut (the loop's `tick < 2` invariant) -/
  tick : c.tick < 2
  /-- HTIF is idle at the cut (no half-written tohost command) -/
  htifIdle : c.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes = some (0#4)

/-- The caller is a property of registers and total reads: it transports to
any zero-equivalent memory (e.g. `fillZero`). -/
theorem InterpCaller.of_mem {P : Prog} {c c' : Config} {pl : Place} {cp : ChanPlace} {high sp : Nat}
    {callerRegs mainSaved : Nat → BitVec 64}
    (h : InterpCaller P c pl cp high sp callerRegs mainSaved) (regs : c'.σ.regs = c.σ.regs)
    (mem : Vsa.Densify.MemEqv c'.σ.mem c.σ.mem) (tick : c'.tick = c.tick) : InterpCaller P c' pl cp high sp callerRegs mainSaved := by
  have hw : ∀ a, word c' a = word c a := fun a => Vsa.Sim.Boot.bytesT_memEqv mem a 8
  have hg : ∀ n, gpr c' n = gpr c n := by
    intro n; unfold gpr Vsa.Sim.gprGet; rw [regs]
  refine ⟨?_, h.ra, ?_, h.frameLow, h.frameHigh, h.aligned, ?_, h.mainReturn, ?_, ?_, ?_, ?_, ?_, ?_,
    tick ▸ h.tick, by rw [regs]; exact h.htifIdle⟩
  · intro r hr; rw [hg]; exact h.regs r hr
  · rw [hg]; exact h.stack
  · intro r hr; rw [hw]; exact h.mainFrame r hr
  · rw [hw]; exact h.domainLow
  · rw [hw]; exact h.domainHigh
  · rw [hw]; exact h.domainAligned
  · have e := hw Layout.sym_Caml_state
    have o := h.outside
    rw [e]
    refine ⟨o.domain, ?_, ?_, o.codeBase, o.atomBase, o.globals, o.code, o.stack, o.heap, o.channels⟩
    · rw [e]; exact o.stackHigh
    · rw [e]; exact o.trapsp
  · rw [hw]; exact h.primTable
  · intro i name hi; rw [hw, hw]; exact h.primEntries i name hi

end OCaml.Vm
