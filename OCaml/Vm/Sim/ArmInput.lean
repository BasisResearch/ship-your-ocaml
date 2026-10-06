import OCaml.Refinement
import OCaml.Vm.Sim.Dispatch
import OCaml.Vm.Sim.ReadGeometry
import OCaml.Vm.Primitives.Payload

namespace OCaml.Vm.Sim
open OCaml.Bytecode Vsa.Machine
open OCaml.Vm.Primitives

/-- An arm-ready loop state. Its dispatch field exposes the extra clock and
bytecode-address facts still needed beyond the current `Running` relation. -/
structure ArmInput (L : OCaml.Layout) (P : Prog) (s : St) (op : Opcode)
    (c : Config) (pl : Place) (cp : ChanPlace) (sp high : Nat) : Prop
    extends VmReprAt P s c pl cp sp high where
  dispatch : DispatchInput op (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) c
  runtime : L.runtimeOk c
  /-- the VM stack geometry of this placement (`Invariant.lean`) -/
  geometry : ArmGeometry P s c pl cp high
  /-- the native invocation (`Invocation.lean`) -/
  native : NativePlaced c

/-- Changing only the abstract bytecode PC does not alter the represented
memory payload. Register restoration is a separate machine obligation. -/
theorem payload_pc {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} (h : VmPayload P s c pl cp sp high) (pc : Nat) :
    VmPayload P {s with pc := pc} c pl cp sp high :=
  ⟨h.stackHigh, h.trapsp, h.codeBase, h.code, h.globals, h.stack, h.heap, h.world, h.atomBase⟩

theorem ArmInput.running {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (h : ArmInput L P s op c pl cp sp high) : Running L P s c :=
  ⟨⟨pl, cp, sp, high, h.toVmReprAt⟩,
    ⟨h.dispatch.good, h.dispatch.image, h.runtime⟩, h.dispatch.loop,
    ⟨pl, cp, sp, high, h.toVmReprAt, h.geometry⟩, h.native⟩

/-- Geometry for one bytecode-word read. These are architectural RAM limits;
all program and image addresses are supplied by the representation/Layout. -/
abbrev CodeReadAt (a : Nat) : Prop := RamReadAt a 4

/-- Code RAM geometry also excludes 64-bit address wraparound. -/
theorem CodeReadAt.toNat {a : Nat} (h : CodeReadAt a) :
    (BitVec.ofNat 64 a).toNat = a := RamReadAt.toNat h

/-- A fetched word is pinned by the (exact, F1) code representation. -/
theorem code_read {code : Code} {base i : Nat} {c : Config} {w : BitVec 32}
    (repr : CodeRepr code base c) (fetch : code[i]? = some w) : word32 c (base + 4 * i) = w :=
  repr i w fetch

/-- Ordinary operand-read facts supplied by bytecode decoding and code
placement. They do not assume a machine run or an arm postcondition. -/
structure OperandAt (P : Prog) (pl : Place) (i : Nat) (w : BitVec 32) : Prop where
  fetch : P.code[i]? = some w
  geometry : CodeReadAt (pl.codeBase + 4 * i)

theorem OperandAt.read {P : Prog} {pl : Place} {i : Nat} {w : BitVec 32} {c : Config}
    (h : OperandAt P pl i w) (repr : CodeRepr P.code pl.codeBase c) :
    word32 c (BitVec.ofNat 64 (pl.codeBase + 4 * i)).toNat = w := by
  rw [h.geometry.toNat]
  exact code_read repr h.fetch

/-- The generated load's four-byte observation survives a read-only prefix. -/
theorem OperandAt.read32 {P : Prog} {pl : Place} {i : Nat} {w : BitVec 32} {c d : Config}
    (h : OperandAt P pl i w) (repr : CodeRepr P.code pl.codeBase c)
    (memory : d.σ.mem = c.σ.mem) :
    Vsa.Sim.bytesT4 d.σ.mem (pl.codeBase + 4 * i) = w := by
  rw [memory]
  simpa only [word32, Vsa.Sim.bytesT_four_eq] using code_read repr h.fetch

/-- The representation supplies every dispatch input except the explicitly
named clock and code-placement facts. -/
theorem ArmInput.of_repr {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (h : VmReprAt P s c pl cp sp high) (platform : PlatformOk L.runtimeOk c)
    (loop : LoopRegisters c) (tick : c.tick < 2)
    (geometry : CodeReadAt (pl.codeBase + 4 * s.pc))
    (fetch : P.code[s.pc]? = some (BitVec.ofNat 32 op.toNat))
    (stack : ArmGeometry P s c pl cp high) (native : NativePlaced c) :
    ArmInput L P s op c pl cp sp high := by
  have ha : (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)).toNat =
      pl.codeBase + 4 * s.pc := geometry.toNat
  refine ⟨h, ⟨platform.control, platform.image, loop, h.atHead, h.pc,
    ?_, tick, ?_, ?_, ?_⟩, platform.runtime, stack, native⟩
  · rw [ha]
    exact code_read h.code fetch
  · simpa only [ha] using geometry.lower
  · simpa only [ha] using geometry.upper
  · simpa only [ha, Vsa.Sim.tohostAddr, Vsa.Sim.LibraryLayout.tohostAddr,
      Layout.sym_tohost] using geometry.htif

/-- Every word of the code buffer is readable (`StackGeometry.codeLow`/`codeArena`). -/
theorem StackGeometry.code_read {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high i : Nat} (g : StackGeometry P s c pl cp high) (bound : i < P.code.size) :
    CodeReadAt (pl.codeBase + 4 * i) := by
  have := g.codeLow
  have := g.codeArena
  refine ⟨?_, ?_, Or.inr ?_⟩ <;> simp only [Layout.sym_bss_end, Layout.sym_tohost,
    Vsa.Sim.DlHeap.heapEnd] at * <;> omega

/-- An operand read needs only its fetch: the geometry is the witness's. -/
theorem OperandAt.of_fetch {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high i : Nat} {w : BitVec 32} (g : ArmGeometry P s c pl cp high)
    (fetch : P.code[i]? = some w) : OperandAt P pl i w :=
  ⟨fetch, g.code_read (by simpa using (Array.getElem?_eq_some_iff.mp fetch).1)⟩

/-- The code fact dispatch needs at the current bytecode PC: the fetch of the
opcode word. Named obligation; a2-sem supplies it from decoding
(`CodeFacts.lean`). The word's RAM geometry comes from `ArmGeometry`. -/
structure DispatchCode (P : Prog) (s : St) (op : Opcode) : Prop where
  fetch : P.code[s.pc]? = some (BitVec.ofNat 32 op.toNat)

/-- **Arm entry from the loop-head invariant.** The witness is the one that
carries the stack geometry (`Running.stack`). -/
theorem ArmInput.of_loop {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config}
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op) :
    ∃ pl cp sp high, ArmInput L P s op c pl cp sp high := by
  obtain ⟨pl, cp, sp, high, repr, stack⟩ := h.running.stack
  exact ⟨pl, cp, sp, high, ArmInput.of_repr repr h.running.platform h.running.loop h.clock
    (stack.code_read (by simpa using (Array.getElem?_eq_some_iff.mp code.fetch).1))
    code.fetch stack h.running.native⟩

/-- A represented register has the uniquely determined word of its value. -/
theorem represented_register {pl : Place} {v : Val} {c : Config} {r : Nat} {w : BitVec 64}
    (reg : ∃ x, gpr c r = some x ∧ valWord pl v = some x)
    (value : valWord pl v = some w) : gpr c r = some w := by
  obtain ⟨x, hx, hv⟩ := reg
  have same := Option.some.inj (hv.symm.trans value)
  exact same ▸ hx

/-- Dispatch plus a generated body gives a nonempty machine run. All arm
families share this composition; the body establishes its own final predicate. -/
theorem dispatch_compose {c : Config} {op : Opcode} {a : BitVec 64} {Q : Config → Prop}
    (h : DispatchInput op a c)
    (body : ∀ d, DispatchPost c op a d → ∃ nb after, StepsN nb d after ∧ Q after) :
    ∃ after, Plus c after ∧ Q after := by
  obtain ⟨nd, d, hnd, hd, dp⟩ := dispatch_run h
  obtain ⟨nb, after, hb, post⟩ := body d dp
  refine ⟨after, ⟨nd + nb - 1, ?_⟩, post⟩
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ nd + nb)] using hd.append hb

end OCaml.Vm.Sim
