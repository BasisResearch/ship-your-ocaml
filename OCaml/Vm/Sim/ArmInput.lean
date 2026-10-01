import OCaml.Refinement
import OCaml.Vm.Sim.Dispatch
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

/-- Changing only the abstract bytecode PC does not alter the represented
memory payload. Register restoration is a separate machine obligation. -/
theorem payload_pc {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} (h : VmPayload P s c pl cp sp high) (pc : Nat) :
    VmPayload P {s with pc := pc} c pl cp sp high :=
  ⟨h.stackHigh, h.trapsp, h.codeBase, h.code, h.globals, h.stack, h.heap, h.world⟩

theorem ArmInput.running {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (h : ArmInput L P s op c pl cp sp high) : Running L P s c :=
  ⟨⟨pl, cp, sp, high, h.toVmReprAt⟩,
    ⟨h.dispatch.good, h.dispatch.image, h.runtime⟩, h.dispatch.loop⟩

/-- Geometry for one bytecode-word read. These are architectural RAM limits;
all program and image addresses are supplied by the representation/Layout. -/
structure CodeReadAt (a : Nat) : Prop where
  lower : 0x80000000 ≤ a
  upper : a + 4 ≤ 0x100000000
  htif : a + 4 ≤ Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 8 ≤ a

/-- Code RAM geometry also excludes 64-bit address wraparound. -/
theorem CodeReadAt.toNat {a : Nat} (h : CodeReadAt a) :
    (BitVec.ofNat 64 a).toNat = a := by
  apply Nat.mod_eq_of_lt
  have upper := h.upper
  omega

/-- A fetched ordinary word is pinned by code representation. Method-cache
slots require their separate F3 observation contract. -/
theorem code_read {code : Code} {base i : Nat} {c : Config} {w : BitVec 32}
    (repr : CodeRepr code base c) (fetch : code[i]? = some w)
    (ordinary : methodCacheSlot code i = false) : word32 c (base + 4 * i) = w :=
  (repr i w fetch).resolve_left (by simp only [ordinary, Bool.false_eq_true, not_false_eq_true])

/-- Ordinary operand-read facts supplied by bytecode decoding and code
placement. They do not assume a machine run or an arm postcondition. -/
structure OperandAt (P : Prog) (pl : Place) (i : Nat) (w : BitVec 32) : Prop where
  fetch : P.code[i]? = some w
  ordinary : methodCacheSlot P.code i = false
  geometry : CodeReadAt (pl.codeBase + 4 * i)

theorem OperandAt.read {P : Prog} {pl : Place} {i : Nat} {w : BitVec 32} {c : Config}
    (h : OperandAt P pl i w) (repr : CodeRepr P.code pl.codeBase c) :
    word32 c (BitVec.ofNat 64 (pl.codeBase + 4 * i)).toNat = w := by
  rw [h.geometry.toNat]
  exact code_read repr h.fetch h.ordinary

/-- The representation supplies every dispatch input except the explicitly
named clock, code-placement, and non-cache opcode-position facts. -/
theorem ArmInput.of_repr {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (h : VmReprAt P s c pl cp sp high) (platform : PlatformOk L.runtimeOk c)
    (loop : LoopRegisters c) (tick : c.tick < 2)
    (geometry : CodeReadAt (pl.codeBase + 4 * s.pc))
    (fetch : P.code[s.pc]? = some (BitVec.ofNat 32 op.toNat))
    (opcodeSlot : methodCacheSlot P.code s.pc = false) :
    ArmInput L P s op c pl cp sp high := by
  have ha : (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)).toNat =
      pl.codeBase + 4 * s.pc := geometry.toNat
  refine ⟨h, ⟨platform.control, platform.image, loop, h.atHead, h.pc,
    ?_, tick, ?_, ?_, ?_⟩, platform.runtime⟩
  · rw [ha]
    exact code_read h.code fetch opcodeSlot
  · simpa only [ha] using geometry.lower
  · simpa only [ha] using geometry.upper
  · simpa only [ha] using geometry.htif

end OCaml.Vm.Sim
