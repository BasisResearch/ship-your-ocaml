import OCaml.Vm.Sim.ReadOnly

namespace OCaml.Vm.Sim
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable
open OCaml.Vm.Primitives

/-- Registers unchanged by arms that only advance PC and replace the
accumulator with an immediate or an existing live root. Use the generated register assignment. -/
def immediatePreserved : List Register :=
  [gprReg Layout.reg_sp, gprReg Layout.reg_env, gprReg Layout.reg_extra,
   gprReg Layout.reg_dispatchTable, gprReg Layout.reg_opcodeBound,
   gprReg Layout.reg_pending, gprReg Layout.reg_domain, gprReg 2]

/-- Machine observations sufficient to restore an accumulator-result VM state.
The generated segment supplies execution and its complete frame separately. -/
structure AccuPost (before : Config) (pl : Place) (pc : Nat) (w : BitVec 64)
    (after : Config) : Prop where
  good : GoodState after.σ
  head : pcOf after = some (BitVec.ofNat 64 Layout.loopHead)
  code : gpr after Layout.reg_pc = some (BitVec.ofNat 64 (pl.codeBase + 4 * pc))
  accu : gpr after Layout.reg_accu = some w
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  preserved : ∀ r ∈ immediatePreserved, after.σ.regs.get? r = before.σ.regs.get? r

/-- Immediate results specialize the shared accumulator-word postcondition. -/
abbrev ImmediatePost (before : Config) (pl : Place) (pc : Nat) (n : BitVec 63)
    (after : Config) : Prop := AccuPost before pl pc (tag64 n) after

theorem codePc_add (pl : Place) (pc n : Nat) :
    BitVec.ofNat 64 (pl.codeBase + 4 * pc) + BitVec.ofNat 64 (4 * n) =
      BitVec.ofNat 64 (pl.codeBase + 4 * (pc + n)) := by
  simp only [Nat.mul_add, ← Nat.add_assoc, BitVec.ofNat_add]

theorem codePc_succ (pl : Place) (pc : Nat) :
    BitVec.ofNat 64 (pl.codeBase + 4 * pc) + 4#64 =
      BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 1)) :=
  codePc_add pl pc 1

/-- One restoration proof for read-only accumulator replacements. -/
theorem accu_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high pc : Nat} {v : Val} {w : BitVec 64}
    (stable : MemoryStable L.runtimeOk) (data : VmReprAt P s c pl cp sp high)
    (platform : PlatformOk L.runtimeOk c) (loop : LoopRegisters c)
    (value : valWord pl v = some w)
    (root : ∀ l, v.loc? = some l → Live s.heap (roots P s) l)
    (post : AccuPost c pl pc w after) (geometry : StackGeometry P s c pl cp high)
    (native : NativePlaced c) :
    Running L P {s with pc := pc, accu := v} after := by
  have payload := payload_pc ((payload_of_repr data).accu_of_root v root) pc
  apply readOnly_restore stable payload data.primitives platform ?_ ?_
    post.good post.memory post.output (geometry.state rfl rfl) native
    (post.preserved (gprReg 2) (by decide))
  · refine ⟨post.head, post.code, ?_, ⟨w, post.accu, value⟩, ?_, ?_⟩
    · exact (post.preserved _ (by decide)).trans data.spReg
    · obtain ⟨w, hw, hv⟩ := data.env
      exact ⟨w, (post.preserved _ (by decide)).trans hw, hv⟩
    · exact (post.preserved _ (by decide)).trans data.extra
  · exact loopRegisters_frame
      (fun r hr => post.preserved r (by revert r; decide)) loop

/-- Immediate results introduce no heap root. -/
theorem immediate_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high pc : Nat} {n : BitVec 63}
    (stable : MemoryStable L.runtimeOk) (data : VmReprAt P s c pl cp sp high)
    (platform : PlatformOk L.runtimeOk c) (loop : LoopRegisters c)
    (post : ImmediatePost c pl pc n after) (geometry : StackGeometry P s c pl cp high)
    (native : NativePlaced c) :
    Running L P {s with pc := pc, accu := .int n} after :=
  accu_restore stable data platform loop rfl (fun _ h => by cases h) post geometry native

/-- Check a generated write-set once, then consume the whole frame. -/
theorem immediate_preserved {W : List Register} {σ σ' : MState}
    (frame : StepFrameOut W σ σ')
    (avoid : ∀ r ∈ immediatePreserved, ∀ q ∈ W, (q == r) = false) :
    ∀ r ∈ immediatePreserved, σ'.regs.get? r = σ.regs.get? r :=
  fun r hr => frame.frame r (avoid r hr)

/-- Dispatch's memory frame preserves the executable image for the body. -/
theorem DispatchPost.image {before after : Config} {op : Opcode} {a : BitVec 64}
    (h : DispatchPost before op a after) (image : ExecutableImage before) :
    ExecutableImage after :=
  ⟨fun i hi => by rw [h.memory]; exact image.text i hi,
   fun i hi => by rw [h.memory]; exact image.rodata i hi⟩

/-- Shared composition for generated read-only accumulator bodies. The body premise
is discharged by each generated segment; it is not a headline assumption. -/
theorem accu_arm {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp high pc : Nat} {v : Val} {w : BitVec 64}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s op c pl cp sp high)
    (value : valWord pl v = some w)
    (root : ∀ l, v.loc? = some l → Live s.heap (roots P s) l)
    (body : ∀ d, DispatchPost c op (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d →
      ∃ nb after, StepsN nb d after ∧ AccuPost d pl pc w after) :
    ∃ after, Plus c after ∧ Running L P {s with pc := pc, accu := v} after := by
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨nb, after, hb, post⟩ := body d dp
  refine ⟨nb, after, hb, ?_⟩
  refine accu_restore stable h.toVmReprAt h.running.platform h.dispatch.loop value root
    ?_ h.geometry h.native
  exact ⟨post.good, post.head, post.code, post.accu,
      post.memory.trans dp.memory, post.output.trans dp.frame.out,
      fun r hr => (post.preserved r hr).trans
        (immediate_preserved dp.frame (by decide) r hr)⟩

/-- A control-flow arm retains the represented accumulator. Its generated
body receives the preserved accumulator word at the dispatch boundary. -/
theorem control_arm {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp high pc : Nat}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s op c pl cp sp high)
    (body : ∀ d, DispatchPost c op (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d →
      ∀ w, gpr d Layout.reg_accu = some w → valWord pl s.accu = some w →
      ∃ nb after, StepsN nb d after ∧ AccuPost d pl pc w after) :
    ∃ after, Plus c after ∧ Running L P {s with pc := pc} after := by
  obtain ⟨w, hw, value⟩ := h.accu
  apply accu_arm stable h value (fun _ hl => Live.root (by simp [roots]) hl)
  intro d dp
  exact body d dp w ((dp.frame.frame Register.x21 (by decide)).trans hw) value

/-- Compose an immediate-result arm through the general accumulator rule. -/
theorem immediate_arm {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp high pc : Nat} {n : BitVec 63}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s op c pl cp sp high)
    (body : ∀ d, DispatchPost c op (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d →
      ∃ nb after, StepsN nb d after ∧ ImmediatePost d pl pc n after) :
    ∃ after, Plus c after ∧ Running L P {s with pc := pc, accu := .int n} after :=
  accu_arm stable h rfl (fun _ h => by cases h) body

end OCaml.Vm.Sim
