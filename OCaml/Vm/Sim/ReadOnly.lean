import OCaml.Vm.Sim.ArmInput
import OCaml.Vm.Sim.InvariantUse

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable
open OCaml.Vm.Primitives

/-- The fixed loop registers and the HTIF counter, pinned to values. -/
def loopFixed : List Register :=
  [gprReg Layout.reg_dispatchTable, gprReg Layout.reg_opcodeBound,
   gprReg Layout.reg_pending, gprReg Layout.reg_domain, Register.htif_payload_writes]

/-- Fixed loop registers and the unpinned callee-saved registers, independent
of the current opcode's data registers. -/
def loopPreserved : List Register :=
  loopFixed ++ [gprReg 26]

/-- Each unpinned callee-saved register is kept or freshly written. -/
theorem saved_of {before after : Config} (loop : LoopRegisters before)
    (each : ∀ n ∈ unpinnedSaved, gpr after n = gpr before n ∨ (gpr after n).isSome) :
    ∀ n ∈ unpinnedSaved, (gpr after n).isSome := fun n hn => by
  rcases each n hn with e | p
  · rw [e]; exact loop.saved n hn
  · exact p

/-- A register frame keeps the unpinned callee-saved registers. -/
theorem saved_frame {before after : Config}
    (frame : ∀ r ∈ [gprReg 26], after.σ.regs.get? r = before.σ.regs.get? r)
    (loop : LoopRegisters before) : ∀ n ∈ unpinnedSaved, (gpr after n).isSome :=
  saved_of loop fun n hn => .inl <| by
    simp only [unpinnedSaved, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl
    exact frame (gprReg 26) (by decide)

/-- `s10` pinned to a value (arms that write it). -/
theorem saved_of_pin {after : Config} {v : BitVec 64} (pin : gpr after 26 = some v) :
    ∀ n ∈ unpinnedSaved, (gpr after n).isSome := fun n hn => by
  simp only [unpinnedSaved, List.mem_singleton] at hn
  subst hn; rw [pin]; rfl

/-- `s10` unchanged keeps the unpinned callee-saved registers present. -/
theorem saved_keep {before after : Config} (e : gpr after 26 = gpr before 26)
    (saved : ∀ n ∈ unpinnedSaved, (gpr before n).isSome) : ∀ n ∈ unpinnedSaved, (gpr after n).isSome :=
  fun n hn => by
    have h := saved n hn
    simp only [unpinnedSaved, List.mem_singleton] at hn
    subst hn; rw [e]; exact h

/-- The loop registers from a frame on the fixed ones and the presence of the
unpinned callee-saved registers (arms that write `s10`/`s11`). -/
theorem loopRegisters_of {before after : Config}
    (frame : ∀ r ∈ loopFixed, after.σ.regs.get? r = before.σ.regs.get? r)
    (loop : LoopRegisters before) (saved : ∀ n ∈ unpinnedSaved, (gpr after n).isSome) :
    LoopRegisters after :=
  ⟨(frame _ (by decide)).trans loop.dispatchTable,
   (frame _ (by decide)).trans loop.opcodeBound,
   (frame _ (by decide)).trans loop.pending,
   (frame _ (by decide)).trans loop.domain,
   (frame _ (by decide)).trans loop.htifIdle, saved⟩

/-- Reconstruct all loop registers from one finite frame check. -/
theorem loopRegisters_frame {before after : Config}
    (frame : ∀ r ∈ loopPreserved, after.σ.regs.get? r = before.σ.regs.get? r)
    (loop : LoopRegisters before) : LoopRegisters after :=
  loopRegisters_of (fun r hr => frame r (List.mem_append_left _ hr)) loop
    (saved_frame (fun r hr => frame r (List.mem_append_right _ hr)) loop)

/-- Register observations common to all read-only arm results. Memory payload
and platform preservation are separate so stack-consuming arms can reuse them. -/
structure VmRegisters (s : St) (pl : Place) (sp : Nat) (c : Config) : Prop where
  head : pcOf c = some (BitVec.ofNat 64 Layout.loopHead)
  pc : gpr c Layout.reg_pc = some (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc))
  spReg : gpr c Layout.reg_sp = some (BitVec.ofNat 64 sp)
  accu : ∃ w, gpr c Layout.reg_accu = some w ∧ valWord pl s.accu = some w
  env : ∃ w, gpr c Layout.reg_env = some w ∧ valWord pl s.env = some w
  extra : gpr c Layout.reg_extra = some (BitVec.ofNat 64 s.extra)

/-- Assemble the loop relation once all named data/platform/register parts
are established, independently of the arm's memory effect. -/
theorem running_of_payload {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (data : VmPayload P s c pl cp sp high) (primitives : PrimitiveBindings P c)
    (platform : PlatformOk L.runtimeOk c) (regs : VmRegisters s pl sp c)
    (loop : LoopRegisters c) (geometry : OCaml.LoopGeometry L P s c pl cp high)
    (native : NativePlaced c) : Running L P s c := by
  have repr : VmReprAt P s c pl cp sp high := ⟨regs.head, regs.pc, regs.spReg, regs.accu, regs.env, regs.extra,
    data.stackHigh, data.trapsp, data.codeBase, data.code,
    data.globals, data.stack, data.heap, data.world, primitives, data.atomBase⟩
  exact ⟨⟨pl, cp, sp, high, repr⟩, platform, loop, ⟨pl, cp, sp, high, repr, geometry⟩, native⟩

/-- Restore any read-only result once its payload and register observations
are established. This is the common image/runtime/primitive-table frame. -/
theorem readOnly_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (stable : MemoryStable L.runtimeOk) (payload : VmPayload P s c pl cp sp high)
    (primitives : PrimitiveBindings P c) (platform : PlatformOk L.runtimeOk c)
    (regs : VmRegisters s pl sp after) (loop : LoopRegisters after)
    (good : GoodState after.σ) (memory : after.σ.mem = c.σ.mem)
    (output : after.σ.sailOutput = c.σ.sailOutput)
    (geometry : OCaml.LoopGeometry L P s c pl cp high) (native : NativePlaced c)
    (nativeSp : gpr after 2 = gpr c 2) : Running L P s after := by
  apply running_of_payload (payload.frame memory output) (primitives.frame memory) ?_ regs loop
    (geometry.same rfl rfl memory) (native.frame_read memory nativeSp)
  exact ⟨good,
    ⟨fun i hi => by rw [memory]; exact platform.image.text i hi,
     fun i hi => by rw [memory]; exact platform.image.rodata i hi⟩,
    stable c after memory platform.runtime⟩

end OCaml.Vm.Sim
