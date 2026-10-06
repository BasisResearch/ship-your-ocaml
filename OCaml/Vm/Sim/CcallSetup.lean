import OCaml.Vm.Sim.Ccall1Store
import OCaml.Vm.Sim.CcallReturn
import OCaml.Vm.Sim.StackStore
import OCaml.Vm.Sim.IndexWord
import OCaml.Vm.Sim.WriteGeometry

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- Represented fixed-arity call boundary, independent of the primitive body. -/
structure CcallSetupPost (ra : BitVec 64) (args : List Val)
    (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place)
    (cp : ChanPlace) (sp high domain entry : Nat) (env : BitVec 64) (c : Config) : Prop where
  input : ImmediateInput L.runtimeOk P s pl cp sp high ra args c
  saved : Ccall1Saved {s with pc := s.pc + 2} pl sp (BitVec.ofNat 64 domain)
    (BitVec.ofNat 64 (sp - 16)) env c
  target : pcOf c = some (BitVec.ofNat 64 entry)
  /-- the VM stack geometry at the callee entry (`Invariant.lean`) -/
  geometry : OCaml.LoopGeometry L P s c pl cp high
  /-- the native invocation at the callee entry (`Invocation.lean`) -/
  native : NativePlaced c
  /-- the VM stack pointer, the accumulator and the next-code pointer still
  hold values (the C callee's prologue spills these callee-saved registers) -/
  vmSaved : ∀ n ∈ [9, 21, 23], (gpr c n).isSome

/-- **Every callee-saved register `s0`–`s11` holds a value at the callee entry**
(the primitive prologues spill them). -/
theorem CcallSetupPost.calleeSaved {ra : BitVec 64} {args : List Val} {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high domain entry : Nat} {env : BitVec 64} {c : Config}
    (setup : CcallSetupPost ra args L P s pl cp sp high domain entry env c) :
    ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], (gpr c n).isSome := by
  have loop := setup.input.loop
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact isSome_of_pin setup.saved.pc
  · exact setup.vmSaved 9 (by simp)
  · exact isSome_of_pin setup.saved.extra
  · exact isSome_of_pin loop.domain
  · exact isSome_of_pin loop.pending
  · exact setup.vmSaved 21 (by simp)
  · exact isSome_of_pin loop.dispatchTable
  · exact setup.vmSaved 23 (by simp)
  · exact isSome_of_pin loop.opcodeBound
  · exact isSome_of_pin setup.saved.domainReg
  · exact loop.saved 26 (by simp [unpinnedSaved])
  · exact loop.saved 27 (by simp [unpinnedSaved])

set_option hygiene false in
/-- Discharge `CcallSetupPost.vmSaved` in a setup proof: each register is the
arm input's pin framed through dispatch and setup, dispatch's next-code pin,
or one of the setup segment's output pins. -/
macro "vm_saved_tac" : tactic => `(tactic| (
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  all_goals first
    | exact isSome_of_pin ((frame.frame (gprReg 23) (by decide)).trans dp.nextCode)
    | exact isSome_of_pin ((frame.frame (gprReg 9) (by decide)).trans
        ((dp.frame.frame (gprReg 9) (by decide)).trans h.spReg))
    | (obtain ⟨w, hw, -⟩ := h.accu
       exact isSome_of_pin ((frame.frame (gprReg 21) (by decide)).trans
         ((dp.frame.frame (gprReg 21) (by decide)).trans hw)))
    | exact isSome_of_pin (PinsHold.get post.pins ⟨0, by simp⟩)
    | exact isSome_of_pin (PinsHold.get post.pins ⟨1, by simp⟩)
    | exact isSome_of_pin (PinsHold.get post.pins ⟨2, by simp⟩)
    | exact isSome_of_pin (PinsHold.get post.pins ⟨3, by simp⟩)
    | exact isSome_of_pin (PinsHold.get post.pins ⟨4, by simp⟩)
    | exact isSome_of_pin (PinsHold.get post.pins ⟨5, by simp⟩)
    | exact isSome_of_pin (PinsHold.get post.pins ⟨6, by simp⟩)
    | exact isSome_of_pin (PinsHold.get post.pins ⟨7, by simp⟩)
    | exact isSome_of_pin (PinsHold.get post.pins ⟨8, by simp⟩)
    | exact isSome_of_pin (PinsHold.get post.pins ⟨9, by simp⟩)
    | exact isSome_of_pin (PinsHold.get post.pins ⟨10, by simp⟩)))

/-- C_CALL setup keeps the native invocation: its three stores lie in the
VM stack and the `Caml_state` record, inside the allocator arena. -/
theorem Ccall1WriteOk.native {P : Prog} {s : St} {c after : Config} {pl : Place} {cp : ChanPlace}
    {sp high domain : Nat} {next env : BitVec 64}
    (space : Ccall1WriteOk P s c pl cp sp domain next env) (n : NativePlaced c)
    (g : ArmGeometry P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (domainWord : word c Layout.sym_Caml_state = BitVec.ofNat 64 domain)
    (memory : after.σ.mem = writeLog c.σ.mem (ccall1Log sp domain next env))
    (x2 : gpr after 2 = gpr c 2) : NativePlaced after := by
  apply n.frame_log (logInW_arena ?_ (ccall1_log_in next env space.room)) space.payload.domain
    space.young.external memory x2
  have hs := stack.1
  have ha := g.arena
  have hd := g.domainArena
  have hn := space.domainNat
  rw [domainWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hd
  have off : Layout.off_extern_sp + 8 ≤ Layout.domainStateBytes := by decide
  intro w hw
  simp only [ccall1Windows, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> simp only <;> omega

abbrev Ccall1SetupPost (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place)
    (cp : ChanPlace) (sp high domain entry : Nat) (env : BitVec 64) :=
  CcallSetupPost (0x80003060#64) [s.accu] L P s pl cp sp high domain entry env

/-- Setup_for_c_call decrements the VM stack by two words. -/
theorem ccall1_frame_address {sp : Nat} (room : 16 ≤ sp) :
    BitVec.ofNat 64 sp + sign_extend (m := 64) (0xff0#12) = BitVec.ofNat 64 (sp - 16) :=
  stack_decrement room (by decide) (by decide)

/-- Stack arguments must exist and their native loads must be readable.
The loop invariant supplies these finite bounds at each call site. -/
structure CcallArguments (s : St) (sp count : Nat) : Prop where
  bound : count ≤ s.stack.length
  read : ∀ i, i < count → RamReadAt (sp + 8 * i) 8

/-- Saved-frame writes preserve every existing stack argument's native word. -/
theorem ccall_argument_load {P : Prog} {s : St} {c : Config} {pl : Place}
    {cp : ChanPlace} {sp domain : Nat} {next env : BitVec 64}
    {memory : Std.ExtHashMap Nat (BitVec 8)}
    (space : Ccall1WriteOk P s c pl cp sp domain next env)
    (written : memory = writeLog c.σ.mem (ccall1Log sp domain next env))
    (i : Nat) (bound : i < s.stack.length) :
    sign_extend (m := 64) (bytesT8 memory (sp + 8 * i)) = word c (sp + 8 * i) := by
  have selected : s.stack[i]? = some s.stack[i] := by simp
  have outside := space.payload.stack i _ selected
  have same := word_read_writeLog_out outside written
  simpa only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend,
    BitVec.signExtend_eq] using same

/-- Consecutive argument registers represent accumulator plus the selected
stack prefix. This factors list lookup and stack representation once. -/
theorem ccall_arguments_repr {s : St} {pl : Place} {c after : Config}
    {sp high count : Nat} {value : BitVec 64}
    (stack : StackRepr c pl sp high s.stack)
    (accu : valWord pl s.accu = some value) (first : gpr after 10 = some value)
    (rest : ∀ i, i < count → gpr after (11 + i) = some (word c (sp + 8 * i))) :
    ArgumentsRepr pl (s.accu :: s.stack.take count) after := by
  intro i v selected
  cases i with
  | zero =>
    cases Option.some.inj selected
    exact ⟨value, accu, first⟩
  | succ i =>
    simp only [List.getElem?_cons_succ, List.getElem?_take] at selected
    split at selected
    next lt =>
      exact ⟨word c (sp + 8 * i), stack.2 i v selected,
        by simpa only [show 10 + (i + 1) = 11 + i by omega] using rest i lt⟩
    next => cases selected

end OCaml.Vm.Sim
