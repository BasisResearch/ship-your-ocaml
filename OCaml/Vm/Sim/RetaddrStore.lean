import OCaml.Vm.Sim.StackStore
import OCaml.Vm.Sim.StackPrefix
import OCaml.Vm.Sim.MulArithmetic
import OCaml.Vm.Sim.WriteGeometry

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Native store order for a three-word OCaml return frame. -/
def retaddrLog (sp : Nat) (pc env extra : BitVec 64) : List WEntry :=
  [(sp - 16, 8, env), (sp - 24, 8, pc), (sp - 8, 8, extra)]

/-- The static frame space and separation supplied by the loop invariant. -/
structure RetaddrWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp dest : Nat) (env : BitVec 64) : Prop where
  room : 24 ≤ sp
  stackNat : sp < 2^64
  envWindow : WriteWindow (BitVec.ofNat 64 (sp - 16)) 8
  pcWindow : WriteWindow (BitVec.ofNat 64 (sp - 24)) 8
  extraWindow : WriteWindow (BitVec.ofNat 64 (sp - 8)) 8
  payload : PayloadOutside (retaddrLog sp (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) env
    (tag64 (BitVec.ofNat 63 s.extra))) P s c pl cp sp
  image : ImageOutside (retaddrLog sp (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) env
    (tag64 (BitVec.ofNat 63 s.extra)))
  young : YoungOutside (retaddrLog sp (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) env
      (tag64 (BitVec.ofNat 63 s.extra))) c
  bindings : BindingsOutside (retaddrLog sp (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) env
    (tag64 (BitVec.ofNat 63 s.extra))) P c

/-- The three saved words, named in logical stack order. -/
structure RetaddrStored (sp : Nat) (pc env extra : BitVec 64) (c : Config) : Prop where
  code : word c (sp - 24) = pc
  environment : word c (sp - 16) = env
  extraArgs : word c (sp - 8) = extra

/-- The three distinct slots retain their last stored values. -/
theorem retaddr_stored {before after : Config} {sp : Nat} {pc env extra : BitVec 64}
    (room : 24 ≤ sp)
    (memory : after.σ.mem = writeLog before.σ.mem (retaddrLog sp pc env extra)) :
    RetaddrStored sp pc env extra after := by
  constructor
  · apply word_after_writeLog_at memory 1 _ _ rfl
    simp only [retaddrLog, List.drop, OutLRange, and_true]
    omega
  · apply word_after_writeLog_at memory 0 _ _ rfl
    simp only [retaddrLog, List.drop, OutLRange, and_true]
    omega
  · exact word_after_writeLog_at memory 2 _ _ rfl trivial

/-- The return frame introduces only its already-live environment root. -/
theorem retaddr_roots {P : Prog} {s : St} (dest : Nat) :
    ∀ v ∈ [.code dest, s.env, Val.ofInt s.extra], ∀ l,
      v.loc? = some l → Live s.heap (roots P s) l := by
  intro v member l loc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · cases loc
  · exact Live.root (by simp [roots]) loc
  · cases loc

/-- An exact three-store frame joins the old represented stack. -/
theorem retaddr_payload {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest : Nat} {env : BitVec 64}
    (h : VmPayload P s before pl cp sp high)
    (space : RetaddrWriteOk P s before pl cp sp dest env)
    (envWord : valWord pl s.env = some env)
    (memory : after.σ.mem = writeLog before.σ.mem
      (retaddrLog sp (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) env (tag64 (BitVec.ofNat 63 s.extra))))
    (output : after.σ.sailOutput = before.σ.sailOutput) :
    VmPayload P {s with stack := .code dest :: s.env :: Val.ofInt s.extra :: s.stack}
      after pl cp (sp - 24) high := by
  have framed := h.frame_log space.payload memory output
  have saved := retaddr_stored space.room memory
  apply payload_stack_prepend (front := [.code dest, s.env, Val.ofInt s.extra]) framed
  · have room := space.room
    simp only [List.length_cons, List.length_nil]
    omega
  · intro i v selected
    have room := space.room
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by
      simp only [List.length_cons, List.length_nil] at bound
      omega
    rcases cases with rfl | rfl | rfl
    · cases selected
      rw [Nat.mul_zero, Nat.add_zero, saved.code]
      rfl
    · cases selected
      rw [show sp - 24 + 8 * 1 = sp - 16 by omega, saved.environment]
      exact envWord
    · cases selected
      rw [show sp - 24 + 8 * 2 = sp - 8 by omega, saved.extraArgs]
      rfl
  · exact retaddr_roots dest

/-- The native extra-argument tag agrees with the abstract saved value. -/
theorem retaddr_extra_word (extra : Nat) :
    ((BitVec.ofNat 64 extra <<< (1 : Nat)) + 1#64) = tag64 (BitVec.ofNat 63 extra) := by
  rw [← tag_truncate]
  apply congrArg tag64
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- All three return-frame writes lie immediately below the old stack. -/
theorem retaddr_log_in {sp : Nat} (pc env extra : BitVec 64) (room : 24 ≤ sp) :
    LogInW [⟨sp - 24, sp⟩] (retaddrLog sp pc env extra) := by
  simp only [retaddrLog, LogInW, InsideW, or_false, and_true]
  omega

/-- Restore the represented caller after its checked three-store return frame. -/
theorem retaddr_restore {L : OCaml.Layout} {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest pc : Nat} {env accu : BitVec 64}
    (stable : WindowStable L.runtimeOk [⟨sp - 24, sp⟩])
    (data : VmReprAt P s before pl cp sp high)
    (platform : PlatformOk L.runtimeOk before) (loop : LoopRegisters before)
    (space : RetaddrWriteOk P s before pl cp sp dest env)
    (envWord : valWord pl s.env = some env) (accuWord : valWord pl s.accu = some accu)
    (post : StackPost before pl pc (sp - 24) accu
      (writeLog before.σ.mem (retaddrLog sp (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) env
        (tag64 (BitVec.ofNat 63 s.extra)))) after)
    (geometry : OCaml.LoopGeometry L P s before pl cp high)
    (native : NativePlaced before) :
    Running L P {s with pc := pc, stack := .code dest :: s.env :: Val.ofInt s.extra :: s.stack} after := by
  have payload := retaddr_payload (payload_of_repr data) space envWord post.memory post.output
  have memoryFrame : FrameOn [⟨sp - 24, sp⟩] before.σ.mem after.σ.mem := by
    rw [post.memory]
    apply frameOn_writeLog
    exact retaddr_log_in _ _ _ space.room
  exact running_of_payload (payload_pc payload pc)
    (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory,
      stable before after memoryFrame platform.runtime⟩
    (post.registers data rfl rfl accuWord) (post.loopRegisters loop)
    (geometry.frame_log rfl rfl space.payload.domain space.bindings.contents space.young post.memory)
    (native.frame_vm (ws := [⟨sp - 24, sp⟩]) (retaddr_log_in _ _ _ space.room) (by simp only [List.mem_singleton, forall_eq]; exact geometry.stack_below (by have := data.stack.1; omega)) space.payload.domain post.memory post.nativeSp)

end OCaml.Vm.Sim
