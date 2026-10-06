import OCaml.Vm.Sim.PushtrapStore

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Reconstruct PUSHTRAP's new trap depth and four saved words from its log. -/
theorem pushtrap_payload {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest : Nat} {env : BitVec 64}
    (h : VmPayload P s before pl cp sp high)
    (space : PushtrapWriteOk P s before pl cp sp high dest env)
    (envWord : valWord pl s.env = some env)
    (memory : after.σ.mem = writeLog before.σ.mem
      (pushtrapLog sp (word before Layout.sym_Caml_state).toNat (BitVec.ofNat 64 (pl.codeBase + 4 * dest))
        (tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap))) env (tag64 (BitVec.ofNat 63 s.extra))))
    (out : after.σ.sailOutput = before.σ.sailOutput) :
    VmPayload P {s with stack := .code dest :: Val.ofInt (s.stack.length + 4 - s.trap : Nat) :: s.env :: Val.ofInt s.extra :: s.stack, trap := s.stack.length + 4}
      after pl cp (sp - 32) high := by
  have shape := h.stack.1
  have room := space.room
  have small := space.highSmall
  have saved := pushtrap_stored space.room space.separate memory
  have base : VmPayload P {s with trap := s.stack.length + 4} after pl cp sp high := by
    apply payload_rebuild h space.payload.toPayloadCoreOutside memory out
    · have domain : word after Layout.sym_Caml_state = word before Layout.sym_Caml_state :=
        Reloc.bytesT_congr (copied_of_writeLog memory space.payload.domain)
      rw [domain, saved.trap]
      change (sp - 32) % 2^64 = high - 8 * (s.stack.length + 4)
      omega
    · exact stack_frame_log h.stack space.payload.stack memory
    · exact heap_frame_log h.heap space.payload.heap memory
  apply payload_stack_prepend
    (front := [.code dest, Val.ofInt (s.stack.length + 4 - s.trap : Nat), s.env, Val.ofInt s.extra]) base
  · simp only [List.length_cons, List.length_nil]
    omega
  · intro i v selected
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      simp only [List.length_cons, List.length_nil] at bound
      omega
    rcases cases with rfl | rfl | rfl | rfl
    · cases selected
      rw [Nat.mul_zero, Nat.add_zero, saved.handler]
      rfl
    · cases selected
      rw [show sp - 32 + 8 * 1 = sp - 24 by omega, saved.linkWord]
      rfl
    · cases selected
      rw [show sp - 32 + 8 * 2 = sp - 16 by omega, saved.environment]
      exact envWord
    · cases selected
      rw [show sp - 32 + 8 * 3 = sp - 8 by omega, saved.extraArgs]
      rfl
  · exact pushtrap_roots dest (s.stack.length + 4 - s.trap)

/-- PUSHTRAP writes only its new frame and the domain's trap-pointer field. -/
theorem pushtrap_log_in {sp domain : Nat} (code link env extra : BitVec 64) (room : 32 ≤ sp) :
    LogInW [⟨sp - 32, sp⟩, ⟨domain + Layout.off_trapsp, domain + Layout.off_trapsp + 8⟩]
      (pushtrapLog sp domain code link env extra) := by
  simp only [pushtrapLog, LogInW, InsideW, or_false, and_true]
  omega

/-- Restore the complete loop-head representation after PUSHTRAP's exact writes. -/
theorem pushtrap_restore {L : OCaml.Layout} {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest pc : Nat} {env accu : BitVec 64}
    (stable : WindowStable L.runtimeOk [⟨sp - 32, sp⟩,
      ⟨(word before Layout.sym_Caml_state).toNat + Layout.off_trapsp,
       (word before Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩])
    (data : VmReprAt P s before pl cp sp high)
    (platform : PlatformOk L.runtimeOk before) (loop : LoopRegisters before)
    (space : PushtrapWriteOk P s before pl cp sp high dest env)
    (envWord : valWord pl s.env = some env) (accuWord : valWord pl s.accu = some accu)
    (post : StackPost before pl pc (sp - 32) accu
      (writeLog before.σ.mem (pushtrapLog sp (word before Layout.sym_Caml_state).toNat
        (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) (tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap)))
        env (tag64 (BitVec.ofNat 63 s.extra)))) after)
    (geometry : OCaml.LoopGeometry L P s before pl cp high)
    (native : NativePlaced before) :
    Running L P {s with pc := pc, stack := .code dest :: Val.ofInt (s.stack.length + 4 - s.trap : Nat) :: s.env :: Val.ofInt s.extra :: s.stack, trap := s.stack.length + 4} after := by
  have payload := pushtrap_payload (payload_of_repr data) space envWord post.memory post.output
  have memoryFrame : FrameOn [⟨sp - 32, sp⟩,
      ⟨(word before Layout.sym_Caml_state).toNat + Layout.off_trapsp,
       (word before Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩] before.σ.mem after.σ.mem := by
    rw [post.memory]
    apply frameOn_writeLog
    exact pushtrap_log_in _ _ _ _ space.room
  exact running_of_payload (payload_pc payload pc)
    (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory,
      stable before after memoryFrame platform.runtime⟩
    (post.registers data rfl rfl accuWord) (post.loopRegisters loop)
    (geometry.frame_log rfl rfl space.payload.domain space.bindings.contents space.young post.memory)
    (native.frame_vm (pushtrap_log_in _ _ _ _ space.room) (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> dsimp only <;> first | exact geometry.stack_below (by have := data.stack.1; omega) | (have := geometry.domain_below (off := Layout.off_trapsp + 8) (by decide); omega)) space.payload.domain post.memory post.nativeSp)

end OCaml.Vm.Sim
