import OCaml.Vm.Boot.Startup.SecureGetenvPrefix
import OCaml.Vm.Boot.Startup.NativeFrame
import OCaml.Vm.Gc.Readback
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem secure_slot_nat {sp} (frame : NativeFrame sp 32) (off : Nat) (bound : off ≤ 32) :
    (secureStack sp + BitVec.ofNat 64 off).toNat = nativeFrameBase sp 32 + off := by
  rw [secureStack, frame.address off bound]
  exact frame.slot_nat bound

theorem secure_log_slots {sp ra s0 s1} (frame : NativeFrame sp 32) :
    secureLog sp ra s0 s1 =
      [(nativeFrameBase sp 32 + 16, 8, s0), (nativeFrameBase sp 32 + 8, 8, s1),
       (nativeFrameBase sp 32 + 24, 8, ra)] := by
  simp only [secureLog, secure_slot_nat frame 16 (by decide), secure_slot_nat frame 8 (by decide),
    secure_slot_nat frame 24 (by decide)]

theorem secure_log_inside {sp ra s0 s1} (frame : NativeFrame sp 32) :
    LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (secureLog sp ra s0 s1) := by
  rw [secure_log_slots frame]
  have lower := frame.lower
  simp only [LogInW, InsideW]
  unfold nativeFrameBase
  constructor
  · left; constructor <;> omega
  constructor
  · left; constructor <;> omega
  constructor
  · left; constructor <;> omega
  trivial

/-- One stack-frame certificate discharges every save in secure getenv. -/
theorem secure_getenv_input {sp name ra s0 s1 c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (secureInput sp name ra s0 s1)) (frame : NativeFrame sp 32) :
    SecureGetenvInput sp name ra s0 s1 c where
  toLeafInput := leaf
  registers := regs
  windows := by
    intro off member
    have choices : off = 16 ∨ off = 8 ∨ off = 24 := by simpa using member
    have bound : off + 8 ≤ 32 := by omega
    have aligned : off % 8 = 0 := by rcases choices with rfl | rfl | rfl <;> decide
    rw [secureStack, frame.address off (by omega)]
    exact frame.word bound aligned
  outside := frame.image_outside (secure_log_inside frame)

structure SecureSaved (sp ra s0 s1 : BitVec 64) (c : Config) : Prop where
  saved0 : bytesT c.σ.mem (nativeFrameBase sp 32 + 16) 8 = s0
  saved1 : bytesT c.σ.mem (nativeFrameBase sp 32 + 8) 8 = s1
  returnAddress : bytesT c.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra

theorem secure_saved_after_prefix {before after : Config} {sp ra s0 s1}
    (frame : NativeFrame sp 32) (memory : after.σ.mem = writeLog before.σ.mem (secureLog sp ra s0 s1)) :
    SecureSaved sp ra s0 s1 after := by
  rw [secure_log_slots frame] at memory
  constructor
  · rw [memory]
    apply OCaml.Vm.Gc.word_writeLog_at _ _ 0 _ _ rfl
    simp only [List.drop, OutLRange]
    exact ⟨Or.inr (by omega), Or.inl (by omega), trivial⟩
  · rw [memory]
    apply OCaml.Vm.Gc.word_writeLog_at _ _ 1 _ _ rfl
    simp only [List.drop, OutLRange]
    exact ⟨Or.inl (by omega), trivial⟩
  · rw [memory]
    exact OCaml.Vm.Gc.word_writeLog_at _ _ 2 _ _ rfl trivial

theorem SecureSaved.transport {before after sp ra s0 s1} (h : SecureSaved sp ra s0 s1 before)
    (same : after.σ.mem = before.σ.mem) : SecureSaved sp ra s0 s1 after := by
  constructor <;> rw [same]
  · exact h.saved0
  · exact h.saved1
  · exact h.returnAddress
end OCaml.Vm.Boot.Startup
