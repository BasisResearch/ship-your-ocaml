import OCaml.Vm.Gc.ForwardedIteration
import OCaml.Vm.Gc.ObservationFrame

namespace OCaml.Vm.Gc.ForwardedField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The actual call's native and destination windows keep the oldify code
image available for later iterations of the enclosing scan. -/
theorem Input.oldifyCode_after {R domain before after writes}
    (input : Input R domain before)
    (post : MopupCall.AdvancedPost (args R before) before after writes) :
    Code.Caml_oldify_oneLoaded after.σ.mem := by
  rw [post.memory]
  apply image_writeLog Code.caml_oldify_one_transport input.oldifyCode
  intro e member
  exact Nat.le_trans (by decide : (0x80009cb4 : Nat) ≤ tohostAddr)
    (ForwardedCall.effect_high (R := MopupCall.linked (args R before))
      input.conditions.rootWrite input.stackWindows e member)

/-- Native values retained by a whole forwarded iteration. -/
def stable (R : Nat → BitVec 64) : GRegs :=
  [(2,R 2),(18,R 18),(19,R 19),(20,R 20),(21,R 21),(22,R 22),(23,R 23),(24,R 24),(25,R 25)]

/-- The next iteration has an advanced source/index and the mopup call link. -/
def next (R : Nat → BitVec 64) (n : Nat) : BitVec 64 :=
  if n = 1 then MopupCall.call.link else if n = 8 then R 8 + 8#64
  else if n = 9 then R 9 + 1#64 else R n

theorem Input.stable {R domain c} (input : Input R domain c) : GHolds c.σ (stable R) := by
  apply gholds_select input.registers
  intro n v member
  simp only [ForwardedField.stable, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

theorem stable_after {R before after}
    (post : MopupCall.AdvancedPost (args R before) before after [1,8,9,10,11,12,14,15])
    (holds : GHolds before.σ (stable R)) : GHolds after.σ (stable R) := by
  apply gholds_of_frame post.native _ (by change KeysOK [2,18,19,20,21,22,23,24,25]; decide)
    ?_ ?_ holds
  · change ∀ n ∈ [2,18,19,20,21,22,23,24,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false
    decide
  · change ∀ n ∈ [2,18,19,20,21,22,23,24,25], ∀ m ∈ [1,8,9,10,11,12,14,15], (gprReg m == gprReg n) = false
    decide

/-- Every register read at the next field boundary is supplied by the
actual restored/advanced register view. The overwritten x10/x11 inputs are
not required: the field classifier computes both before calling oldify. -/
theorem Input.next_registers {R domain before after}
    (input : Input R domain before)
    (post : MopupCall.AdvancedPost (args R before) before after [1,8,9,10,11,12,14,15]) :
    GHolds after.σ (ForwardedField.carried (next R)) := by
  have saved := stable_after post input.stable
  exact ⟨gholds_lookup _ saved rfl, gholds_lookup _ post.registers rfl,
    gholds_lookup _ post.registers rfl, post.link,
    gholds_lookup _ saved rfl, gholds_lookup _ saved rfl, gholds_lookup _ saved rfl,
    gholds_lookup _ saved rfl, gholds_lookup _ saved rfl, gholds_lookup _ saved rfl,
    gholds_lookup _ saved rfl, gholds_lookup _ saved rfl, True.intro⟩

end OCaml.Vm.Gc.ForwardedField
