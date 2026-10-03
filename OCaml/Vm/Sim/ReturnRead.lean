import OCaml.Vm.Sim.ReturnPayload
import OCaml.Vm.Sim.ReadGeometry

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- Named observations of a saved caller frame, selected from the represented stack. -/
structure ReturnFrameValues (P : Prog) (s : St) (c : Config) (pl : Place)
    (base dest : Nat) (env : Val) (extra : BitVec 63) : Prop where
  code : word c base = BitVec.ofNat 64 (pl.codeBase + 4 * dest)
  environment : valWord pl env = some (word c (base + 8))
  extraArgs : word c (base + 16) = tag64 extra
  root : ∀ l, env.loc? = some l → Live s.heap (roots P s) l

/-- The three frame slots are already represented at the selected stack suffix. -/
theorem return_frame_values {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high count dest : Nat} {env : Val} {extra : BitVec 63} {rest : List Val}
    (h : VmPayload P s c pl cp sp high)
    (stack : s.stack.drop count = .code dest :: env :: .int extra :: rest) :
    ReturnFrameValues P s c pl (sp + 8 * count) dest env extra := by
  have selected (i : Nat) (v : Val)
      (slot : (.code dest :: env :: .int extra :: rest)[i]? = some v) : s.stack[count + i]? = some v := by
    rw [← List.getElem?_drop, stack]
    exact slot
  have code := h.stack.2 count (.code dest) (by simpa using selected 0 (.code dest) rfl)
  have environment := h.stack.2 (count + 1) env (selected 1 env rfl)
  have extraArgs := h.stack.2 (count + 2) (.int extra) (selected 2 (.int extra) rfl)
  refine ⟨(Option.some.inj code).symm, ?_, ?_, stack_value_root (selected 1 env rfl)⟩
  · simpa only [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc] using environment
  · simpa only [Nat.mul_add, ← Nat.add_assoc] using (Option.some.inj extraArgs).symm

/-- Native reads of the three saved caller words require ordinary RAM geometry. -/
structure ReturnFrameReads (base : Nat) : Prop where
  code : RamReadAt base 8
  environment : RamReadAt (base + 8) 8
  extraArgs : RamReadAt (base + 16) 8

end OCaml.Vm.Sim
