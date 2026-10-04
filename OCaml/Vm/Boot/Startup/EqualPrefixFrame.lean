import OCaml.Vm.Boot.Startup.StrncmpLoop
import OCaml.Vm.Boot.Startup.Environment
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Equal-prefix certificates depend only on their two bounded byte ranges. -/
theorem EqualPrefix.frame {p q last byte} {before after : Config} (h : EqualPrefix p q last byte before)
    (left : ∀ k, k ≤ last → (after.σ.mem[p.toNat + k]?).getD 0 = (before.σ.mem[p.toNat + k]?).getD 0)
    (right : ∀ k, k ≤ last → (after.σ.mem[q.toNat + k]?).getD 0 = (before.σ.mem[q.toNat + k]?).getD 0) :
    EqualPrefix p q last byte after :=
  ⟨h.left, h.right, fun k hk => (left k hk).trans (h.leftByte k hk),
    fun k hk => (right k hk).trans (h.rightByte k hk), h.nonzero⟩

theorem EqualPrefix.same_mem {p q last byte} {before after : Config} (h : EqualPrefix p q last byte before)
    (memory : after.σ.mem = before.σ.mem) : EqualPrefix p q last byte after :=
  h.frame (fun _ _ => by rw [memory]) (fun _ _ => by rw [memory])

/-- A stack-confined log preserves both string prefixes below its frame. -/
theorem EqualPrefix.stack_log {p q last byte sp size log} {before after : Config} (h : EqualPrefix p q last byte before)
    (left : p.toNat + (last + 1) ≤ nativeFrameBase sp size)
    (right : q.toNat + (last + 1) ≤ nativeFrameBase sp size)
    (inside : LogInW [⟨nativeFrameBase sp size, sp.toNat⟩] log)
    (memory : after.σ.mem = writeLog before.σ.mem log) : EqualPrefix p q last byte after := by
  apply h.frame
  · intro k hk
    rw [memory, frameOn_writeLog _ _ _ inside _ ⟨Or.inl (by dsimp only; omega), trivial⟩]
  · intro k hk
    rw [memory, frameOn_writeLog _ _ _ inside _ ⟨Or.inl (by dsimp only; omega), trivial⟩]
end OCaml.Vm.Boot.Startup
