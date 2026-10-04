import OCaml.Vm.Boot.Startup.NameData
import OCaml.Vm.Boot.Startup.NativeSave
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.MemRepr OCaml.Vm.Primitives

/-- Preserve a C string through byte agreement on its complete zero-terminated extent. -/
theorem cstr_frame {m m' : Mem} {p : Nat} {cs : List Char} (h : CStr m p cs)
    (same : ∀ a, p ≤ a → a ≤ p + cs.length → m'[a]? = m[a]?) : CStr m' p cs := by
  induction h with
  | nil pin =>
    constructor
    rw [same _ (by omega) (by simp)]
    exact pin
  | @cons a b cs pin nonzero ascii tail ih =>
    apply CStr.cons (b := b) (by rw [same a (by omega) (by simp)]; exact pin) nonzero ascii
    apply ih
    intro addr lower upper
    apply same addr (by omega)
    simp only [List.length_cons]
    omega

theorem EnvName.frame {p cs before after} (data : EnvName p cs before)
    (same : ∀ a, p.toNat ≤ a → a ≤ p.toNat + cs.length → after.σ.mem[a]? = before.σ.mem[a]?) :
    EnvName p cs after := ⟨cstr_frame data.bytes same, data.region, data.noEquals⟩

/-- An immutable name below the native frame survives any store log confined to that frame. -/
theorem EnvName.stack_log {p cs before after sp size log} (data : EnvName p cs before)
    (below : p.toNat + cs.length + 1 ≤ nativeFrameBase sp size)
    (inside : LogInW [⟨nativeFrameBase sp size, sp.toNat⟩] log)
    (memory : after.σ.mem = writeLog before.σ.mem log) : EnvName p cs after := by
  apply data.frame
  intro addr lower upper
  rw [memory]
  apply frameOn_writeLog _ _ _ inside
  exact ⟨Or.inl (by change addr < nativeFrameBase sp size; omega), trivial⟩
end OCaml.Vm.Boot.Startup
