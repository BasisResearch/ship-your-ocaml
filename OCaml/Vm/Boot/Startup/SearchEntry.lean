import OCaml.Vm.Boot.Startup.EqualPrefixData
import OCaml.Vm.Boot.Startup.StrncmpDispatch
import OCaml.Vm.Boot.Startup.NameFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Read-only facts about a matching first environment entry. The query prefix
is compared before reading its '=' delimiter; the following value is unrestricted. -/
structure SearchEntry (sp env entry name : BitVec 64) (count : Nat) (byte : Nat → BitVec 8) (c : Config) : Prop where
  frame : NativeFrame sp 80
  array : ReadWindow env 8
  first : bytesT c.σ.mem env.toNat 8 = entry
  nonnull : entry ≠ 0#64
  envBelow : env.toNat + 8 ≤ nativeFrameBase sp 80
  comparison : EqualPrefix entry name (count - 1) byte c
  region : ReadWindow entry (count + 1)
  equals : (c.σ.mem[(nameCursor entry count).toNat]?).getD 0 = 61#8
  entryBelow : entry.toNat + count + 1 ≤ nativeFrameBase sp 80
  nameBelow : name.toNat + count ≤ nativeFrameBase sp 80
  positive : 0 < count
  small : count < 2^31
  unaligned : strncmpAlignment entry name ≠ 0#64

theorem SearchEntry.same_mem {sp env entry name count byte} {before after : Config}
    (h : SearchEntry sp env entry name count byte before) (memory : after.σ.mem = before.σ.mem) :
    SearchEntry sp env entry name count byte after := by
  refine ⟨h.frame, h.array, ?_, h.nonnull, h.envBelow, h.comparison.same_mem memory,
    h.region, ?_, h.entryBelow, h.nameBelow, h.positive, h.small, h.unaligned⟩ <;> rw [memory]
  · exact h.first
  · exact h.equals

/-- The search's save log preserves the environment word, equal prefixes and delimiter. -/
theorem SearchEntry.stack_log {sp env entry name count byte log} {before after : Config}
    (h : SearchEntry sp env entry name count byte before)
    (inside : LogInW [⟨nativeFrameBase sp 80, sp.toNat⟩] log)
    (memory : after.σ.mem = writeLog before.σ.mem log) : SearchEntry sp env entry name count byte after := by
  refine ⟨h.frame, h.array, ?_, h.nonnull, h.envBelow, ?_, h.region, ?_,
    h.entryBelow, h.nameBelow, h.positive, h.small, h.unaligned⟩
  · rw [memory, native_log_read_below before.σ.mem inside h.envBelow]
    exact h.first
  · apply h.comparison.stack_log _ _ inside memory
    · have := h.entryBelow; omega
    · have := h.nameBelow; have := h.positive; omega
  · rw [memory, frameOn_writeLog _ _ _ inside _ ⟨Or.inl ?_, trivial⟩]
    · exact h.equals
    · change (nameCursor entry count).toNat < nativeFrameBase sp 80
      rw [nameCursor_nat h.region (Nat.le_refl _)]
      have := h.entryBelow
      omega
end OCaml.Vm.Boot.Startup
