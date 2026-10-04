import OCaml.Vm.Boot.Startup.EnvironmentInitial
import OCaml.Vm.Boot.Startup.ParameterPresentReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.MemRepr OCaml.Vm.Primitives

def parameterStack : BitVec 64 := firstMallocStack + 16#64
def parameterEnv : BitVec 64 := BitVec.ofNat 64 WhileMinImage.envArray
def parameterEntry : BitVec 64 := BitVec.ofNat 64 WhileMinImage.envEntry
def parameterByte (k : Nat) : BitVec 8 := BitVec.ofNat 8 (byteVal (parameterChars false) k)

/-- The ELF's entry characters supply the native comparison and delimiter bytes. -/
theorem EmbeddedEnvironment.entry_byte {c} (h : EmbeddedEnvironment c) (k : Nat)
    (bound : k ≤ (parameterChars false).length) :
    (c.σ.mem[parameterEntry.toNat + k]?).getD 0 = BitVec.ofNat 8 (byteVal WhileMinImage.envChars k) := by
  have length : (parameterChars false).length + 1 = WhileMinImage.envChars.length := by decide
  have lo : Layout.sym_embedded_env ≤ parameterEntry.toNat := by decide
  have hi : parameterEntry.toNat + (parameterChars false).length < WhileMinImage.envValue + 1 := by decide
  rw [h.byte _ (by omega) (by omega)]
  obtain ⟨b, pin, _, value⟩ := cstr_byte_val _ _ _ WhileMinImage.env_string k (by omega)
  change (WhileMinImage.initialMem[WhileMinImage.envEntry + k]?).getD 0 = _
  rw [pin, Option.getD_some, ← value]
  exact (BitVec.ofNat_toNat 8 b).symm

/-- The pinned embedded entry is a matching first entry for the primary name. -/
theorem EmbeddedEnvironment.search {c} (h : EmbeddedEnvironment c) (image : ExecutableImage c) :
    SearchEntry (nativeStack (nativeStack parameterStack 64) 32) parameterEnv parameterEntry
      (parameterName false) (parameterChars false).length parameterByte c := by
  have name := (parameter_name false image).bytes
  have prefixBytes (k : Nat) (bound : k < (parameterChars false).length) :
      byteVal WhileMinImage.envChars k = byteVal (parameterChars false) k := by
    have split : WhileMinImage.envChars = parameterChars false ++ ['='] := rfl
    rw [split]
    unfold byteVal
    rw [List.getElem?_append_left bound]
  constructor
  · constructor <;> decide
  · constructor <;> decide
  · have lo : Layout.sym_embedded_env ≤ parameterEnv.toNat := by decide
    have hi : parameterEnv.toNat + 8 ≤ WhileMinImage.envValue + 1 := by decide
    apply Eq.trans (word_observed _ (fun i hi' => h.byte _ (by omega) (by omega)))
    exact WhileMinImage.env_first
  · decide
  · decide
  · constructor
    · constructor <;> decide
    · constructor <;> decide
    · intro k hk
      rw [h.entry_byte k (by omega), prefixBytes k (by have := parameter_name_positive false; omega)]
      rfl
    · intro k hk
      obtain ⟨b, pin, _, value⟩ := cstr_byte_val _ _ _ name k (by have := parameter_name_positive false; omega)
      rw [pin, Option.getD_some]
      change b = BitVec.ofNat 8 (byteVal (parameterChars false) k)
      rw [← value]
      exact (BitVec.ofNat_toNat 8 b).symm
    · intro k hk eq
      obtain ⟨b, _, zero, value⟩ := cstr_byte_val _ _ _ name k (by have := parameter_name_positive false; omega)
      change BitVec.ofNat 8 (byteVal (parameterChars false) k) = 0#8 at eq
      rw [← value, BitVec.ofNat_toNat] at eq
      have := zero.mp eq
      have := parameter_name_positive false
      omega
  · constructor <;> decide
  · have atDelimiter := h.entry_byte (parameterChars false).length (Nat.le_refl _)
    have addr : (nameCursor parameterEntry (parameterChars false).length).toNat =
        parameterEntry.toNat + (parameterChars false).length := by decide
    rw [addr, atDelimiter]
    decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem EmbeddedEnvironment.value_zero {c} (h : EmbeddedEnvironment c) :
    (c.σ.mem[(parameterValuePointer parameterEntry).toNat]?).getD 0 = 0#8 := by
  have address : (parameterValuePointer parameterEntry).toNat = WhileMinImage.envValue := by decide
  rw [address, h.byte _ (by decide) (by omega)]
  have value := WhileMinImage.env_value
  have one (m : Mem) (a : Nat) : bytesT m a 1 = (m[a]?).getD 0 := by
    simp only [bytesT]
    change (0#0).append ((m[a]?).getD 0) = _
    rw [BitVec.append]
    simp
  rw [one] at value
  exact value
end OCaml.Vm.Boot.Startup
