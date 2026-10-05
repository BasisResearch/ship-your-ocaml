import OCaml.Vm.Boot.Startup.SearchExePathNormalized
import OCaml.Vm.Boot.Startup.SearchExePathCallInterface
import OCaml.Vm.Boot.Startup.PathName
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Total byte of a certified C string. -/
theorem cstr_getD {m : Vsa.MemRepr.Mem} {p : Nat} {cs : List Char} (h : Vsa.MemRepr.CStr m p cs)
    (k : Nat) (hk : k < cs.length) : (m[p + k]?).getD 0 = BitVec.ofNat 8 (byteVal cs k) := by
  obtain ⟨b, pin, -, val⟩ := cstr_byte_val m p cs h k (Nat.le_of_lt hk)
  rw [pin, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  rw [BitVec.toNat_ofNat, ← val, Nat.mod_eq_of_lt this]

/-- `caml_search_exe_in_path` calls `getenv("PATH")`. -/
theorem search_exe_path (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) :
    FnSummary 0x80025550#64 (fun d => d = c)
      (WriteRegistersPost [10, 1] [] c jal_80025558_call.target pathName0
        [(1, jal_80025558_call.link), (10, pathName0)]) := by
  have front : FnSummary 0x80025550#64 (fun d => d = c)
      (WriteRegistersPost [10] [] c jal_80025558_call.pc pathName0 [(10, pathName0)]) := by
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput searchExePathSave 0x80025550#64 [] [] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := trivial
        keys := by decide
        shape := by decide
        tick := leaf.tick
        facts := by
          have code := searchExePath_code leaf.image
          chain_facts code with "Vsa.Sim.Code.caml_search_exe_in_path_at_" }))
    · rfl
    · rfl
    · decide
    · decide
    · decide
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  obtain ⟨after, run2, called⟩ := (call_registers_summary jal_80025558_call_shape jal_80025558_call_decode request
    (jal_80025558_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ setup.regs
    (by decide) (by simp only [KeysAvoidRa, keysG]; decide) (by rfl)).run request ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩
end OCaml.Vm.Boot.Startup
