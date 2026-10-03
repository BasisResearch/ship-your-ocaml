import OCaml.Vm.Boot.Startup.WhileMinToMalloc
import Vsa.Sim.LibraryLoadValue
import VsaIris.Vsa.SymRun
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.Boot Vsa.MemRepr OCaml.Vm.Primitives

/-- Presence is needed only at the bytes of this library read, not throughout memory. -/
theorem readLE_exists_of_present (m : Mem) (a n : Nat)
    (present : ∀ i < n, (m[a + i]?).isSome) : ∃ v, readLE m a n = some v := by
  induction n generalizing a with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (present 0 (by omega))
    obtain ⟨v, hv⟩ := ih (a + 1) (fun i hi => by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using present (i + 1) (by omega))
    exact ⟨b.toNat + 256 * v, by simp [readLE, show m[a]? = some b from by simpa using hb, hv]⟩

/-- Bridge bounded total-read certificates to the allocator library's partial reads. -/
theorem read64_of_word {m : Mem} {a : Nat} {v : BitVec 64}
    (present : ∀ i < 8, (m[a + i]?).isSome) (word : bytesT m a 8 = v) :
    read64 m a = some v.toNat := by
  obtain ⟨n, hn⟩ := readLE_exists_of_present m a 8 present
  have bound := read64_lt_eg4 m a n hn
  have value := execRetEpilogueWord_value m a (BitVec.ofNat 64 n)
    (by simpa only [read64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using hn)
  change bytesVal .ld (read8 m a) = _ at value
  rw [read8_value, word] at value
  have eq := congrArg BitVec.toNat value
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at eq
  exact hn.trans (congrArg some eq.symm)

/-- BSS clearing never removes an already present byte. -/
theorem clearWords_present (m : Mem) (base n a : Nat) (present : (m[a]?).isSome) :
    ((clearWords m base n)[a]?).isSome := by
  induction n with
  | zero => exact present
  | succ n ih => exact VsaIris.Inst.writeLog_present _ _ _ ih

/-- Dense RAM remains available for the allocator after the abstract startup effects. -/
theorem CrtCamlMainPost.present {initial c : Config} (post : CrtCamlMainPost initial c)
    (a : Nat) (present : (initial.σ.mem[a]?).isSome) : (c.σ.mem[a]?).isSome := by
  rw [post.memory]
  exact VsaIris.Inst.writeLog_present _ _ _ (clearWords_present _ _ _ _ present)
end OCaml.Vm.Boot.Startup
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.Boot Vsa.MemRepr Startup OCaml.Vm.Primitives
open VsaIris.Sym

/-- The native saves before malloc preserve every word below their stack frame. -/
theorem ResetMallocWitness.read_frame {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc)
    (a : Nat) (below : a + 8 ≤ Layout.sym_stack_top - 136) :
    read64 atMalloc.σ.mem a = read64 atMain.σ.mem a := by
  rw [w.post.memory, w.alloc.post.memory, w.alloc.domain.post.memory]
  rw [read64_logOut, read64_logOut]
  · intro i hi
    exact outL_of_range (camlMainLog_below _ _ a (by omega)) (by omega) (by omega)
  · intro i hi
    change (a + i < Layout.sym_stack_top - 136 ∨ _) ∧ True
    exact ⟨Or.inl (by omega), True.intro⟩

/-- The totalized reset memory remains present throughout the proved startup prefix. -/
theorem ResetMallocWitness.main_present {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc)
    (a : Nat) (lo : Vsa.Densify.ramBase ≤ a) (hi : a < Vsa.Densify.ramBase + Vsa.Densify.ramSize) :
    (atMain.σ.mem[a]?).isSome := by
  apply w.alloc.domain.main.post.toCrtCamlMainPost.present
  change ((Vsa.Densify.fillZeroMem initial.σ.mem)[a]?).isSome
  rw [Vsa.Densify.fillZeroMem_ram _ lo hi]
  rfl

theorem ResetMallocWitness.present {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc)
    (a : Nat) (lo : Vsa.Densify.ramBase ≤ a) (hi : a < Vsa.Densify.ramBase + Vsa.Densify.ramSize) :
    (atMalloc.σ.mem[a]?).isSome := by
  rw [w.post.memory, w.alloc.post.memory, w.alloc.domain.post.memory]
  exact VsaIris.Inst.writeLog_present _ _ _
    (VsaIris.Inst.writeLog_present _ _ _ (w.main_present a lo hi))

/-- Convert an immutable loader word certificate at the actual first malloc entry. -/
theorem ResetMallocWitness.initial_read {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc)
    (a : Nat) (v : BitVec 64) (lo : Vsa.Densify.ramBase ≤ a)
    (beforeBss : a + 8 ≤ Layout.sym_bss_start)
    (envOutside : a + 8 ≤ Layout.sym_environ ∨ Layout.sym_environ + 8 ≤ a)
    (word : bytesT WhileMinImage.initialMem a 8 = v) :
    read64 atMalloc.σ.mem a = some v.toNat := by
  have bounds : Layout.sym_bss_start ≤ Layout.sym_stack_top - 136 ∧
      Layout.sym_bss_start ≤ Vsa.Densify.ramBase + Vsa.Densify.ramSize := by decide
  rw [w.read_frame a (by omega)]
  apply read64_of_word (fun i hi => w.main_present (a + i) (by omega) (by omega))
  rw [w.alloc.domain.main.post.toCrtCamlMainPost.bytes_below a 8 beforeBss (by
    intro i hi
    rcases envOutside with below | above
    · exact mainWrites_before _ _ _ (by omega) (by omega)
    · exact mainWrites_between _ _ _ (by omega) (by omega))]
  have eqv := bytesT_memEqv (fun b => (Vsa.Densify.memEqv_fillZeroMem initial.σ.mem b).symm) a 8
  exact eqv.trans ((congrArg (fun m => bytesT m a 8)
    (w.alloc.domain.main.reset.memory.trans loaded_memory)).trans word)

/-- Every complete BSS word is still zero at the first allocator call. -/
theorem ResetMallocWitness.bss_read {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc)
    (a : Nat) (lo : Layout.sym_bss_start ≤ a)
    (hi : a + 8 ≤ Layout.sym_bss_start + 8 * bssWords) :
    read64 atMalloc.σ.mem a = some 0 := by
  have bounds : Vsa.Densify.ramBase ≤ Layout.sym_bss_start ∧
      Layout.sym_environ + 8 ≤ Layout.sym_bss_start ∧
      Layout.sym_bss_start + 8 * bssWords ≤ Layout.sym_stack_top - 136 ∧
      Layout.sym_bss_start + 8 * bssWords ≤ Vsa.Densify.ramBase + Vsa.Densify.ramSize := by decide
  rw [w.read_frame a (by omega)]
  apply read64_of_word (v := 0#64) (fun i h => w.main_present (a + i) (by omega) (by omega))
  rw [bytesT_eight_eq]
  exact bytesT8_of_lpins8 (w.alloc.domain.main.post.toCrtCamlMainPost.bss_pins a lo hi (by
    intro i h
    exact mainWrites_between _ _ _ (by omega) (by omega)))
end OCaml.Vm.Boot.WhileMinElfParse
