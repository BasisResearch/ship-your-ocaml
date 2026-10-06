import OCaml.Vm.Boot.Startup.StrchrMiss
import OCaml.Vm.Boot.Startup.StrdupMeasure
import OCaml.Vm.Boot.WhileMinArgv
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-! The heap copy of "ocamlrun" that `open` resolves: from its nine bytes and
its alignment, the facts `strchr(·, '/')` and `strlen` consume. -/

/-- The low byte of a little-endian read is its first byte. -/
theorem bytesT_low (m : Std.ExtHashMap Nat (BitVec 8)) (a w : Nat) :
    (bytesT m a (w + 1)).toNat % 256 = ((m[a]?).getD 0).toNat := by
  have lt := ((m[a]?).getD 0).isLt
  simp only [bytesT, BitVec.toNat_cast]
  change ((bytesT m (a + 1) w) ++ ((m[a]?).getD 0)).toNat % 256 = _
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lt, Nat.shiftLeft_eq]
  omega

/-- "ocamlrun" and its NUL at `path`, 8-byte aligned. -/
structure OcamlrunName (m : Std.ExtHashMap Nat (BitVec 8)) (path : BitVec 64) : Prop where
  aligned : path.toNat % 8 = 0
  region : ReadWindow path 16
  bytes : ∀ k, k ≤ 8 → (m[path.toNat + k]?).getD 0 = BitVec.ofNat 8 (byteVal WhileMinImage.argv0Chars k)

/-- The name survives any change that keeps its nine bytes. -/
theorem OcamlrunName.transport {m m' : Std.ExtHashMap Nat (BitVec 8)} {path : BitVec 64} (h : OcamlrunName m path)
    (same : ∀ k, k ≤ 8 → (m'[path.toNat + k]?).getD 0 = (m[path.toNat + k]?).getD 0) : OcamlrunName m' path :=
  ⟨h.aligned, h.region, fun k hk => (same k hk).trans (h.bytes k hk)⟩

theorem OcamlrunName.slash {m path} (h : OcamlrunName m path) : SlashString m path 8 where
  region := ⟨h.region.lower, by have := h.region.upper; omega,
    by rcases h.region.htif with l | r; exact Or.inl (by omega); exact Or.inr r⟩
  free := fun j hj => by
    unfold strByte
    rw [h.bytes j (by omega)]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  nul := by unfold strByte; rw [h.bytes 8 (by omega)]; decide

theorem OcamlrunName.word {m path} (h : OcamlrunName m path) :
    wordAt m (nameCursor path 0) = 0x6e75726c6d61636f#64 := by
  unfold wordAt nameCursor
  rw [show path + BitVec.ofNat 64 0 = path from BitVec.add_zero path]
  have b := h.bytes
  simp only [bytesT, Nat.add_assoc]
  rw [show path.toNat = path.toNat + 0 from rfl, b 0 (by decide), b 1 (by decide), b 2 (by decide), b 3 (by decide),
    b 4 (by decide), b 5 (by decide), b 6 (by decide), b 7 (by decide)]
  decide

theorem OcamlrunName.plan {m path} (h : OcamlrunName m path) : StrchrPlan m path 8 := by
  have c0 : nameCursor path 0 = path := BitVec.add_zero path
  have nat8 : (nameCursor path (8 * 1)).toNat = path.toNat + 8 := by
    unfold nameCursor; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := h.region.upper; omega
  have win8 : ReadWindow (nameCursor path 0) 8 := by
    rw [c0]
    exact ⟨h.region.lower, by have := h.region.upper; omega,
      by rcases h.region.htif with l | r; exact Or.inl (by omega); exact Or.inr r⟩
  have run : WordRun m (nameCursor path 0) 1 := by
    rw [c0]
    refine ⟨by decide, h.region, fun i lo hi => absurd hi (by omega), ?_⟩
    apply loopTest_low_zero
    unfold wordAt
    rw [nat8, bytesT_low, h.bytes 8 (by decide)]
    decide
  exact .later 0 1 (by decide) (fun j hj => absurd hj (by omega)) (by simpa using h.aligned) win8
    (by rw [h.word]; decide) run (by decide)

theorem OcamlrunName.cbytes {m path} (h : OcamlrunName m path) : CBytes m path.toNat 8 where
  nz := fun i hi => (h.slash.free i hi).1
  nul := h.slash.nul
  lo := h.region.lower
  hi := by have := h.region.upper; omega
  htif := by
    have t := h.region.htif
    simp only [Layout.sym_tohost] at t
    rcases t with l | r
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
end OCaml.Vm.Boot.Startup
