import OCaml.Vm.Primitives.Named.NamedTransport
import OCaml.Vm.Platform

/-!
# The C strings of `caml_fatal_uncaught_exception`

The two `caml_named_value` keys are NUL-terminated strings in `.rodata`.
`RodataString off name` checks the image's bytes once (`decide +kernel`), and
`rodata_nameAt` turns that check into the lookup's `NameAt` premise in any
state whose image is loaded.
-/

namespace OCaml.Vm.Primitives.Uncaught.FatalUncaught
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives
open Vsa.MemRepr
open OCaml.Vm.Primitives.Named.NamedValue (NameAt strOf)

/-- `name`, then a NUL, at `.rodata` offset `off`; no byte of `name` is NUL. -/
def RodataString (off : Nat) (name : List (BitVec 8)) : Prop :=
  off + name.length < Image.rodataSize ∧
    (List.range name.length).all (fun i => Image.rodataByte (off + i) == name.getD i 0 && name.getD i 0 != 0 &&
      decide ((name.getD i 0).toNat < 256)) = true ∧
    Image.rodataByte (off + name.length) = 0#8

instance (off : Nat) (name : List (BitVec 8)) : Decidable (RodataString off name) := by
  unfold RodataString; infer_instance

/-- **A `.rodata` string is a `NameAt` fact** in any state with the image loaded. -/
theorem rodata_nameAt {c : Config} (image : ExecutableImage c) {off : Nat} {name : List (BitVec 8)}
    (h : RodataString off name) : NameAt c.σ.mem (BitVec.ofNat 64 (Image.rodataBase + off)) name := by
  obtain ⟨fits, all, nul⟩ := h
  have size : Image.rodataBase + Image.rodataSize ≤ Layout.sym_tohost := by decide
  have base : Image.rodataBase = 0x80053180 := rfl
  have addr (i : Nat) (hi : i ≤ name.length) :
      (BitVec.ofNat 64 (Image.rodataBase + off) + BitVec.ofNat 64 i).toNat = Image.rodataBase + (off + i) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [Image.rodataSize, Layout.sym_tohost] at fits size
    omega
  have each (i : Nat) (hi : i < name.length) :
      Image.rodataByte (off + i) = name[i] ∧ name[i] ≠ 0#8 := by
    have := List.all_eq_true.1 all i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some] at this
    exact ⟨this.1.1, this.1.2⟩
  have byte (i : Nat) (hi : i ≤ name.length) :
      (c.σ.mem[(BitVec.ofNat 64 (Image.rodataBase + off) + BitVec.ofNat 64 i).toNat]?).getD 0 =
        Image.rodataByte (off + i) := by
    rw [addr i hi, image.rodata (off + i) (by omega)]; rfl
  refine ⟨fun i hi => (byte i (Nat.le_of_lt hi)).trans (each i hi).1, fun i hi => (each i hi).2,
    (byte _ (Nat.le_refl _)).trans nul, fun i hi => ⟨?_, ?_, Or.inl ?_⟩⟩ <;>
    rw [addr i hi] <;> simp only [Image.rodataBase, Image.rodataSize, Layout.sym_tohost] at fits size ⊢ <;> omega

/-- A C string from its bytes, present in memory. -/
theorem cstr_of_bytes {m : Mem} : ∀ (l : List (BitVec 8)) (a : Nat),
    (∀ i (hi : i < l.length), m[a + i]? = some l[i] ∧ l[i] ≠ 0#8 ∧ l[i].toNat < 256) → m[a + l.length]? = some 0#8 →
    CStr m a (l.map fun b => Char.ofNat b.toNat)
  | [], a, _, nul => .nil nul
  | b :: l, a, bytes, nul => by
    obtain ⟨hb, ne, lt⟩ := bytes 0 (by simp)
    refine .cons (by simpa using hb) (by simpa using ne) (by simpa using lt) (cstr_of_bytes l (a + 1) (fun i hi => ?_) ?_)
    · have := bytes (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    · simpa [Nat.add_assoc, Nat.add_comm 1 l.length] using nul

/-- **A `.rodata` string is a `CString`** in any state with the image loaded. -/
theorem rodata_cstring {m : Mem}
    (rodata : Vsa.Sim.Code.FixedBytesLoaded Image.rodataBase Image.rodataSize Image.rodataByte m) {off : Nat}
    {name : List (BitVec 8)} (h : RodataString off name) : CString m (Image.rodataBase + off) (strOf name) := by
  obtain ⟨fits, all, nul⟩ := h
  refine ⟨_, cstr_of_bytes name _ (fun i hi => ?_) ?_, rfl⟩
  · have := List.all_eq_true.1 all i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some] at this
    refine ⟨?_, this.1.2, this.2⟩
    rw [Nat.add_assoc, rodata (off + i) (by omega), this.1.1]
  · rw [Nat.add_assoc, rodata _ fits, nul]

/-- `"Printexc.handle_uncaught_exception"`, `caml_fatal_uncaught_exception`'s first key. -/
def handlerName : List (BitVec 8) :=
  [0x50#8, 0x72#8, 0x69#8, 0x6e#8, 0x74#8, 0x65#8, 0x78#8, 0x63#8, 0x2e#8, 0x68#8, 0x61#8, 0x6e#8, 0x64#8,
   0x6c#8, 0x65#8, 0x5f#8, 0x75#8, 0x6e#8, 0x63#8, 0x61#8, 0x75#8, 0x67#8, 0x68#8, 0x74#8, 0x5f#8, 0x65#8,
   0x78#8, 0x63#8, 0x65#8, 0x70#8, 0x74#8, 0x69#8, 0x6f#8, 0x6e#8]

/-- `"Pervasives.do_at_exit"`, the second key. -/
def atExitName : List (BitVec 8) :=
  [0x50#8, 0x65#8, 0x72#8, 0x76#8, 0x61#8, 0x73#8, 0x69#8, 0x76#8, 0x65#8, 0x73#8, 0x2e#8, 0x64#8, 0x6f#8,
   0x5f#8, 0x61#8, 0x74#8, 0x5f#8, 0x65#8, 0x78#8, 0x69#8, 0x74#8]

/-- The keys' `.rodata` offsets: `0x80056570` and `0x80055770`. -/
theorem handlerName_rodata : RodataString 13296 handlerName := by decide +kernel
theorem atExitName_rodata : RodataString 9712 atExitName := by decide +kernel

theorem handlerName_at {c : Config} (image : ExecutableImage c) : NameAt c.σ.mem 0x80056570#64 handlerName :=
  rodata_nameAt image handlerName_rodata

theorem atExitName_at {c : Config} (image : ExecutableImage c) : NameAt c.σ.mem 0x80055770#64 atExitName :=
  rodata_nameAt image atExitName_rodata

end OCaml.Vm.Primitives.Uncaught.FatalUncaught
