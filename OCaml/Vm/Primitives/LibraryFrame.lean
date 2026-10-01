import OCaml.Vm.Primitives.LocalRunBridge
import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Primitives.ImageFrame

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim Vsa.Sim.Code VsaIris.Inst LeanRV64DExecutable

/-- A total observation plus presence determines the optional value. -/
theorem some_of_observed {α : Type} {x : Option α} {zero value : α}
    (present : x.isSome) (observed : x.getD zero = value) : x = some value := by
  cases x with
  | none => cases present
  | some v => exact congrArg some observed

/-- The library well-formedness invariant supplies the PC's presence. -/
theorem library_pc {live c pc} (good : VsaOk live c)
    (observed : (vsaModel live).reg c VsaIris.PC = pc) : OCaml.Vm.pcOf c = some pc := by
  obtain ⟨old, present⟩ := good.good.PC
  apply some_of_observed (zero := 0) (by change (c.σ.regs.get? Register.PC).isSome = true; rw [present]; rfl)
  exact observed

/-- Recover an ABI register from a library model observation. -/
theorem library_gpr {live c r value} (good : VsaOk live c)
    (lower : 1 ≤ r) (upper : r ≤ 31)
    (observed : (vsaModel live).reg c r = value) : gpr c r = some value := by
  apply some_of_observed (zero := 0) (good.gpr r lower upper)
  change (if r = VsaIris.PC then _ else _) = value at observed
  rw [if_neg (by change r ≠ 32; omega)] at observed
  exact observed

/-- Convert total register agreement back to the generator's option frame. -/
theorem library_register_frame {live before after r} (pre : VsaOk live before)
    (post : VsaOk live after) (lower : 1 ≤ r) (upper : r ≤ 31)
    (observed : (vsaModel live).reg after r = (vsaModel live).reg before r) :
    gpr after r = gpr before r :=
  (library_gpr post lower upper observed).trans (library_gpr pre lower upper rfl).symm

/-- Primitive dispatch observes words, so total-byte equality frames its bindings. -/
theorem bindings_observed {P before after} (h : PrimitiveBindings P before)
    (memory : Vsa.Densify.MemEqv after.σ.mem before.σ.mem) : PrimitiveBindings P after :=
  h.of_words fun a => Vsa.Sim.Boot.bytesT_memEqv memory a 8

/-- The library's live-memory set includes both immutable ELF sections. -/
structure ImageLive (live : Nat → Prop) : Prop where
  text : ∀ i, i < Image.textSize → live (Image.textBase + i)
  rodata : ∀ i, i < Image.rodataSize → live (Image.rodataBase + i)

/-- Presence recovers exact code pins from equality of total byte reads. -/
theorem fixedBytes_observed {base size bytes m m'}
    (image : FixedBytesLoaded base size bytes m)
    (memory : Vsa.Densify.MemEqv m' m)
    (present : ∀ i, i < size → (m'[base + i]?).isSome) :
    FixedBytesLoaded base size bytes m' := by
  intro i hi
  apply some_of_observed (zero := 0) (present i hi)
  have same : (m'[base + i]?).getD 0 = (m[base + i]?).getD 0 := memory _
  rw [same, image i hi]
  rfl

/-- Restore the generator's executable-image input after a library call. -/
theorem image_observed {live c c'} (image : ExecutableImage c)
    (good : VsaOk live c') (liveImage : ImageLive live)
    (memory : Vsa.Densify.MemEqv c'.σ.mem c.σ.mem) : ExecutableImage c' :=
  ⟨fixedBytes_observed image.text memory (fun i hi => good.live _ (liveImage.text i hi)),
   fixedBytes_observed image.rodata memory (fun i hi => good.live _ (liveImage.rodata i hi))⟩

/-- A library's mutable footprint excludes both immutable ELF sections. -/
structure ImageSeparate (S : Nat → Prop) : Prop where
  text : ∀ i, i < Image.textSize → ¬ S (Image.textBase + i)
  rodata : ∀ i, i < Image.rodataSize → ¬ S (Image.rodataBase + i)

/-- Recover exact code pins after a confined library write. -/
theorem image_local {live S c c'} (image : ExecutableImage c)
    (good : VsaOk live c') (liveImage : ImageLive live) (outside : ImageSeparate S)
    (memory : ∀ a, ¬ S a → (vsaModel live).mem c' a = (vsaModel live).mem c a) :
    ExecutableImage c' := by
  constructor
  · intro i hi
    apply some_of_observed (zero := 0) (good.live _ (liveImage.text i hi))
    have agree := memory _ (outside.text i hi)
    change (c'.σ.mem[Image.textBase + i]?).getD 0 = (c.σ.mem[Image.textBase + i]?).getD 0 at agree
    rw [agree, image.text i hi]
    rfl
  · intro i hi
    apply some_of_observed (zero := 0) (good.live _ (liveImage.rodata i hi))
    have agree := memory _ (outside.rodata i hi)
    change (c'.σ.mem[Image.rodataBase + i]?).getD 0 = (c.σ.mem[Image.rodataBase + i]?).getD 0 at agree
    rw [agree, image.rodata i hi]
    rfl

end OCaml.Vm.Primitives
