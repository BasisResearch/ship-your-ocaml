import OCaml.Vm.Boot.Startup.MallocReturn

/-! The library model's live set (`VsaOk live`): what the allocator's machine
proofs need of it. The allocator's code is live (`AllocLive`) and the program
image is live (`ImageLive`). Startup uses all of RAM (`startupLive`); a caller
whose memory is not dense uses the image alone. -/
namespace OCaml.Vm.Boot.Startup
open VsaIris.VsaHeap OCaml.Vm.Primitives

class LibraryLive (live : Nat → Prop) : Prop where
  alloc : AllocLive live
  image : ImageLive live

instance : LibraryLive startupLive := ⟨startup_alloc_live, startup_image_live⟩

/-- Every `.text` byte is live. -/
theorem LibraryLive.text {live : Nat → Prop} [LibraryLive live] {a : Nat}
    (lo : Image.textBase ≤ a) (hi : a < Image.textBase + Image.textSize) : live a := by
  have h := (LibraryLive.image (live := live)).text (a - Image.textBase) (by omega)
  rwa [Nat.add_sub_cancel' lo] at h
end OCaml.Vm.Boot.Startup
