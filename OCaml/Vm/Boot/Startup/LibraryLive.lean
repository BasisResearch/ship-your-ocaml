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
end OCaml.Vm.Boot.Startup
