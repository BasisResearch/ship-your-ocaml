import OCaml.Bytecode.Semantics

/-! `caml_ml_out_channels_list`'s model, by name: the ids it lists and where
its fresh objects go. For each listed channel, in visiting order (newest
first), it allocates the channel's custom block and then the cons cell. -/
namespace OCaml.Vm.Primitives
open OCaml.Bytecode
set_option autoImplicit false

/-- The ids `outChannelsList` lists, in visiting order (newest first): the
open output channels. -/
def outChannelIds (w : World) : List Nat :=
  ((List.range w.chans.length).filter fun i =>
    (w.chans[i]?.map (fun c => c.isOut && c.fd != -1)).getD false).reverse

/-- One step of `outChannelsList`: the custom block, then the cons. -/
def outListStep (st : Heap × Val) (id : Nat) : Heap × Val :=
  let (h1, lc) := st.1.alloc (.channel id)
  let (h2, cell) := h1.alloc (.block 0 [.ptr lc 0, st.2])
  (h2, .ptr cell 0)

theorem outChannelsList_eq (h : Heap) (w : World) :
    outChannelsList h w = (outChannelIds w).foldl outListStep (h, .int 0) := rfl

/-- The fresh `(location, value address)` pairs: object `i` (custom blocks at
even `i`, cons cells at odd `i`) at heap location `size + i`, with its value
24 bytes per object below `young - 16`. -/
def outListPlaces (s : St) (young : BitVec 64) : List (Nat × Nat) :=
  (List.range (2 * (outChannelIds s.world).length)).map fun i =>
    (s.heap.size + i, (young - BitVec.ofNat 64 (24 * i + 16)).toNat)

end OCaml.Vm.Primitives
