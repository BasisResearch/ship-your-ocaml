import OCaml.Vm.Gc.Generated.MopupCall
import OCaml.Vm.Gc.OldifyBridge

namespace OCaml.Vm.Gc.MopupCall
open Vsa.Machine Vsa.Sim Primitives

/-- Generated suffix-field call site instantiates the shared oldify bridge. -/
def site : OldifyBridge.Site :=
  ⟨call, call_shape, call_decode, call_target, by decide, call_pins⟩

abbrev carried := OldifyBridge.carried
abbrev linked := OldifyBridge.linked site
abbrev carried_regs := @OldifyBridge.carried_regs
abbrev linked_regs := @OldifyBridge.linked_regs site
abbrev linked_input := @OldifyBridge.linked_input site
abbrev ForwardedPost := OldifyBridge.ForwardedPost site
abbrev forwarded := @OldifyBridge.forwarded site
abbrev preserved := OldifyBridge.preserved
abbrev PreservedPins := OldifyBridge.PreservedPins
abbrev preserved_pins := @OldifyBridge.preserved_pins site
abbrev abi_frame := @OldifyBridge.abi_frame site

end OCaml.Vm.Gc.MopupCall
