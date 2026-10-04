import OCaml.Vm.Boot.Startup.CamlLocale
import OCaml.Vm.Boot.Startup.RuntimeStack
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem caml_locale_ready {H capacity sp ra s0 s2 s3 s4 before after}
    (ready : RuntimeReady H capacity (nativeStack sp Layout.camlMainFrameBytes) ra before)
    (frame : NativeFrame sp Layout.camlMainFrameBytes)
    (post : WriteRegistersPost [1] (camlLocaleLog sp s0 s2 s3 s4) before jal_80004dcc_call.link 1#64
      (camlLocaleRegs sp s0 s2 s3 s4) after) :
    RuntimeReady H capacity (nativeStack sp Layout.camlMainFrameBytes) jal_80004dcc_call.link after := by
  apply ready.stack_log post (by decide) (by simp only [camlLocaleRegs, camlLocaleParked, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ post.regs (by rfl))
    (gholds_lookup (n := 1) _ post.regs (by rfl)) (by decide) frame (camlLocaleLog_inside frame)
end OCaml.Vm.Boot.Startup
