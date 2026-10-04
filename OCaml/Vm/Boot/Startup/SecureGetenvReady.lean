import OCaml.Vm.Boot.Startup.SecureGetenv
import OCaml.Vm.Boot.Startup.RuntimeStack
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The successful security wrapper preserves the startup allocator contract
while restoring its original caller stack and return link. -/
theorem secure_getenv_ready {H capacity sp name ra s0 s1 before after}
    (ready : RuntimeReady H capacity sp ra before) (frame : NativeFrame sp 32)
    (post : WriteRegistersPost [1, 2, 8, 9, 10] (secureLog sp ra s0 s1) before 0x80037410#64 name
      (secureTailRegs sp name ra s0 s1) after) : RuntimeReady H capacity sp ra after :=
  ready.stack_log post (by decide) (by simp only [secureTailRegs, keysG]; decide) (by decide)
    (gholds_lookup _ post.regs (by rfl)) (gholds_lookup _ post.regs (by rfl)) ready.aligned
    frame (secure_log_inside frame)
end OCaml.Vm.Boot.Startup
