import OCaml.Vm.Primitives.Console.MlFlush

/-! The runtime statics the console-output primitives read: constant from
startup (no F1 arm or primitive writes them), so they belong to the runtime
invariant (`L.runtimeOk`), which supplies them at every `C_CALL` site. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open OCaml.Bytecode Vsa.Machine Vsa.Sim
open FdWrite (impurePtr enterHook leaveHook)

/-- The console runtime: the HTIF file table is ready and its descriptors 1
and 2 are consoles, the blocking-section hooks are the defaults,
`_impure_ptr` is `_impure_data`, no signal or action is pending, and the
channel-mutex hooks are unset. -/
structure ConsoleRuntime (c : Config) : Prop where
  stdout : ConsoleFd 1#64 c
  stderr : ConsoleFd 2#64 c
  enterHookWord : bytesVal .ld (read8 c.σ.mem enterHook.toNat) = 0x8000d2a4#64
  leaveHookWord : bytesVal .ld (read8 c.σ.mem leaveHook.toNat) = 0x8000d2a8#64
  impure : bytesVal .ld (read8 c.σ.mem impurePtr.toNat) = BitVec.ofNat 64 Layout.sym_impure_data
  clear : NoPendingSignals c.σ.mem
  quiet : bytesVal .lw (read8 c.σ.mem somethingToDo.toNat) = 0#64
  lockNull : bytesVal .ld (read8 c.σ.mem channelLock.toNat) = 0#64
  unlockNull : bytesVal .ld (read8 c.σ.mem channelUnlock.toNat) = 0#64

end OCaml.Vm.Primitives.ConsoleWrite
