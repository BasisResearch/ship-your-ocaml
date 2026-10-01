import TCB
import Vsa.Machine

/-!
# The OS boundary on bare metal: `htif.c` against the trusted OS spec

`tcb/TCB/Os` is the OS interface (a port of SibylFS for files and of
CakeML's basis model for console streams): `OsStep st call ret st'`. On
Linux it is trusted — it describes the kernel. On this bare-metal build
the "kernel" is `c/src/htif.c`, code inside the ELF, so the spec is a
proof obligation instead: `HtifFsImplements`.

The statement is about the machine: whenever the ELF enters one of its
system-call functions (`_open`, `_read`, `_write`, `_lseek`, `_close`,
`_fstat`, `_stat`, `_unlink`, `rename`, `opendir`, `readdir`, `closedir`,
`_gettimeofday`, `_times`) in a state whose in-image file system
represents the abstract state `st` (the relation `R`, over the machine's
memory), the function returns after finitely many steps with a result the
spec allows, and the new memory represents the new abstract state.

`CallConv` (how arguments and results sit in registers and memory at the
entry and return of those functions) is a parameter here; its instance is
generated from the ELF like `OCaml/Vm/Layout.lean` (PHASES F5).

The trace validation in `tcb/validation/` (RESULTS.md) is the empirical
side: `htif.c` (the file system shared with ship-your-lua, plus embedded
files and directory streams) is accepted on all 6,490 validation scripts.
-/

namespace OCaml.Os

open Vsa.Machine

/-- The calling convention of the ELF's system-call functions: the call
decoded at a function's entry, and the result read at its return. -/
structure CallConv where
  /-- `some call` iff `c` is at the entry of a system-call function with
  arguments that decode to `call` -/
  callAt : Config → Option TCB.Os.Call
  /-- `c'` is the return point of the call entered at `c` (the return
  address reached with the callee's stack frame popped) -/
  returnsTo : Config → Config → Prop
  /-- the result as the C library sees it (return value, `errno`) -/
  retOf : Config → TCB.Os.Ret

/-- **The in-image file system implements the OS spec (statement).** Where
the spec leaves a call unconstrained (`OsSpecial`, e.g. `lseek` on the
console fds, `O_TRUNC` on a directory), any result is allowed, but the call
must still return and the file system must still represent some abstract
state: `next` lists no results for those cases, so demanding an `OsStep`
there would be unsatisfiable (pointed out by ship-your-lua). -/
def HtifFsImplements (cc : CallConv) (R : Config → TCB.Os.OsState → Prop) : Prop :=
  ∀ c st call, R c st → cc.callAt c = some call →
    ∃ c' st', Steps c c' ∧ cc.returnsTo c c' ∧
      (TCB.Os.OsStep st call (cc.retOf c') st' ∨ TCB.Os.OsSpecial st call) ∧ R c' st'

/-- The C functions covered by the file-system validation driver. -/
inductive HtifFunction where
  | open | read | write | lseek | close | fstat | stat | unlink
  | rename | opendir | readdir | closedir | gettimeofday | times
  deriving DecidableEq, Repr

/-- Concrete entry classification remains an ELF calling-convention
obligation. Its addresses must be supplied by generated `Vm.Layout` symbols;
it must not be instantiated from trace results or hard-coded addresses. -/
structure HtifEntries (cc : CallConv) where
  entry : HtifFunction → Config → Prop
  covers : ∀ c call, cc.callAt c = some call → ∃ f, entry f c

/-- Named remaining machine premise, split into termination and partial
correctness for each C function. Supply these fields with generated function
summaries (`gen_fn.py`/MachWP), using the pinned ELF and a concrete FS memory
relation R. The native-C trace evidence in results/htif-fs.json validates
behaviour but does not establish either universal machine field. -/
structure HtifFunctionObligations (cc : CallConv)
    (R : Config → TCB.Os.OsState → Prop) (entries : HtifEntries cc) : Prop where
  terminates : ∀ f c st call, entries.entry f c → R c st → cc.callAt c = some call →
    ∃ c', Steps c c' ∧ cc.returnsTo c c'
  refines : ∀ f c st call c', entries.entry f c → R c st → cc.callAt c = some call →
    Steps c c' → cc.returnsTo c c' →
    ∃ st', (TCB.Os.OsStep st call (cc.retOf c') st' ∨ TCB.Os.OsSpecial st call) ∧ R c' st'

/-- Reduction of the whole HTIF boundary to the named per-function machine
obligations. This theorem deliberately does not claim those premises are
proved by the finite trace suite. -/
theorem htifFsImplements_of_functions (cc : CallConv)
    (R : Config → TCB.Os.OsState → Prop) (entries : HtifEntries cc)
    (h : HtifFunctionObligations cc R entries) : HtifFsImplements cc R := by
  intro c st call hr hc
  obtain ⟨f, hf⟩ := entries.covers c call hc
  obtain ⟨c', hs, hret⟩ := h.terminates f c st call hf hr hc
  obtain ⟨st', hspec, hr'⟩ := h.refines f c st call c' hf hr hc hs hret
  exact ⟨c', st', hs, hret, hspec, hr'⟩

end OCaml.Os
