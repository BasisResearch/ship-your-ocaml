import OCaml.Vm.Repr
import OCaml.Vm.ImageData
import Vsa.Sim.Code.FixedImage
import Vsa.Sim.GoodState
import OCaml.Vm.Boot.Startup.GprPresence
import Vsa.Sim.LibraryLayout

/-!
# Platform and fixed loop registers

These predicates contain no abstract heap placement. Relocation does not
rename any of their fields: a collector must preserve the image and control
state and re-establish the runtime invariant. `GoodState` is the existing
Sail site-lemma precondition, including `htif_done = false`.

The OCaml image is deliberately distinct from the copied WHILE image.
Only `FixedBytesLoaded`, the image-independent range predicate, is reused.
A0 library code-pin projections can be discharged from these exact bytes.
-/
namespace OCaml.Vm
open Vsa.Machine Vsa.Sim.Code

/-- The immutable sections of the pinned OCaml ELF, including the dispatch table. -/
structure ExecutableImage (c : Config) : Prop where
  text : FixedBytesLoaded Image.textBase Image.textSize Image.textByte c.σ.mem
  rodata : FixedBytesLoaded Image.rodataBase Image.rodataSize Image.rodataByte c.σ.mem

/-- Cut-point platform state, shared by startup and the dispatch loop.
The runtime parameter is `L.runtimeOk`; allocation/GC proofs must preserve it. -/
structure PlatformOk (runtimeOk : Config → Prop) (c : Config) : Prop where
  control : Vsa.Sim.GoodState c.σ
  image : ExecutableImage c
  runtime : runtimeOk c

/-- The platform's explicit running condition (already a `GoodState` field). -/
theorem PlatformOk.htif_done {runtimeOk : Config → Prop} {c : Config}
    (h : PlatformOk runtimeOk c) :
    c.σ.regs.get? LeanRV64DExecutable.Register.htif_done = some false :=
  h.control.htif_done

/-- The callee-saved registers the loop head keeps present without pinning a
value: `s10` and `s11`, which C paths spill (caml_sys_exit's and the console
primitives' prologues). The other
callee-saved registers the interpreter uses hold the VM registers, the loop
constants and the native `sp`; `s7` is the next-code pointer each dispatch
writes and pins (`DispatchPost.nextCode`). -/
def unpinnedSaved : List Nat := [26, 27]

/-- A property of both unpinned callee-saved registers. -/
theorem forall_saved {P : Nat → Prop} (h26 : P 26) (h27 : P 27) : ∀ n ∈ unpinnedSaved, P n := by
  intro n hn
  simp only [unpinnedSaved, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact h26
  · exact h27

/-- Fixed callee-saved registers established by the interpreter prologue.
The variable loop registers (pc/sp/accu/env/extra) live in `VmReprAt`.
All constants and register numbers are extracted from the pinned ELF. -/
structure LoopRegisters (c : Config) : Prop where
  dispatchTable : gpr c Layout.reg_dispatchTable = some (BitVec.ofNat 64 Layout.jumpTable)
  opcodeBound : gpr c Layout.reg_opcodeBound = some (BitVec.ofNat 64 Layout.opcodeBound)
  pending : gpr c Layout.reg_pending = some (BitVec.ofNat 64 Layout.sym_caml_something_to_do)
  domain : gpr c Layout.reg_domain = some (BitVec.ofNat 64 Layout.sym_Caml_state)
  /-- no HTIF command is half-written (the console device is idle between
  complete `tohost` commands; caml_do_exit's exit command needs it) -/
  htifIdle : c.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes = some 0#4
  /-- the unpinned callee-saved registers hold values (C paths spill them:
  caml_sys_exit's and the console primitives' prologues) -/
  saved : ∀ n ∈ unpinnedSaved, (gpr c n).isSome
  /-- the global pointer the C runtime was linked with (no arm or C path writes `gp`) -/
  gp : gpr c 3 = some Vsa.Sim.LibraryLayout.gpV

/-- Full GPR presence gives the unpinned callee-saved registers. -/
theorem _root_.OCaml.Vm.Boot.Startup.GprPresent.saved {c : Config}
    (p : OCaml.Vm.Boot.Startup.GprPresent c.σ) : ∀ n ∈ unpinnedSaved, (gpr c n).isSome := by
  intro n hn
  have b : 1 ≤ n ∧ n < 32 := by
    simp only [unpinnedSaved, List.mem_cons, List.not_mem_nil, or_false] at hn
    omega
  exact p.get n b.1 b.2

end OCaml.Vm
