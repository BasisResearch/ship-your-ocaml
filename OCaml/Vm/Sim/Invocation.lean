import OCaml.Vm.Primitives.MemoryFrame
import Vsa.Sim.DlHeap

/-!
# The native invocation of `caml_interprete`

Entry (`ArmSim.entry`) runs the interpreter prologue from `caml_main`'s call
and fixes, for the rest of the run, the native stack pointer and the native
words the exits read back (STOP's return through caml_interprete's and
caml_main's epilogues, `caml_sys_exit`):

* `[sp, sp + 32)`: the prologue's saved runtime values (`initial_sp_offset`,
  `initial_local_roots`, `prog`, `initial_external_raise`);
* `[sp + 200, sp + 640)`: the saved local roots, the `raise_buf` jump buffer,
  caml_interprete's callee-saved registers and caml_main's frame above it.

`[sp + 32, sp + 192)` is excluded: arm bodies spill C locals there
(`sd … 0x20(sp)` to `0xb8(sp)` in caml_interprete's body).

`Invocation D c` is frame-shaped: it says the bytes of those ranges, the
native `sp` and the `Caml_state` pointer equal the snapshot `D` taken at
entry. An arm preserves it from its write footprint alone
(`Invocation.frame`): the log misses `invocationRanges` and
`Caml_state`, and the arm restores `x2`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The preserved native ranges, as (offset from the native sp, length). -/
def invocationRanges : List (Nat × Nat) := [(0, 32), (Layout.interpSavedRootsOffset,
  Layout.interpFrameBytes + Layout.camlMainFrameBytes - Layout.interpSavedRootsOffset)]

/-- What entry fixes: the native sp at the loop head, the `Caml_state`
pointer, and the bytes of `invocationRanges` above that sp. -/
structure InvocationData where
  nativeSp : Nat
  domain : BitVec 64
  snapshot : Nat → BitVec 8

/-- **The native invocation is intact** at `c`. -/
structure Invocation (D : InvocationData) (c : Config) : Prop where
  stack : gpr c 2 = some (BitVec.ofNat 64 D.nativeSp)
  domain : word c Layout.sym_Caml_state = D.domain
  region : ∀ r ∈ invocationRanges, ∀ i < r.2, byte c (D.nativeSp + r.1 + i) = D.snapshot (D.nativeSp + r.1 + i)

/-- **The footprint obligation** of an arm: its write log misses the
preserved ranges and the `Caml_state` pointer. -/
structure InvocationOutside (D : InvocationData) (log : List WEntry) : Prop where
  domain : OutLRange log Layout.sym_Caml_state 8
  region : ∀ r ∈ invocationRanges, OutLRange log (D.nativeSp + r.1) r.2

/-- **Preservation by footprint**: bytes outside the log are unchanged and
`x2` is restored. -/
theorem Invocation.frame {D : InvocationData} {c c' : Config} {log : List WEntry}
    (h : Invocation D c) (outside : InvocationOutside D log)
    (memory : ∀ x, OutL log x → byte c' x = byte c x) (stack : gpr c' 2 = gpr c 2) :
    Invocation D c' where
  stack := stack.trans h.stack
  domain := by
    rw [← h.domain]
    exact Reloc.bytesT_congr (copied_of_outsideLog memory outside.domain)
  region r hr i hi := by
    rw [← h.region r hr i hi]
    simpa only [Nat.add_zero] using
      copied_of_outsideLog memory (outside.region r hr) i hi

/-- Exact write logs specialize the footprint frame. -/
theorem Invocation.frame_log {D : InvocationData} {c c' : Config} {log : List WEntry}
    (h : Invocation D c) (outside : InvocationOutside D log)
    (memory : c'.σ.mem = writeLog c.σ.mem log) (stack : gpr c' 2 = gpr c 2) :
    Invocation D c' :=
  h.frame outside (fun x hx => by rw [byte_total, byte_total, memory, writeLog_out _ _ _ hx]) stack

/-- A read-only run (memory unchanged) preserves the invocation. -/
theorem Invocation.frame_read {D : InvocationData} {c c' : Config}
    (h : Invocation D c) (memory : c'.σ.mem = c.σ.mem) (stack : gpr c' 2 = gpr c 2) :
    Invocation D c' :=
  h.frame (log := []) ⟨trivial, fun _ _ => trivial⟩
    (fun x _ => by simp only [byte, memory]) stack

/-- What the exits (STOP, caml_sys_exit) need from the entry snapshot: the
native frames lie above the allocator arena and below the stack top, and the
saved return addresses of caml_interprete (into caml_main) and of caml_main
(into main) are the ones startup installed. D-only: preserved trivially. -/
structure NativeValid (D : InvocationData) : Prop where
  low : Vsa.Sim.DlHeap.heapEnd ≤ D.nativeSp
  high : D.nativeSp + Layout.interpFrameBytes + Layout.camlMainFrameBytes ≤ Layout.sym_stack_top
  aligned : D.nativeSp % 16 = 0
  interpReturn : ∀ c, Invocation D c → word c (D.nativeSp + Layout.interpSaveOffset 1) = 0x80004ff8#64
  mainReturn : ∀ c, Invocation D c →
    word c (D.nativeSp + Layout.interpFrameBytes + Layout.camlMainSaveOffset 1) = 0x80001df0#64

/-- The native invocation at a loop-head configuration: some entry snapshot
that is intact and valid (`Running.native`). -/
def NativePlaced (c : Config) : Prop := ∃ D, Invocation D c ∧ NativeValid D

end OCaml.Vm.Sim
