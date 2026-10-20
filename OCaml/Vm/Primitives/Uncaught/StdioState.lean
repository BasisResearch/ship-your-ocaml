import OCaml.Vm.Primitives.Uncaught.StdioFclose
import VsaIris.Vsa.HeapShape

/-!
# newlib's stdio at exit

The state `exit`'s stdio handler needs (`StdioAtExit`): the glue `__sglue`
of the three standard streams, `_impure_data`'s `__cleanup`, and each
stream's fields (`StdStream`). Every byte read is a low global outside the
allocator's state (`StdioReads.low`), so the fact moves along anything that
keeps those (`StdioAtExit.transport`).
-/

namespace OCaml.Vm.Primitives.Uncaught.StdioState
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives
open OCaml.Vm.Primitives.Uncaught.StdioClose (fdSlot FdLive)
open OCaml.Vm.Primitives.Uncaught.StdioFclose (scloseFn fdLive_of_read)
open OCaml.Vm.Primitives.Uncaught.StdioFlush (stdinFile stdoutFile stderrFile)

/-- `_impure_data`, newlib's reentrancy structure. -/
def impure : BitVec 64 := 0x80064668#64
/-- `__sglue`, the glue of the three standard streams. -/
def sglue : BitVec 64 := 0x800643a0#64

/-- **A standard stream at exit**: flags, descriptor, no lock flag, closed by
`__sclose` on itself, no buffers, a live console descriptor. -/
structure StdStream (m : Std.ExtHashMap Nat (BitVec 8)) (fp fd flags : BitVec 64) : Prop where
  flagsAt : bytesVal .lh (read8 m (fp + 16#64).toNat) = flags
  fileAt : bytesVal .lh (read8 m (fp + 18#64).toNat) = fd
  flags2 : bytesVal .lw (read8 m (fp + 176#64).toNat) &&& 1#64 = 0#64
  close : bytesVal .ld (read8 m (fp + 80#64).toNat) = scloseFn
  cookie : bytesVal .ld (read8 m (fp + 48#64).toNat) = fp
  ub : bytesVal .ld (read8 m (fp + 88#64).toNat) = 0#64
  lb : bytesVal .ld (read8 m (fp + 120#64).toNat) = 0#64
  slot : FdLive m fd

/-- **newlib's stdio at exit**: one glue of three streams (stdin read-only and
never read, stdout never written, stderr unbuffered with nothing pending),
and `__cleanup` set. Supplied by the state `fprintf(stderr, …)` leaves
(`FprintfReport`). -/
structure StdioAtExit (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  next : bytesVal .ld (read8 m sglue.toNat) = 0#64
  niobs : bytesVal .lw (read8 m (sglue + 8#64).toNat) = 3#64
  iobs : bytesVal .ld (read8 m (sglue + 16#64).toNat) = stdinFile
  cleanup : bytesVal .ld (read8 m (impure + 72#64).toNat) ≠ 0#64
  stdin : StdStream m stdinFile 0#64 4#64
  stdout : StdStream m stdoutFile 1#64 9#64
  stderr : StdStream m stderrFile 2#64 0x201a#64
  stdinR : bytesVal .lw (read8 m (stdinFile + 8#64).toNat) = 0#64
  stdinUR : bytesVal .lw (read8 m (stdinFile + 112#64).toNat) = 0#64
  stdoutBase : bytesVal .ld (read8 m (stdoutFile + 24#64).toNat) = 0#64
  stderrBase : bytesVal .ld (read8 m (stderrFile + 24#64).toNat) ≠ 0#64
  stderrPos : bytesVal .ld (read8 m stderrFile.toNat) = bytesVal .ld (read8 m (stderrFile + 24#64).toNat)

/-- The words a stream's close reads. -/
def StreamReads (fp fd : BitVec 64) (a : Nat) : Prop :=
  a = (fp + 16#64).toNat ∨ a = (fp + 18#64).toNat ∨ a = (fp + 176#64).toNat ∨ a = (fp + 80#64).toNat ∨
    a = (fp + 48#64).toNat ∨ a = (fp + 88#64).toNat ∨ a = (fp + 120#64).toNat ∨ a = (0x80064918#64).toNat ∨
    a = (fdSlot fd).toNat

theorem StdStream.transport {m m' : Std.ExtHashMap Nat (BitVec 8)} {fp fd flags : BitVec 64}
    (h : StdStream m fp fd flags) (r : ∀ a, StreamReads fp fd a → read8 m' a = read8 m a) : StdStream m' fp fd flags where
  flagsAt := by rw [r _ (Or.inl rfl)]; exact h.flagsAt
  fileAt := by rw [r _ (Or.inr (Or.inl rfl))]; exact h.fileAt
  flags2 := by rw [r _ (Or.inr (Or.inr (Or.inl rfl)))]; exact h.flags2
  close := by rw [r _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact h.close
  cookie := by rw [r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact h.cookie
  ub := by rw [r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))]; exact h.ub
  lb := by rw [r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))]; exact h.lb
  slot := fdLive_of_read h.slot (r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
    (r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))

/-- The glue's, `reent`'s and the flushes' words `StdioAtExit` reads. -/
def stdioWords : List Nat :=
  [sglue.toNat, (sglue + 8#64).toNat, (sglue + 16#64).toNat, (impure + 72#64).toNat, (stdinFile + 8#64).toNat,
    (stdinFile + 112#64).toNat, (stdoutFile + 24#64).toNat, (stderrFile + 24#64).toNat, stderrFile.toNat]

/-- Every word `StdioAtExit` reads. -/
def StdioReads (a : Nat) : Prop :=
  a ∈ stdioWords ∨ StreamReads stdinFile 0#64 a ∨ StreamReads stdoutFile 1#64 a ∨ StreamReads stderrFile 2#64 a

/-- They are low globals, outside the allocator's state. -/
theorem StdioReads.low {a : Nat} (h : StdioReads a) :
    ∀ i, i < 8 → a + i < Vsa.Sim.DlHeap.heapStart ∧ ¬ VsaIris.VsaHeap.allocGlobal (a + i) := by
  unfold VsaIris.VsaHeap.allocGlobal VsaIris.VsaHeap.InRange Vsa.Sim.DlHeap.heapStart
  rcases h with h | h | h | h
  · simp only [stdioWords, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  all_goals rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem StdioAtExit.transport {m m' : Std.ExtHashMap Nat (BitVec 8)} (h : StdioAtExit m)
    (r : ∀ a, StdioReads a → read8 m' a = read8 m a) : StdioAtExit m' :=
  have w (a : Nat) (ha : a ∈ stdioWords) : read8 m' a = read8 m a := r a (Or.inl ha)
  { next := by rw [w _ (by decide)]; exact h.next
    niobs := by rw [w _ (by decide)]; exact h.niobs
    iobs := by rw [w _ (by decide)]; exact h.iobs
    cleanup := by rw [w _ (by decide)]; exact h.cleanup
    stdin := h.stdin.transport fun a ha => r a (Or.inr (Or.inl ha))
    stdout := h.stdout.transport fun a ha => r a (Or.inr (Or.inr (Or.inl ha)))
    stderr := h.stderr.transport fun a ha => r a (Or.inr (Or.inr (Or.inr ha)))
    stdinR := by rw [w _ (by decide)]; exact h.stdinR
    stdinUR := by rw [w _ (by decide)]; exact h.stdinUR
    stdoutBase := by rw [w _ (by decide)]; exact h.stdoutBase
    stderrBase := by rw [w _ (by decide)]; exact h.stderrBase
    stderrPos := by
      rw [w stderrFile.toNat (by decide), w (stderrFile + 24#64).toNat (by decide)]
      exact h.stderrPos }

end OCaml.Vm.Primitives.Uncaught.StdioState
