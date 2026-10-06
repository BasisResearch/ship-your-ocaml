import OCaml.Bytecode.Semantics

/-! The world side of console output: the OS model selects the complete write
on an output stream, so flushing a channel whose descriptor is stdout or
stderr appends its buffer to the console. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open OCaml.Bytecode

/-- The OS model's selected `write` on an output stream is complete. -/
theorem osCall_write_stream {os : TCB.Os.OsState} {fd : Nat} {st : TCB.Os.Stream} {b : List UInt8}
    (live : os.proc.exited = none) (h : TCB.Os.lookupFd os fd = some (.stream st)) (out : st ≠ .stdin) :
    osCall os (.write fd b b.length) =
      some (.num b.length, { os with streams := os.streams.doWrite st b }) := by
  cases st with
  | stdin => exact absurd rfl out
  | stdout =>
    simp [osCall, osReturn, TCB.Os.outs, TCB.Os.osWrite, h, TCB.Os.Streams.writeLengths, TCB.Os.allowed,
      TCB.Os.next, live, TCB.Os.Ret.matches, List.range_succ]
    rw [List.findSome?_eq_none_iff.mpr ?_]
    · rfl
    · intro k hk
      simp only [List.mem_range] at hk
      simp only [Function.comp]
      split
      · rename_i heq; simp at heq; omega
      · rfl
  | stderr =>
    simp [osCall, osReturn, TCB.Os.outs, TCB.Os.osWrite, h, TCB.Os.Streams.writeLengths, TCB.Os.allowed,
      TCB.Os.next, live, TCB.Os.Ret.matches, List.range_succ]
    rw [List.findSome?_eq_none_iff.mpr ?_]
    · rfl
    · intro k hk
      simp only [List.mem_range] at hk
      simp only [Function.comp]
      split
      · rename_i heq; simp at heq; omega
      · rfl

/-- The world after a flush of a channel whose descriptor is an output stream. -/
def flushedWorld (w : World) (id : Nat) (c : Chan) (st : TCB.Os.Stream) : World :=
  ({ w with os := { w.os with streams := w.os.streams.doWrite st c.buf } } : World).setChan id
    { c with buf := [], offset := c.offset + c.buf.length }

/-- `caml_flush` of a channel on stdout or stderr writes its buffer whole. -/
theorem flushChan_stream {w : World} {id : Nat} {c : Chan} {st : TCB.Os.Stream}
    (hc : w.chans[id]? = some c) (fdNonneg : 0 ≤ c.fd) (live : w.os.proc.exited = none)
    (stream : TCB.Os.lookupFd w.os c.fd.toNat = some (.stream st)) (out : st ≠ .stdin)
    (isOut : c.isOut = true) (fits : offsetFits c c.buf.length = true) :
    flushChan w id = some (flushedWorld w id c st) := by
  have ne : c.fd ≠ -1 := by omega
  have nlt : ¬ c.fd < 0 := by omega
  simp [flushChan, writeFd, hc, ne, nlt, isOut, fits, osCall_write_stream live stream out, flushedWorld]

/-- The flushed buffer is appended to the console. -/
theorem flushedWorld_console (w : World) (id : Nat) (c : Chan) {st : TCB.Os.Stream} (out : st ≠ .stdin) :
    (flushedWorld w id c st).console = w.console ++ c.buf := by
  cases st with
  | stdin => exact absurd rfl out
  | stdout => rfl
  | stderr => rfl

/-- The world after a whole write `b` to an output stream. -/
def wroteWorld (w : World) (st : TCB.Os.Stream) (b : List UInt8) : World :=
  { w with os := { w.os with streams := w.os.streams.doWrite st b } }

/-- A write of `b` on a console descriptor completes. -/
theorem writeFd_stream {w : World} {fd : Int} {b : List UInt8} {st : TCB.Os.Stream}
    (fdNonneg : 0 ≤ fd) (live : w.os.proc.exited = none)
    (stream : TCB.Os.lookupFd w.os fd.toNat = some (.stream st)) (out : st ≠ .stdin) :
    writeFd w fd b = some (wroteWorld w st b) := by
  have nlt : ¬ fd < 0 := by omega
  simp [writeFd, nlt, osCall_write_stream live stream out, wroteWorld]

/-- The written bytes are appended to the console. -/
theorem wroteWorld_console (w : World) (b : List UInt8) {st : TCB.Os.Stream} (out : st ≠ .stdin) :
    (wroteWorld w st b).console = w.console ++ b := by
  cases st with
  | stdin => exact absurd rfl out
  | stdout => rfl
  | stderr => rfl

end OCaml.Vm.Primitives.ConsoleWrite
