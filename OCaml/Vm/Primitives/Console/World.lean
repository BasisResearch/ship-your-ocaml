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

/-- A console write keeps the descriptor table and the process state. -/
theorem wroteWorld_lookupFd (w : World) (st : TCB.Os.Stream) (b : List UInt8) (fd : Nat) :
    TCB.Os.lookupFd (wroteWorld w st b).os fd = TCB.Os.lookupFd w.os fd := rfl

theorem wroteWorld_exited (w : World) (st : TCB.Os.Stream) (b : List UInt8) :
    (wroteWorld w st b).os.proc.exited = w.os.proc.exited := rfl

theorem wroteWorld_chans (w : World) (st : TCB.Os.Stream) (b : List UInt8) :
    (wroteWorld w st b).chans = w.chans := rfl

/-- `caml_putblock` with room: the bytes are appended to the buffer. -/
theorem putBlock_room {w : World} {id fuel : Nat} {bs : List UInt8} {c : Chan}
    (hc : w.chans[id]? = some c) (fd0 : 0 ≤ c.fd) (out : c.isOut = true) (ne : bs ≠ [])
    (room : bs.length < ioBufferSize - c.buf.length) :
    putBlock w id bs (fuel + 1) = some (w.setChan id { c with buf := c.buf ++ bs }) := by
  cases bs with
  | nil => exact absurd rfl ne
  | cons b bs =>
    have bad : ¬ (c.fd < 0 ∨ (!c.isOut) = true) := by rw [out]; simp; omega
    rw [putBlock]
    · simp only [hc, Option.bind_eq_bind, Option.bind_some, bad, room, ↓reduceIte]
      rfl
    · intro h; cases h

/-- The buffer after a block reaching its end: filled from the block. -/
def filledChan (c : Chan) (bs : List UInt8) : Chan :=
  { c with buf := [], offset := c.offset + (c.buf ++ bs.take (ioBufferSize - c.buf.length)).length }

/-- `caml_putblock` on a block reaching the end of the buffer: the buffer is
filled, written out whole, and the rest of the block put. -/
theorem putBlock_full {w w'' : World} {id fuel : Nat} {bs : List UInt8} {c : Chan}
    (hc : w.chans[id]? = some c) (fd0 : 0 ≤ c.fd) (out : c.isOut = true) (ne : bs ≠ [])
    (full : ioBufferSize - c.buf.length ≤ bs.length)
    (fits : offsetFits c (c.buf ++ bs.take (ioBufferSize - c.buf.length)).length = true)
    (write : writeFd w c.fd (c.buf ++ bs.take (ioBufferSize - c.buf.length)) = some w'') :
    putBlock w id bs (fuel + 1) =
      putBlock (w''.setChan id (filledChan c bs)) id (bs.drop (ioBufferSize - c.buf.length)) fuel := by
  cases bs with
  | nil => exact absurd rfl ne
  | cons b bs =>
    have bad : ¬ (c.fd < 0 ∨ (!c.isOut) = true) := by rw [out]; simp; omega
    have nroom : ¬ (b :: bs).length < ioBufferSize - c.buf.length := by omega
    rw [putBlock]
    · simp only [hc, Option.bind_eq_bind, Option.bind_some, bad, nroom, ↓reduceIte]
      simp only [fits, Bool.not_true, Bool.false_eq_true, ↓reduceIte, write, Option.bind_some]
      rfl
    · intro h; cases h

/-- A `caml_putblock` that succeeds on a full buffer passed the offset check. -/
theorem putBlock_full_fits {w wF : World} {id fuel : Nat} {bs : List UInt8} {c : Chan}
    (hc : w.chans[id]? = some c) (fd0 : 0 ≤ c.fd) (out : c.isOut = true) (ne : bs ≠ [])
    (full : ioBufferSize - c.buf.length ≤ bs.length) (ok : putBlock w id bs (fuel + 1) = some wF) :
    offsetFits c (c.buf ++ bs.take (ioBufferSize - c.buf.length)).length = true := by
  cases bs with
  | nil => exact absurd rfl ne
  | cons b bs =>
    have bad : ¬ (c.fd < 0 ∨ (!c.isOut) = true) := by rw [out]; simp; omega
    have nroom : ¬ (b :: bs).length < ioBufferSize - c.buf.length := by omega
    cases e : offsetFits c (c.buf ++ (b :: bs).take (ioBufferSize - c.buf.length)).length
    · rw [putBlock] at ok
      · simp only [hc, Option.bind_eq_bind, Option.bind_some, bad, nroom, ↓reduceIte] at ok
        simp only [e, Bool.not_false, ↓reduceIte] at ok
        cases ok
      · intro h; cases h
    · rfl

/-- `caml_putblock` with fuel left needs at least one step. -/
theorem putBlock_fuel {w wF : World} {id fuel : Nat} {bs : List UInt8} (ne : bs ≠ [])
    (ok : putBlock w id bs fuel = some wF) : ∃ f, fuel = f + 1 := by
  cases fuel with
  | zero =>
    cases bs with
    | nil => exact absurd rfl ne
    | cons b bs => simp [putBlock] at ok
  | succ f => exact ⟨f, rfl⟩

theorem putBlock_nil (w : World) (id fuel : Nat) : putBlock w id [] fuel = some w := by
  cases fuel <;> rfl

/-- **What `caml_putblock` changes**: the one channel and the OS state. -/
theorem putBlock_shape {w wF : World} {id fuel : Nat} {bs : List UInt8} {c : Chan}
    (hc : w.chans[id]? = some c) (ok : putBlock w id bs fuel = some wF) :
    ∃ c', wF = { w with chans := w.chans.set id c', os := wF.os } := by
  induction fuel generalizing w bs c with
  | zero =>
    cases bs with
    | nil =>
      cases ok
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hc
      exact ⟨c, by rw [← heq, List.set_getElem_self]⟩
    | cons b bs => simp [putBlock] at ok
  | succ f ih =>
    cases bs with
    | nil =>
      cases ok
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hc
      exact ⟨c, by rw [← heq, List.set_getElem_self]⟩
    | cons b bs =>
      rw [putBlock] at ok
      · simp only [hc, Option.bind_eq_bind, Option.bind_some] at ok
        split at ok
        · cases ok
        · split at ok
          · cases ok; exact ⟨_, rfl⟩
          · split at ok
            · cases ok
            · try simp only [Option.bind_eq_bind] at ok
              cases hw : writeFd w c.fd (c.buf ++ (b :: bs).take (ioBufferSize - c.buf.length)) with
              | none => rw [hw] at ok; cases ok
              | some w' =>
                rw [hw, Option.bind_some] at ok
                have hlt := (List.getElem?_eq_some_iff.mp hc).1
                have w'eq : ∃ os', w' = { w with os := os' } := by
                  unfold writeFd at hw
                  split at hw
                  · cases hw
                  · simp only [Option.bind_eq_bind] at hw
                    cases ho : osCall w.os _ with
                    | none => rw [ho] at hw; cases hw
                    | some r =>
                      rw [ho, Option.bind_some] at hw
                      split at hw
                      · cases hw; exact ⟨_, rfl⟩
                      · cases hw
                obtain ⟨os', rfl⟩ := w'eq
                obtain ⟨c', hc'⟩ := ih (c := filledChan c (b :: bs))
                  (by simp [World.setChan, List.getElem?_set_self hlt, filledChan]) ok
                refine ⟨c', ?_⟩
                rw [hc']
                simp [World.setChan, List.set_set]
      · intro h; cases h

end OCaml.Vm.Primitives.ConsoleWrite
