import OCaml.Vm.Sim.PrimMlFlush
import OCaml.Vm.Sim.PrimMlOutputChar
import OCaml.Vm.Sim.PrimMlOutput
import OCaml.RefinementF1

/-! The console primitives at their `C_CALL` sites (`PrimReturnsAt`): the
framed summaries, closed by `console_callee_summary`. Premises are
layout-level and named: the console footprint keeps the runtime invariant
(`ConsoleStable`), the runtime invariant pins the console statics
(`consoleRt`), and every open output channel is a console stream
(`ConsoleChannels`). -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- An open channel's successful flush: an output channel whose offset stays
an `int64`. -/
theorem flushChan_open {w w' : World} {id : Nat} {c : Chan} (hc : w.chans[id]? = some c) (fd : c.fd ≠ -1)
    (ok : flushChan w id = some w') : c.isOut = true ∧ offsetFits c c.buf.length = true := by
  simp only [flushChan, hc, Option.bind_eq_bind, Option.bind_some, fd, ↓reduceIte] at ok
  cases hout : c.isOut
  · simp [hout] at ok
  · cases hfit : offsetFits c c.buf.length
    · simp [hout, hfit] at ok
    · exact ⟨rfl, rfl⟩

/-- The console setting of a channel C_CALL: the native invocation, the
channel argument, and the console footprint's separation from the payload. -/
structure ConsoleCallSite (L : OCaml.Layout) (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp : Nat) (id : Nat) (chn : Chan) (D : InvocationData) (l a ch : Nat) : Prop where
  inv : Invocation D c
  valid : NativeValid D
  arg : ChannelArg s c pl cp l a id ch chn
  outside : PayloadChanOutside (consoleLog D.nativeSp ch) P s c pl cp sp id
  bindings : BindingsOutside (consoleLog D.nativeSp ch) P c

/-- **The console setting at a C_CALL entry**, for the accumulator's channel. -/
theorem console_site {L : OCaml.Layout} {P : Prog} {op : Opcode} {s : St} {c0 c : Config} {pl : Place}
    {cp : ChanPlace} {sp high table entry : Nat} {value env ra : BitVec 64} {index : BitVec 32} {name : String}
    {args : List Val} {id : Nat} {chn : Chan}
    (ready : CcallReady op L P s c0 pl cp sp high (domainAt c0) table entry value env index name)
    (setup : CcallSetupPost ra args L P s pl cp sp high (domainAt c0) entry env c)
    (first : args[0]? = some s.accu) (hc : chanOf? s.heap s.accu = some id) (hw : s.world.chans[id]? = some chn) :
    ∃ D l a ch, ConsoleCallSite L P s c pl cp sp id chn D l a ch := by
  obtain ⟨D, inv, valid⟩ := setup.native
  obtain ⟨l, a, ch, arg⟩ := channel_arg setup first hc hw
  have nl : Vsa.Sim.DlHeap.heapEnd + 512 ≤ D.nativeSp :=
    Nat.le_trans (Nat.add_le_add_left (show 512 ≤ nativeHeadroom by rw [show nativeHeadroom = 4096 from rfl]; omega) _)
      valid.headroom
  have g := setup.geometry.toArmGeometry.toStackGeometry
  have stk := setup.input.data.stack.1
  have fits := ready.stackFits
  have low : high - Layout.stackBytes ≤ sp := by
    rw [← stk]; rw [show Layout.stackBytes = 32768 from rfl] at fits ⊢; omega
  exact ⟨D, l, a, ch, inv, valid, arg, console_outside g stk low nl arg.chan arg.record,
    console_bindings g nl arg.chan arg.record⟩

/-- **`caml_ml_output_char` returns at a `C_CALL2` site.** -/
theorem prim_caml_ml_output_char_returns {L : OCaml.Layout} {P : Prog} {ra : BitVec 64}
    (consoleStable : ConsoleStable L) (consoleRt : ∀ c, L.runtimeOk c → ConsoleWrite.ConsoleRuntime c)
    (consoles : OCaml.ConsoleChannels P) :
    PrimReturnsAt L P .C_CALL2 ra 1 "caml_ml_output_char" := by
  intro s c0 pl cp sp high table entry value env index v heap world reach ready sem
  obtain ⟨x, rest, hst⟩ : ∃ x rest, s.stack = x :: rest := by
    match h : s.stack with
    | x :: rest => exact ⟨x, rest, rfl⟩
    | [] => rw [h] at sem; simp [primF1Impl] at sem
  have args : s.accu :: s.stack.take 1 = [s.accu, x] := by rw [hst]; rfl
  have sem0 := sem
  rw [args] at sem
  obtain ⟨id, n, hc, hn, put, rfl, rfl⟩ := output_char_semantics sem
  obtain ⟨nb, rfl, rfl⟩ := intArg_some hn
  obtain ⟨chn, hw, fd0, out, case⟩ := putChar_cases put
  have hentry : entry = Layout.sym_caml_ml_output_char :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_ml_output_char)
  subst hentry
  have open_ : chn.fd ≠ -1 := by omega
  obtain ⟨console, live, st, stream, streamOut⟩ := consoles s reach id chn hw out open_
  refine ⟨1#64, by decide, sem0, fun c setup => ?_⟩
  obtain ⟨D, l, a, ch, site⟩ := console_site ready setup (by rw [args]; rfl) hc hw
  have I := oc_input setup site.arg site.inv site.valid (consoleRt c setup.input.runtime) console out
    (console_geometry_full setup.geometry site.arg site.valid) (by rw [args]; rfl) setup.calleeSaved
  cases case with
  | room len =>
    exact console_callee_summary ready setup site.inv site.valid site.arg rfl rfl
      (oc_room_framed setup site.arg site.inv site.valid I open_ out len site.outside site.bindings consoleStable sem0)
  | full len fits write =>
    rw [ConsoleWrite.writeFd_stream fd0 live stream streamOut] at write
    cases write
    exact console_callee_summary ready setup site.inv site.valid site.arg rfl rfl
      (oc_full_framed setup site.arg site.inv site.valid (consoleRt c setup.input.runtime) console out I
        (by simp only [ioBufferSize] at len ⊢; have := site.arg.repr.bufferLe; have open_' := open_
            obtain ⟨hbuf, -⟩ := out_buffer open_ out; rw [hbuf] at this; simp only [ioBufferSize] at this; omega)
        fits streamOut site.outside site.bindings consoleStable sem0)

/-- **`caml_ml_flush` returns at a `C_CALL1` site.** -/
theorem prim_caml_ml_flush_returns {L : OCaml.Layout} {P : Prog} {ra : BitVec 64}
    (consoleStable : ConsoleStable L) (consoleRt : ∀ c, L.runtimeOk c → ConsoleWrite.ConsoleRuntime c)
    (consoles : OCaml.ConsoleChannels P) :
    PrimReturnsAt L P .C_CALL1 ra 0 "caml_ml_flush" := by
  intro s c0 pl cp sp high table entry value env index v heap world reach ready sem
  simp only [List.take_zero] at sem ⊢
  obtain ⟨id, hc, flushed, rfl, rfl⟩ := flush_semantics sem
  have hentry : entry = Layout.sym_caml_ml_flush :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_ml_flush)
  subst hentry
  obtain ⟨chn, hw⟩ : ∃ chn, s.world.chans[id]? = some chn := by
    cases e : s.world.chans[id]? with
    | none => simp [flushChan, e] at flushed
    | some chn => exact ⟨chn, rfl⟩
  refine ⟨1#64, by decide, sem, fun c setup => ?_⟩
  obtain ⟨D, l, a, ch, ⟨inv, valid, arg, outside, bindings⟩⟩ := console_site ready setup rfl hc hw
  by_cases closed : chn.fd = -1
  · have hworld : world = s.world := by
      simp only [flushChan, hw, Option.bind_eq_bind, Option.bind_some, closed, ↓reduceIte] at flushed
      exact (Option.some.inj flushed).symm
    subst hworld
    have hset : s.world.chans = s.world.chans.set id chn := by
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hw
      rw [← heq, List.set_getElem_self]
    exact console_callee_summary ready setup inv valid arg rfl hset
      (flush_closed_framed setup arg inv valid closed setup.calleeSaved outside bindings consoleStable sem)
  · obtain ⟨out, ofits⟩ := flushChan_open hw closed flushed
    obtain ⟨console, live, st, stream, streamOut⟩ := consoles s reach id chn hw out closed
    have fd0 : 0 ≤ chn.fd := by rcases console with h | h <;> rw [h] <;> decide
    rw [ConsoleWrite.flushChan_stream hw fd0 live stream streamOut out ofits] at flushed
    cases flushed
    exact console_callee_summary ready setup inv valid arg rfl rfl
      (flush_framed setup arg inv valid (consoleRt c setup.input.runtime) console out ofits streamOut
        setup.calleeSaved outside bindings consoleStable sem)

end OCaml.Vm.Sim
