import OCaml.Vm.Sim.ConsoleCall
import OCaml.Vm.Primitives.Console.MlFlush
import OCaml.Vm.Primitives.Console.Runtime
import OCaml.Vm.Primitives.ChannelFrame
import OCaml.Vm.Primitives.Console.Geometry
import OCaml.Vm.Primitives.Console.World
import OCaml.Vm.Gc.F1Runtime

/-! `caml_ml_flush` at a `C_CALL1` site: the model inversion, the machine
input at a represented console channel, the flushed channel's record, and the
framed summaries of the open and closed paths. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- `caml_ml_flush`'s model: a channel argument, `flushChan`, `Val_unit`. -/
theorem flush_semantics {a v : Val} {h h' : Heap} {w w' : World}
    (sem : primF1Impl "caml_ml_flush" [a] h w = .ok v h' w') :
    ∃ id, chanOf? h a = some id ∧ flushChan w id = some w' ∧ v = Val.unit ∧ h' = h := by
  cases hc : chanOf? h a with
  | none => simp [primF1Impl, hc] at sem
  | some id =>
    cases hf : flushChan w id with
    | none => simp [primF1Impl, hc, hf] at sem
    | some w'' =>
      simp [primF1Impl, hc, hf] at sem
      obtain ⟨rfl, rfl, rfl⟩ := sem
      exact ⟨id, rfl, hf, rfl, rfl⟩

/-- **`caml_ml_flush`'s entry** at a represented channel, open or closed. -/
theorem flush_entry {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain entry : Nat} {env ra : BitVec 64} {c : Config} {l a id ch : Nat} {chn : Chan}
    {D : InvocationData}
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain entry env c)
    (arg : ChannelArg s c pl cp l a id ch chn) (inv : Invocation D c) (valid : NativeValid D)
    (saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], (gprGet c.σ n).isSome) :
    ConsoleWrite.MlFlushEntry ra (BitVec.ofNat 64 D.nativeSp) (BitVec.ofNat 64 a) (word c (a + 8))
      (word c Layout.sym_Caml_state) (word c ((word c Layout.sym_Caml_state).toNat + 288)) c := by
  have G := console_geometry setup.geometry arg valid
  have GL := G.lits
  have hs : (BitVec.ofNat 64 D.nativeSp).toNat = D.nativeSp := by
    rw [BitVec.toNat_ofNat]; have := GL.high; omega
  have hv : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; have := GL.valHigh; omega
  exact
    { setup.input.toLeafInput with
      idle := setup.input.loop.htifIdle
      saved := saved
      stack := inv.stack
      valReg := arg.reg
      frame := G.mlFlushFrame arg.pointer hv rfl hs
      domWord := by rw [ConsoleWrite.consoleLits.state, read8_value]; rfl
      rootsWord := by
        rw [ConsoleWrite.bv_add_toNat (by have := GL.domHigh; omega), read8_value]; rfl
      chanPtr := by
        rw [ConsoleWrite.bv_add_toNat (by rw [hv]; have := GL.valHigh; omega), hv, read8_value]; rfl }

/-- **`caml_ml_flush`'s input** at a represented console channel. -/
theorem flush_input {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain entry : Nat} {env ra : BitVec 64} {c : Config} {l a id ch : Nat} {chn : Chan}
    {D : InvocationData}
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain entry env c)
    (arg : ChannelArg s c pl cp l a id ch chn) (inv : Invocation D c) (valid : NativeValid D)
    (rt : ConsoleWrite.ConsoleRuntime c) (console : chn.fd = 1 ∨ chn.fd = 2) (out : chn.isOut = true)
    (saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], (gprGet c.σ n).isSome) :
    ConsoleWrite.MlFlushInput ra (BitVec.ofNat 64 D.nativeSp) (BitVec.ofNat 64 a) (word c (a + 8))
      (BitVec.ofInt 64 chn.fd) ConsoleWrite.impureData (word c (ch + 8))
      (word c Layout.sym_Caml_state) (word c ((word c Layout.sym_Caml_state).toNat + 288)) chn.buf c := by
  have G := console_geometry setup.geometry arg valid
  have F := arg.repr.fields
  have open_ : chn.fd ≠ -1 := by omega
  obtain ⟨hbuf, hcur⟩ := out_buffer open_ out
  rw [hbuf] at G
  have GL := G.lits
  have hc : (word c (a + 8)).toNat = ch := arg.pointer
  have hfd : BitVec.ofInt 64 chn.fd = 1#64 ∨ BitVec.ofInt 64 chn.fd = 2#64 := by
    rcases console with e | e <;> rw [e] <;> decide
  have hs : (BitVec.ofNat 64 D.nativeSp).toNat = D.nativeSp := by
    rw [BitVec.toNat_ofNat]; have := GL.high; omega
  have h112 : (BitVec.ofNat 64 D.nativeSp - 112#64).toNat + 112 = D.nativeSp := by
    rw [ConsoleWrite.bv_sub_toNat (by rw [hs]; have := GL.low; omega), hs]; have := GL.low; omega
  have hv : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; have := GL.valHigh; omega
  have chRam := GL.chanHigh
  have chL := GL.chanLow
  have b72 : (word c (a + 8) + 72#64).toNat = ch + 72 := by
    rw [ConsoleWrite.bv_add_toNat (by rw [hc]; omega), hc]
  have C := ConsoleWrite.consoleLits
  have fdw : bytesVal .lw (read8 c.σ.mem (word c (a + 8)).toNat) = BitVec.ofInt 64 chn.fd := by
    rw [hc]; exact fd_word (by simpa [chanOffFd] using F.fd) console
  have curr : bytesVal .ld (read8 c.σ.mem (word c (a + 8) + 24#64).toNat) =
      word c (a + 8) + 72#64 + BitVec.ofNat 64 chn.buf.length := by
    rw [ConsoleWrite.bv_add_toNat (by rw [hc]; omega), hc, read8_value]
    apply BitVec.eq_of_toNat_eq
    have cw := F.curr
    simp only [chanOffCurr, chanOffBuff, hcur] at cw
    change (word c (ch + 24)).toNat = _
    rw [cw, BitVec.toNat_add, b72, BitVec.toNat_ofNat]; omega
  refine
    { flush_entry setup arg inv valid saved with
      flush :=
        { short := by have := F.cursorLe; rw [hcur] at this; simp only [ioBufferSize] at this; omega
          layout := G.flush hc h112 (by decide) (by decide) hfd
          fdWord := fdw
          descriptor := by
            rcases hfd with e | e <;> rw [e]
            · exact rt.stdout
            · exact rt.stderr
          curr := curr
          offset := by rw [ConsoleWrite.bv_add_toNat (by rw [hc]; omega), hc, read8_value]; rfl
          ram := by rw [b72, C.tohost]; omega
          bytes := by
            intro i x hx
            have hi := (List.getElem?_eq_some_iff.mp hx).1
            have e : (word c (a + 8) + 72#64 + BitVec.ofNat 64 i).toNat = ch + chanOffBuff + i := by
              rw [ConsoleWrite.bv_add_toNat (by rw [b72]; omega), b72]; rfl
            rw [e, ← byte_total]
            exact F.bytes i x (by rw [hbuf]; exact hx)
          enterHookWord := rt.enterHookWord
          leaveHookWord := rt.leaveHookWord
          impure := rt.impure
          clear := rt.clear
          quiet := rt.quiet }
      layout := G.mlFlush hc hv rfl hs hfd
      lockNull := rt.lockNull
      unlockNull := rt.unlockNull }

/-- `caml_ml_flush`'s footprint as a write log (the values are irrelevant). -/
def flushLog (sp a : Nat) : List WEntry :=
  [(sp - 384, 384, 0#64), (Layout.sym_errno, 4, 0#64), (Layout.sym_impure_data, 4, 0#64),
   (a + 8, 8, 0#64), (a + 24, 8, 0#64)]

/-- A byte frame on the flush footprint is a getD frame on the console windows. -/
theorem frameOnD_of_flushLog {c e : Config} {sp a : Nat} (room : 384 ≤ sp)
    (memory : ∀ x, OutL (flushLog sp a) x → byte e x = byte c x) :
    FrameOnD (consoleWindows sp a) c.σ.mem e.σ.mem := by
  intro x hx
  simp only [consoleWindows, OutW, and_true] at hx
  have m := memory x (by simp only [flushLog, OutL, and_true]; omega)
  rwa [byte_total, byte_total] at m

/-- A run that keeps every byte outside the footprint and the local-roots
word, and restores the local-roots word's value, keeps every byte outside the
footprint. -/
theorem footprint_memory {c e : Config} {sp ch dom : Nat} {lr : BitVec 64}
    (rootsC : bytesT c.σ.mem (dom + 288) 8 = lr) (rootsE : bytesT e.σ.mem (dom + 288) 8 = lr)
    (frame : ∀ x, OutL (flushLog sp ch) x → (x < dom + 288 ∨ dom + 296 ≤ x) →
      (e.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0) :
    ∀ x, OutL (flushLog sp ch) x → byte e x = byte c x := by
  intro x hx
  rw [byte_total, byte_total]
  by_cases hr : dom + 288 ≤ x ∧ x < dom + 296
  · have b := Gc.byte_of_bytesT (rootsE.trans rootsC.symm) (i := x - (dom + 288)) (by omega)
    rwa [show dom + 288 + (x - (dom + 288)) = x by omega] at b
  · exact frame x hx (by omega)

/-- `caml_ml_flush` (open channel) writes nothing outside its footprint: the
frame, the errno words and the two channel words; the local-roots word it
rewrites is restored to its old value. -/
theorem flush_memory {ra spB chB rp off domB lr : BitVec 64} {bs : List UInt8} {c e : Config} {sp ch : Nat}
    (post : ConsoleWrite.MlFlushPost ra spB chB rp off domB lr bs c e)
    (hs : spB.toNat = sp) (room : 384 ≤ sp) (hc : chB.toNat = ch) (hrp : rp = ConsoleWrite.impureData)
    (roots : bytesVal .ld (OCaml.Vm.Primitives.read8 c.σ.mem (domB + 288#64).toNat) = lr)
    (hd : (domB + 288#64).toNat = domB.toNat + 288) :
    ∀ x, OutL (flushLog sp ch) x → byte e x = byte c x := by
  have C := ConsoleWrite.consoleLits
  apply footprint_memory (dom := domB.toNat) (lr := lr)
  · rw [← read8_value, ← hd]; exact roots
  · rw [← read8_value, ← hd]; exact post.roots
  · intro x hx hr
    simp only [flushLog, OutL, Layout.sym_errno, Layout.sym_impure_data] at hx
    subst hrp
    exact post.frame x (by omega) (by rw [C.errno]; omega) (by rw [C.impureData]; omega) (by omega) (by omega) hr

/-- **The flushed channel's record**: `curr` back at the buffer start, `offset`
advanced by the buffer's length, every other field kept. -/
theorem flushed_chanAt {c e : Config} {ch : Nat} {chn : Chan} {chB : BitVec 64}
    (repr : ChanAt c ch chn) (open_ : chn.fd ≠ -1) (out : chn.isOut = true)
    (fits : offsetFits chn chn.buf.length = true) (hc : chB.toNat = ch) (ram : ch + 72 < 2 ^ 64)
    (curr : bytesVal .ld (OCaml.Vm.Primitives.read8 e.σ.mem (chB + 24#64).toNat) = chB + 72#64)
    (offset : bytesVal .ld (OCaml.Vm.Primitives.read8 e.σ.mem (chB + 8#64).toNat) =
      word c (ch + 8) + BitVec.ofNat 64 chn.buf.length)
    (keep : ∀ x, ch ≤ x → x < ch + 72 → (x < ch + 8 ∨ ch + 16 ≤ x) → (x < ch + 24 ∨ ch + 32 ≤ x) →
      byte e x = byte c x) :
    ChanAt e ch { chn with buf := [], offset := chn.offset + chn.buf.length } := by
  have F := repr.fields
  have len := F.bufferLe
  obtain ⟨hbuf, hcur⟩ := out_buffer open_ out
  rw [hbuf] at len
  simp only [ioBufferSize] at len
  have fits' : chn.offset + chn.buf.length < 2 ^ 63 := of_decide_eq_true fits
  have copy := fun (k n : Nat) (hk : 72 ≤ k + n ∨ True) (lo : k + n ≤ 8 ∨ (16 ≤ k ∧ k + n ≤ 24) ∨ (32 ≤ k ∧ k + n ≤ 72)) =>
    (show Reloc.Copied c e (ch + k) (ch + k) n from fun j hj => keep _ (by omega) (by omega) (by omega) (by omega))
  have w8 : word e (ch + 8) = word c (ch + 8) + BitVec.ofNat 64 chn.buf.length := by
    change bytesT e.σ.mem (ch + 8) 8 = _
    rw [← read8_value, ← offset, show (chB + 8#64).toNat = ch + 8 by
      rw [ConsoleWrite.bv_add_toNat (by omega), hc]]
  have w24 : (word e (ch + 24)).toNat = ch + 72 := by
    change (bytesT e.σ.mem (ch + 24) 8).toNat = _
    rw [← read8_value, show ch + 24 = (chB + 24#64).toNat by rw [ConsoleWrite.bv_add_toNat (by omega), hc],
      curr, ConsoleWrite.bv_add_toNat (by omega), hc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, F.aligned⟩
  · rw [show word32 e (ch + chanOffFd) = word32 c (ch + chanOffFd) from
      Reloc.bytesT_congr (copy chanOffFd 4 (Or.inr trivial) (by simp only [chanOffFd]; omega))]
    exact F.fd
  · simp only [chanOffOffset]
    rw [w8, toInt_add_small _ _ (by omega) (by have := F.offset; simp only [chanOffOffset] at this; omega)]
    have := F.offset; simp only [chanOffOffset] at this; rw [this]
  · simp only [chanOffCurr, chanOffBuff, Chan.cursor, open_, out, ↓reduceIte, List.length_nil, Nat.add_zero]
    exact w24
  · rw [show word e (ch + chanOffMax) = word c (ch + chanOffMax) from
      Reloc.bytesT_congr (copy chanOffMax 8 (Or.inr trivial) (by simp only [chanOffMax]; omega))]
    exact F.max
  · rw [show word e (ch + chanOffEnd) = word c (ch + chanOffEnd) from
      Reloc.bytesT_congr (copy chanOffEnd 8 (Or.inr trivial) (by simp only [chanOffEnd]; omega))]
    exact F.bufEnd
  · rw [show word32 e (ch + chanOffFlags) = word32 c (ch + chanOffFlags) from
      Reloc.bytesT_congr (copy chanOffFlags 4 (Or.inr trivial) (by simp only [chanOffFlags]; omega))]
    exact F.flags
  · intro i b hb; simp [Chan.buffer, open_, out] at hb
  · simp [Chan.cursor, open_, out]
  · simp [Chan.buffer, open_, out]

/-- **`caml_ml_flush` on an open console channel, framed**: the machine
summary with the represented post a C_CALL return needs. The payload and
binding apartness of the footprint are premises (from the loop geometry). -/
theorem flush_framed {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain : Nat} {env ra : BitVec 64} {c : Config} {l a id ch : Nat} {chn : Chan}
    {D : InvocationData} {st : TCB.Os.Stream}
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain 0x80016238 env c)
    (arg : ChannelArg s c pl cp l a id ch chn) (inv : Invocation D c) (valid : NativeValid D)
    (rt : ConsoleWrite.ConsoleRuntime c) (console : chn.fd = 1 ∨ chn.fd = 2) (out : chn.isOut = true)
    (fits : offsetFits chn chn.buf.length = true) (streamOut : st ≠ .stdin)
    (saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], (gprGet c.σ n).isSome)
    (outside : PayloadChanOutside (flushLog D.nativeSp ch) P s c pl cp sp id)
    (bindings : BindingsOutside (flushLog D.nativeSp ch) P c)
    (stable : ConsoleStable L)
    (sem : primF1Impl "caml_ml_flush" [s.accu] s.heap s.world =
      .ok Val.unit s.heap (ConsoleWrite.flushedWorld s.world id chn st)) :
    FnSummary (BitVec.ofNat 64 0x80016238) (fun x => x = c)
      (FramedPrimitivePost L.runtimeOk P s pl cp sp high "caml_ml_flush" [s.accu] Val.unit 1#64 s.heap
        (ConsoleWrite.flushedWorld s.world id chn st) (flushLog D.nativeSp ch) c ra) := by
  have I := flush_input setup arg inv valid rt console out saved
  have G := (console_geometry setup.geometry arg valid).lits
  have open_ : chn.fd ≠ -1 := by omega
  obtain ⟨hbuf, hcur⟩ := out_buffer open_ out
  have nlow := G.low
  have nhigh := G.high
  have chl := G.chanLow
  have chh := G.chanHigh
  have dh := G.domHigh
  have hs : (BitVec.ofNat 64 D.nativeSp).toNat = D.nativeSp := by rw [BitVec.toNat_ofNat]; omega
  have hd : (word c Layout.sym_Caml_state + 288#64).toNat = (word c Layout.sym_Caml_state).toNat + 288 := by
    rw [ConsoleWrite.bv_add_toNat (by omega)]
  refine ⟨fun c0 ⟨pc0, e0⟩ => ?_⟩
  subst c0
  obtain ⟨e, run, post⟩ := ConsoleWrite.ml_flush I pc0
  have memory := flush_memory post hs (by omega) arg.pointer rfl I.rootsWord hd
  have repr' : ChanAt e ch { chn with buf := [], offset := chn.offset + chn.buf.length } :=
    flushed_chanAt arg.repr open_ out fits arg.pointer (by omega) post.curr post.offset
      (fun x lo hi o k => memory x (by
        simp only [flushLog, OutL, Layout.sym_errno, Layout.sym_impure_data, and_true]; omega))
  have console' : output e.σ = bytesToString (ConsoleWrite.flushedWorld s.world id chn st).console := by
    rw [ConsoleWrite.flushedWorld_console _ _ _ streamOut, bytesToString_append, ← setup.input.data.world.output]
    exact post.output
  refine ⟨e, run, ⟨⟨post.good, post.image, post.minstret, post.tick, post.pc, post.result, memory, ?_⟩,
    ?_, bindings_frame_outsideLog setup.input.primitives bindings memory,
    ⟨post.good, post.image, stable P s c pl cp high id chn ch D.nativeSp setup.geometry setup.input.runtime
      arg.chan arg.record valid.headroom (by simp only [Layout.sym_stack_top]; omega) e (frameOnD_of_flushLog (by omega) memory)⟩,
    LoopRegisters.of_restored setup.input.loop (fun n hn => post.saved n (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn ⊢; omega)) post.idle,
    rfl, sem⟩⟩
  · intro r hr
    simp only [callSavedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact post.saved 25 (by decide)
    · exact post.saved 8 (by decide)
    · exact post.saved 18 (by decide)
    · exact post.stack.trans inv.stack.symm
  · have d1 := setup.input.data.frame_chan (w' := ConsoleWrite.flushedWorld s.world id chn st) outside memory rfl rfl rfl arg.record repr' console'
    exact d1.accu_int 0

/-- A closed channel's descriptor word is `-1`: `caml_ml_flush` returns at once. -/
theorem closed_fd {c : Config} {a : Nat} (h : (word32 c a).toInt = -1) :
    guardB .BEQ (bytesVal .lw (OCaml.Vm.Primitives.read8 c.σ.mem a)) 18446744073709551615#64 = true := by
  rw [lw_read8]
  change guardB .BEQ (LeanRV64DExecutable.Functions.sign_extend (m := 64) (word32 c a)) _ = true
  have e : word32 c a = 4294967295#32 := BitVec.eq_of_toInt_eq (by rw [h]; decide)
  rw [e]; decide

/-- **`caml_ml_flush` on a closed channel, framed**: `Val_unit`, the world
unchanged. -/
theorem flush_closed_framed {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain : Nat} {env ra : BitVec 64} {c : Config} {l a id ch : Nat} {chn : Chan}
    {D : InvocationData}
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain 0x80016238 env c)
    (arg : ChannelArg s c pl cp l a id ch chn) (inv : Invocation D c) (valid : NativeValid D)
    (closed : chn.fd = -1)
    (saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], (gprGet c.σ n).isSome)
    (outside : PayloadChanOutside (flushLog D.nativeSp ch) P s c pl cp sp id)
    (bindings : BindingsOutside (flushLog D.nativeSp ch) P c)
    (stable : ConsoleStable L)
    (sem : primF1Impl "caml_ml_flush" [s.accu] s.heap s.world = .ok Val.unit s.heap s.world) :
    FnSummary (BitVec.ofNat 64 0x80016238) (fun x => x = c)
      (FramedPrimitivePost L.runtimeOk P s pl cp sp high "caml_ml_flush" [s.accu] Val.unit 1#64 s.heap
        s.world (flushLog D.nativeSp ch) c ra) := by
  have E := flush_entry setup arg inv valid saved
  have G := (console_geometry setup.geometry arg valid).lits
  have nlow := G.low
  have nhigh := G.high
  have chl := G.chanLow
  have chh := G.chanHigh
  have dh := G.domHigh
  have hs : (BitVec.ofNat 64 D.nativeSp).toNat = D.nativeSp := by rw [BitVec.toNat_ofNat]; omega
  have hd : (word c Layout.sym_Caml_state + 288#64).toNat = (word c Layout.sym_Caml_state).toNat + 288 := by
    rw [ConsoleWrite.bv_add_toNat (by omega)]
  have hc : (word c (a + 8)).toNat = ch := arg.pointer
  have fd : guardB .BEQ (bytesVal .lw (OCaml.Vm.Primitives.read8 c.σ.mem (word c (a + 8)).toNat))
      18446744073709551615#64 = true := by
    rw [hc]; exact closed_fd (by simpa [chanOffFd] using arg.repr.fields.fd.trans closed)
  refine ⟨fun c0 ⟨pc0, e0⟩ => ?_⟩
  subst c0
  obtain ⟨e, run, post⟩ := ConsoleWrite.ml_flush_closed E pc0 fd
  have keep : ∀ x, (x < D.nativeSp - 112 ∨ D.nativeSp ≤ x) →
      (x < (word c Layout.sym_Caml_state).toNat + 288 ∨ (word c Layout.sym_Caml_state).toNat + 296 ≤ x) →
      (e.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := fun x lo hi => post.frame x (by rw [hs]; exact lo) hi
  have memory : ∀ x, OutL (flushLog D.nativeSp ch) x → byte e x = byte c x := by
    apply footprint_memory (dom := (word c Layout.sym_Caml_state).toNat)
      (lr := word c ((word c Layout.sym_Caml_state).toNat + 288)) rfl
    · have r := post.roots
      rw [hd, read8_value] at r
      exact r
    · intro x hx hr
      simp only [flushLog, OutL, Layout.sym_errno, Layout.sym_impure_data] at hx
      exact keep x (by omega) hr
  have repr : ChanAt e ch chn := by
    have dc := G.chanDom
    have len := arg.repr.bufferLe
    simp only [ioBufferSize] at len
    exact channel_copied arg.repr fun j hj => by
      have hj' : j < 72 + chn.buffer.length := by simpa [chanOffBuff] using hj
      rw [byte_total, byte_total]
      exact keep (ch + j) (by omega) (by omega)
  have chans : s.world.chans = s.world.chans.set id chn := by
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp arg.chan
    rw [← heq, List.set_getElem_self]
  refine ⟨e, run, ⟨⟨post.good, post.image, post.minstret, post.tick, post.pc, post.result, memory, ?_⟩,
    ?_, bindings_frame_outsideLog setup.input.primitives bindings memory,
    ⟨post.good, post.image, stable P s c pl cp high id chn ch D.nativeSp setup.geometry setup.input.runtime
      arg.chan arg.record valid.headroom (by simp only [Layout.sym_stack_top]; omega) e
      (frameOnD_of_flushLog (by omega) memory)⟩,
    LoopRegisters.of_restored setup.input.loop (fun n hn => post.saved n (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn ⊢; omega)) post.idle,
    rfl, sem⟩⟩
  · intro r hr
    simp only [callSavedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact post.saved 25 (by decide)
    · exact post.saved 8 (by decide)
    · exact post.saved 18 (by decide)
    · exact post.stack.trans inv.stack.symm
  · have d1 := setup.input.data.frame_chan (w' := s.world) outside memory chans rfl rfl arg.record repr
      (post.output.trans setup.input.data.world.output)
    exact d1.accu_int 0

end OCaml.Vm.Sim
