import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Sim.CcallWriting
import OCaml.Vm.Primitives.Console.MlFlush
import OCaml.Vm.Primitives.Console.Runtime
import OCaml.Vm.Primitives.ChannelFrame
import OCaml.Vm.Primitives.Console.Geometry
import OCaml.Vm.Primitives.Console.World

/-! `caml_ml_flush` at a `C_CALL1` site: its write footprint and the
runtime-stability obligation it puts on the layout. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- `caml_ml_flush`'s writes: the native stack below the C-call sp, newlib's
two `errno` words, the channel record's `offset` and `curr` words. -/
def flushWindows (sp a : Nat) : List W :=
  [⟨sp - 384, sp⟩, ⟨Layout.sym_errno, Layout.sym_errno + 4⟩,
   ⟨Layout.sym_impure_data, Layout.sym_impure_data + 4⟩, ⟨a + 8, a + 16⟩, ⟨a + 24, a + 32⟩]

/-- A byte-total frame: outside `ws`, every byte reads the same (`getD 0`). -/
def FrameOnD (ws : List W) (m0 m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ a, OutW ws a → (m[a]?).getD 0 = (m0[a]?).getD 0

/-- **Named obligation** (a6-gc, `f1_flush_stable` for F1): the runtime
invariant survives `caml_ml_flush`'s writes to a represented channel record,
from the call site's geometry and native sp. -/
def FlushStable (L : OCaml.Layout) : Prop :=
  ∀ (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace) (high id : Nat) (chn : Chan) (a sp : Nat),
    OCaml.LoopGeometry L P s c pl cp high → L.runtimeOk c →
    s.world.chans[id]? = some chn → cp id = some a →
    Vsa.Sim.DlHeap.heapEnd + nativeHeadroom ≤ sp → sp ≤ Layout.sym_stack_top →
    ∀ c', FrameOnD (flushWindows sp a) c.σ.mem c'.σ.mem → L.runtimeOk c'

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

/-- A channel value: a custom block holding the channel's record pointer. -/
theorem chanOf_ptr {h : Heap} {a : Val} {id : Nat} (hc : chanOf? h a = some id) :
    ∃ l, a = .ptr l 0 ∧ h.get? l = some (.channel id) := by
  unfold chanOf? at hc
  split at hc
  · rename_i l
    split at hc
    · rename_i id' e
      cases hc
      exact ⟨l, rfl, e⟩
    · cases hc
  · cases hc

/-- **The represented channel argument** of a one-argument channel primitive
at its entry: the custom block at `a` (in `a0`), its record at `ch`. -/
structure ChannelArg (s : St) (c : Config) (pl : Place) (cp : ChanPlace) (l a id ch : Nat) (chn : Chan) : Prop where
  accu : s.accu = .ptr l 0
  object : s.heap.get? l = some (.channel id)
  placed : pl.φ l = some a
  ops : (word c a).toNat = Layout.sym_channel_operations
  pointer : (word c (a + 8)).toNat = ch
  chan : s.world.chans[id]? = some chn
  record : cp id = some ch
  repr : ChanAt c ch chn
  reg : gpr c 10 = some (BitVec.ofNat 64 a)

theorem channel_arg {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain entry : Nat} {env ra : BitVec 64} {c : Config} {id : Nat} {chn : Chan}
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain entry env c)
    (hc : chanOf? s.heap s.accu = some id) (hw : s.world.chans[id]? = some chn) :
    ∃ l a ch, ChannelArg s c pl cp l a id ch chn := by
  obtain ⟨l, accu, object⟩ := chanOf_ptr hc
  have live : Live s.heap (roots P s) l := Live.root (v := s.accu) List.mem_cons_self (by rw [accu]; rfl)
  obtain ⟨a, o, placed, ho, layout⟩ := setup.input.data.heap.1 l live
  rw [object] at ho
  cases ho
  obtain ⟨-, ops, pointer⟩ := layout
  obtain ⟨ch, record, repr⟩ := setup.input.data.world.chans id chn hw
  have e : (word c (a + 8)).toNat = ch := Option.some.inj (pointer.symm.trans record)
  have reg := setup.input.arguments.get (i := 0) (by simp [accu]) (show valWord pl (.ptr l 0) = some (BitVec.ofNat 64 (a + 8 * 0)) by simp [valWord, placed])
  exact ⟨l, a, ch, accu, object, placed, ops, e, hw, record, repr, by simpa using reg⟩

/-- The console geometry of a channel call: the native frames from the
invocation, the records from the loop geometry. -/
theorem console_geometry {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {high l a id ch : Nat} {chn : Chan} {c : Config} {D : InvocationData}
    (g : OCaml.LoopGeometry L P s c pl cp high) (arg : ChannelArg s c pl cp l a id ch chn) (valid : NativeValid D) :
    ConsoleWrite.ConsoleGeometry D.nativeSp ch (word c Layout.sym_Caml_state).toNat a chn.buffer.length := by
  have SG := g.toArmGeometry.toStackGeometry
  have hr := valid.headroom
  have hh := valid.high
  have ca := SG.channelArena id chn ch arg.chan arg.record
  have cd := (SG.domainChannels id chn ch arg.chan arg.record).1
  have hl := SG.heapLow l a (.channel id) arg.placed arg.object
  have ha := SG.heapArena l a (.channel id) arg.placed arg.object
  have hc := (SG.heapChannels l a (.channel id) arg.placed arg.object id chn ch arg.chan arg.record).1
  have hd := (SG.domainHeap l a (.channel id) arg.placed arg.object).1
  have cl := SG.channelLow id chn ch arg.chan arg.record
  have dl := SG.domainLow
  have da := SG.domainArena
  have dal := SG.domainAligned
  have al := arg.repr.aligned
  have va := valid.aligned
  simp only [chanOffBuff, Obj.wosize, nativeHeadroom] at ca cd hl ha hc hd hr
  generalize Layout.interpFrameBytes = f1 at hh
  generalize Layout.camlMainFrameBytes = f2 at hh
  generalize (word c Layout.sym_Caml_state).toNat = dom at *
  clear g SG arg valid
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_bss_end, Layout.domainStateBytes, Layout.sym_stack_top]
    at hr ca hl ha hc cl hh cd hd dl da
  refine ⟨?_, ?_, va, cl, ?_, al, dl, da, dal, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_bss_end, Layout.domainStateBytes, Layout.sym_stack_top]) <;> omega

/-- A signed word load of a word whose value is `n`. -/
theorem lw_read8 (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    bytesVal .lw (OCaml.Vm.Primitives.read8 m a) = LeanRV64DExecutable.Functions.sign_extend (m := 64) (bytesT m a 4) := by
  rw [← read4_value]; simp [bytesVal, OCaml.Vm.Primitives.read8, read4]

/-- A console channel's descriptor word. -/
theorem fd_word {c : Config} {a : Nat} {fd : Int} (h : (word32 c a).toInt = fd) (hfd : fd = 1 ∨ fd = 2) :
    bytesVal .lw (OCaml.Vm.Primitives.read8 c.σ.mem a) = BitVec.ofInt 64 fd := by
  rw [lw_read8]
  change LeanRV64DExecutable.Functions.sign_extend (m := 64) (word32 c a) = _
  rcases hfd with rfl | rfl
  · have e : word32 c a = 1#32 := BitVec.eq_of_toInt_eq (by rw [h]; decide)
    rw [e]; decide
  · have e : word32 c a = 2#32 := BitVec.eq_of_toInt_eq (by rw [h]; decide)
    rw [e]; decide

/-- An open output channel's active bytes and cursor are its buffer. -/
theorem out_buffer {chn : Chan} (open_ : chn.fd ≠ -1) (out : chn.isOut = true) :
    chn.buffer = chn.buf ∧ chn.cursor = chn.buf.length := by
  simp [Chan.buffer, Chan.cursor, open_, out]

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
    { setup.input.toLeafInput with
      idle := setup.input.loop.htifIdle
      saved := saved
      stack := inv.stack
      valReg := arg.reg
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
      domWord := by rw [ConsoleWrite.consoleLits.state, read8_value]; rfl
      rootsWord := by
        rw [ConsoleWrite.bv_add_toNat (by have := GL.domHigh; omega), read8_value]; rfl
      chanPtr := by
        rw [ConsoleWrite.bv_add_toNat (by rw [hv]; have := GL.valHigh; omega), hv, read8_value]; rfl
      lockNull := rt.lockNull
      unlockNull := rt.unlockNull }

end OCaml.Vm.Sim
