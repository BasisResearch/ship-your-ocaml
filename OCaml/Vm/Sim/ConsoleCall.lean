import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Sim.CcallWriting
import OCaml.Vm.Primitives.ChannelFrame
import OCaml.Vm.Primitives.Console.Geometry

/-! Pieces shared by the console primitives' C_CALL adapters (`caml_ml_flush`,
`caml_ml_output_char`, `caml_ml_output_bytes`): their write windows and the
runtime-stability obligation, the represented channel argument, the numeric
geometry at the callee entry, and the register and arithmetic facts of a
console return. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The console primitives' writes (`caml_ml_flush`, `caml_ml_output_char`,
`caml_ml_output_bytes`): the native stack below the C-call sp (448 bytes deep at most:
`caml_ml_output_bytes`' frame, `caml_flush_partial`'s, `caml_write_fd`'s), newlib's two
`errno` words, the channel record's `offset` and `curr` words and its buffer. -/
def consoleWindows (sp a : Nat) : List W :=
  [⟨sp - 512, sp⟩, ⟨Layout.sym_errno, Layout.sym_errno + 4⟩,
   ⟨Layout.sym_impure_data, Layout.sym_impure_data + 4⟩, ⟨a + 8, a + 16⟩, ⟨a + 24, a + 32⟩,
   ⟨a + 72, a + 72 + ioBufferSize⟩]

/-- A byte-total frame: outside `ws`, every byte reads the same (`getD 0`). -/
def FrameOnD (ws : List W) (m0 m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ a, OutW ws a → (m[a]?).getD 0 = (m0[a]?).getD 0

/-- **Named obligation** (a6-gc, `f1_console_stable` for F1): the runtime
invariant survives the console primitives' writes to a represented channel
record, from the call site's geometry and native sp. -/
def ConsoleStable (L : OCaml.Layout) : Prop :=
  ∀ (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace) (high id : Nat) (chn : Chan) (a sp : Nat),
    OCaml.LoopGeometry L P s c pl cp high → L.runtimeOk c →
    s.world.chans[id]? = some chn → cp id = some a →
    Vsa.Sim.DlHeap.heapEnd + nativeHeadroom ≤ sp → sp ≤ Layout.sym_stack_top →
    ∀ c', FrameOnD (consoleWindows sp a) c.σ.mem c'.σ.mem → L.runtimeOk c'

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

/-- **The represented channel argument** of a channel primitive
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
    {sp high domain entry : Nat} {env ra : BitVec 64} {c : Config} {id : Nat} {chn : Chan} {args : List Val}
    (setup : CcallSetupPost ra args L P s pl cp sp high domain entry env c) (first : args[0]? = some s.accu)
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
  have reg := setup.input.arguments.get (i := 0) (by rw [first, accu]) (show valWord pl (.ptr l 0) = some (BitVec.ofNat 64 (a + 8 * 0)) by simp [valWord, placed])
  exact ⟨l, a, ch, accu, object, placed, ops, e, hw, record, repr, by simpa using reg⟩

/-- The console geometry of a channel call: the native frames from the
invocation, the records from the loop geometry, up to any extent `len` of the
channel buffer. -/
theorem console_geometry_upto {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {high l a id ch : Nat} {chn : Chan} {c : Config} {D : InvocationData}
    (g : OCaml.LoopGeometry L P s c pl cp high) (arg : ChannelArg s c pl cp l a id ch chn) (valid : NativeValid D)
    {len : Nat} (bl : len ≤ ioBufferSize) :
    ConsoleWrite.ConsoleGeometry D.nativeSp ch (word c Layout.sym_Caml_state).toNat a len := by
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
  simp only [chanOffBuff, ioBufferSize, Obj.wosize, nativeHeadroom] at ca cd hl ha hc hd hr bl
  generalize Layout.interpFrameBytes = f1 at hh
  generalize Layout.camlMainFrameBytes = f2 at hh
  generalize (word c Layout.sym_Caml_state).toNat = dom at *
  clear g SG arg valid
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_bss_end, Layout.domainStateBytes, Layout.sym_stack_top]
    at hr ca hl ha hc cl hh cd hd dl da bl
  refine ⟨?_, ?_, va, cl, ?_, al, dl, da, dal, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_bss_end, Layout.domainStateBytes, Layout.sym_stack_top]) <;> omega

/-- The console geometry of a channel call: the channel record at its full extent. -/
theorem console_geometry_full {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {high l a id ch : Nat} {chn : Chan} {c : Config} {D : InvocationData}
    (g : OCaml.LoopGeometry L P s c pl cp high) (arg : ChannelArg s c pl cp l a id ch chn) (valid : NativeValid D) :
    ConsoleWrite.ConsoleGeometry D.nativeSp ch (word c Layout.sym_Caml_state).toNat a 65536 :=
  console_geometry_upto g arg valid (Nat.le_refl _)

/-- The console geometry of a channel call, up to the buffer's active bytes. -/
theorem console_geometry {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {high l a id ch : Nat} {chn : Chan} {c : Config} {D : InvocationData}
    (g : OCaml.LoopGeometry L P s c pl cp high) (arg : ChannelArg s c pl cp l a id ch chn) (valid : NativeValid D) :
    ConsoleWrite.ConsoleGeometry D.nativeSp ch (word c Layout.sym_Caml_state).toNat a chn.buffer.length :=
  console_geometry_upto g arg valid arg.repr.bufferLe

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

/-- The words of an open console output channel's record, as loads read them. -/
structure ChanWords (c : Config) (chB : BitVec 64) (chn : Chan) : Prop where
  fd : bytesVal .lw (OCaml.Vm.Primitives.read8 c.σ.mem chB.toNat) = BitVec.ofInt 64 chn.fd
  offset : bytesVal .ld (OCaml.Vm.Primitives.read8 c.σ.mem (chB + 8#64).toNat) = word c (chB.toNat + 8)
  curr : bytesVal .ld (OCaml.Vm.Primitives.read8 c.σ.mem (chB + 24#64).toNat) =
    chB + 72#64 + BitVec.ofNat 64 chn.buf.length
  bufEnd : bytesVal .ld (OCaml.Vm.Primitives.read8 c.σ.mem (chB + 16#64).toNat) = chB + 72#64 + 65536#64

theorem ChanAt.words {c : Config} {chB : BitVec 64} {chn : Chan} (repr : ChanAt c chB.toNat chn)
    (console : chn.fd = 1 ∨ chn.fd = 2) (out : chn.isOut = true) (high : chB.toNat + 72 + 65536 < 2 ^ 64) :
    ChanWords c chB chn := by
  have F := repr.fields
  have open_ : chn.fd ≠ -1 := by omega
  obtain ⟨-, hcur⟩ := out_buffer open_ out
  have b72 : (chB + 72#64).toNat = chB.toNat + 72 := ConsoleWrite.bv_add_toNat (by omega)
  refine ⟨fd_word (by simpa [chanOffFd] using F.fd) console, ?_, ?_, ?_⟩
  · rw [ConsoleWrite.bv_add_toNat (by omega), read8_value]; rfl
  · rw [ConsoleWrite.bv_add_toNat (by omega), read8_value]
    apply BitVec.eq_of_toNat_eq
    have cw := F.curr
    simp only [chanOffCurr, chanOffBuff, hcur] at cw
    change (word c (chB.toNat + 24)).toNat = _
    have bl := F.cursorLe; rw [hcur] at bl; simp only [ioBufferSize] at bl
    rw [cw, BitVec.toNat_add, b72, BitVec.toNat_ofNat]; omega
  · rw [ConsoleWrite.bv_add_toNat (by omega), read8_value]
    apply BitVec.eq_of_toNat_eq
    have ew := F.bufEnd
    simp only [chanOffEnd, chanOffBuff, ioBufferSize] at ew
    change (word c (chB.toNat + 16)).toNat = _
    rw [ew, BitVec.toNat_add, b72]; simp; omega

/-- The loop registers survive a call that restores `s3`–`s11` and leaves the
HTIF device idle. -/
theorem LoopRegisters.of_restored {c e : Config} (loop : LoopRegisters c)
    (regs : ∀ n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], gpr e n = gpr c n)
    (idle : e.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes = some 0#4)
    (gp : gpr e 3 = gpr c 3) : LoopRegisters e where
  dispatchTable := (regs _ (by decide)).trans loop.dispatchTable
  opcodeBound := (regs _ (by decide)).trans loop.opcodeBound
  pending := (regs _ (by decide)).trans loop.pending
  domain := (regs _ (by decide)).trans loop.domain
  htifIdle := idle
  saved n hn := by
    have sub : ∀ n ∈ unpinnedSaved, n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27] := by decide
    rw [regs n (sub n hn)]; exact loop.saved n hn
  gp := gp.trans loop.gp

/-- A signed 64-bit add of a small count that does not overflow. -/
theorem toInt_add_small (x : BitVec 64) (n : Nat) (hn : n < 2 ^ 62) (h : x.toInt + n < 2 ^ 63) :
    (x + BitVec.ofNat 64 n).toInt = x.toInt + n := by
  have lo := BitVec.le_toInt x
  have hi := @BitVec.toInt_lt 64 x
  have h1 : (BitVec.ofNat 64 n).toInt = n := by
    rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Int.bmod_def]
    split <;> omega
  rw [BitVec.toInt_add, h1, Int.bmod_def]
  simp at lo hi
  split <;> omega

theorem bytesToString_append (a b : List UInt8) : bytesToString (a ++ b) = bytesToString a ++ bytesToString b := by
  simp [bytesToString, String.ofList_append]

/-- `consoleWindows` as a write log (the values are irrelevant): the footprint
of every console primitive's framed post. -/
def consoleLog (sp a : Nat) : List WEntry :=
  [(sp - 512, 512, 0#64), (Layout.sym_errno, 4, 0#64), (Layout.sym_impure_data, 4, 0#64),
   (a + 8, 8, 0#64), (a + 24, 8, 0#64), (a + 72, ioBufferSize, 0#64)]

/-- A byte frame on the console footprint is a getD frame on its windows. -/
theorem frameOnD_of_consoleLog {c e : Config} {sp a : Nat} (room : 512 ≤ sp)
    (memory : ∀ x, OutL (consoleLog sp a) x → byte e x = byte c x) :
    FrameOnD (consoleWindows sp a) c.σ.mem e.σ.mem := by
  intro x hx
  simp only [consoleWindows, OutW, and_true] at hx
  have m := memory x (by simp only [consoleLog, OutL, and_true]; omega)
  rwa [byte_total, byte_total] at m

/-- The control and register facts of a console primitive's return:
`Val_unit`, `s0`–`s11` and `sp` restored, the HTIF device idle. -/
structure ConsoleRet (ra sp : BitVec 64) (c e : Config) : Prop where
  good : GoodState e.σ
  image : ExecutableImage e
  minstret : ∃ w, e.σ.regs.get? LeanRV64DExecutable.Register.minstret = some w
  tick : e.tick < 2
  idle : e.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes = some (0#4)
  pc : pcOf e = some ra
  result : gpr e 10 = some 1#64
  stack : gpr e 2 = some sp
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr e n = gpr c n
  gprs : GprsKept c e

/-- **A console primitive's framed post**: from its return, its byte frame
on the console footprint, and the one channel record it changes. -/
theorem framed_of_ret {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain entry : Nat} {env ra : BitVec 64} {c e : Config} {args : List Val} {name : String}
    {id ch : Nat} {chn chn' : Chan} {w' : World} {D : InvocationData}
    (setup : CcallSetupPost ra args L P s pl cp sp high domain entry env c)
    (inv : Invocation D c) (valid : NativeValid D) (high' : D.nativeSp ≤ Layout.sym_stack_top)
    (ret : ConsoleRet ra (BitVec.ofNat 64 D.nativeSp) c e)
    (memory : ∀ x, OutL (consoleLog D.nativeSp ch) x → byte e x = byte c x)
    (outside : PayloadChanOutside (consoleLog D.nativeSp ch) P s c pl cp sp id)
    (bindings : BindingsOutside (consoleLog D.nativeSp ch) P c)
    (stable : ConsoleStable L)
    (chan : s.world.chans[id]? = some chn) (record : cp id = some ch)
    (chans : w'.chans = s.world.chans.set id chn') (counter : w'.ooId = s.world.ooId)
    (rootsEq : roots P {s with world := w'} = roots P s)
    (repr : ChanAt e ch chn') (console : output e.σ = bytesToString w'.console)
    (sem : primF1Impl name args s.heap s.world = .ok Val.unit s.heap w') :
    FramedPrimitivePost L.runtimeOk P s pl cp sp high name args Val.unit 1#64 s.heap w'
      (consoleLog D.nativeSp ch) c ra e := by
  have hr := valid.headroom
  simp only [nativeHeadroom] at hr
  refine ⟨⟨ret.good, ret.image, ret.minstret, ret.tick, ret.pc, ret.result, memory, ?_⟩,
    ?_, bindings_frame_outsideLog setup.input.primitives bindings memory,
    ⟨ret.good, ret.image, stable P s c pl cp high id chn ch D.nativeSp setup.geometry setup.input.runtime
      chan record valid.headroom high' e
      (frameOnD_of_consoleLog (by simp only [Vsa.Sim.DlHeap.heapEnd] at hr; omega) memory)⟩,
    LoopRegisters.of_restored setup.input.loop (fun n hn => ret.saved n (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn ⊢; omega)) ret.idle ret.gprs.gp,
    rfl, sem, ret.gprs⟩
  · intro r hr
    simp only [callSavedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ret.saved 25 (by decide)
    · exact ret.saved 8 (by decide)
    · exact ret.saved 18 (by decide)
    · exact ret.stack.trans inv.stack.symm
  · exact (setup.input.data.frame_chan outside memory chans counter rootsEq record repr console).accu_int 0

/-- What a channel update keeps: the descriptor, direction and read-ahead. -/
structure ChanSame (chn chn' : Chan) : Prop where
  fd : chn'.fd = chn.fd
  isOut : chn'.isOut = chn.isOut
  inBuf : chn'.inBuf = chn.inBuf

/-- **A channel record after an update** of its `offset`/`curr` words and
buffer bytes: every other header word is copied. -/
theorem _root_.OCaml.Vm.ChanAt.update {c e : Config} {ch : Nat} {chn chn' : Chan} (repr : ChanAt c ch chn)
    (same : ChanSame chn chn')
    (keep : ∀ x, ch ≤ x → x < ch + 72 → (x < ch + 8 ∨ ch + 16 ≤ x) → (x < ch + 24 ∨ ch + 32 ≤ x) →
      byte e x = byte c x)
    (offset : (word e (ch + 8)).toInt = chn'.offset)
    (curr : (word e (ch + 24)).toNat = ch + 72 + chn'.cursor)
    (bytes : ∀ i (b : UInt8), chn'.buffer[i]? = some b → byte e (ch + 72 + i) = BitVec.ofNat 8 b.toNat)
    (cursorLe : chn'.cursor ≤ ioBufferSize) (bufferLe : chn'.buffer.length ≤ ioBufferSize) :
    ChanAt e ch chn' := by
  have F := repr.fields
  have copy := fun (k n : Nat) (lo : k + n ≤ 8 ∨ (16 ≤ k ∧ k + n ≤ 24) ∨ (32 ≤ k ∧ k + n ≤ 72)) =>
    (show Reloc.Copied c e (ch + k) (ch + k) n from fun j hj => keep _ (by omega) (by omega) (by omega) (by omega))
  refine ⟨?_, offset, curr, ?_, ?_, ?_, bytes, cursorLe, bufferLe, F.aligned⟩
  · rw [show word32 e (ch + chanOffFd) = word32 c (ch + chanOffFd) from
      Reloc.bytesT_congr (copy chanOffFd 4 (by simp only [chanOffFd]; omega)), same.fd]
    exact F.fd
  · rw [show word e (ch + chanOffMax) = word c (ch + chanOffMax) from
      Reloc.bytesT_congr (copy chanOffMax 8 (by simp only [chanOffMax]; omega)), same.fd, same.isOut, same.inBuf]
    exact F.max
  · rw [show word e (ch + chanOffEnd) = word c (ch + chanOffEnd) from
      Reloc.bytesT_congr (copy chanOffEnd 8 (by simp only [chanOffEnd]; omega))]
    exact F.bufEnd
  · rw [show word32 e (ch + chanOffFlags) = word32 c (ch + chanOffFlags) from
      Reloc.bytesT_congr (copy chanOffFlags 4 (by simp only [chanOffFlags]; omega))]
    exact F.flags

/-- **A channel record whose bytes are unchanged** (header and full buffer)
still represents the channel. -/
theorem _root_.OCaml.Vm.ChanAt.of_bytes {c e : Config} {ch : Nat} {chn : Chan} (repr : ChanAt c ch chn)
    (keep : ∀ x, ch ≤ x → x < ch + 72 + 65536 → byte e x = byte c x) : ChanAt e ch chn := by
  have F := repr.fields
  refine ChanAt.update repr ⟨rfl, rfl, rfl⟩ (fun x a b _ _ => keep x a (by omega)) ?_ ?_ ?_ F.cursorLe F.bufferLe
  · rw [show word e (ch + 8) = word c (ch + 8) from Reloc.bytesT_congr fun j hj => keep _ (by omega) (by omega)]
    simpa [chanOffOffset] using F.offset
  · rw [show word e (ch + 24) = word c (ch + 24) from Reloc.bytesT_congr fun j hj => keep _ (by omega) (by omega)]
    simpa [chanOffCurr, chanOffBuff] using F.curr
  · intro i b hb
    have hi := (List.getElem?_eq_some_iff.mp hb).1
    have bl := F.bufferLe; simp only [ioBufferSize] at bl
    rw [keep _ (by omega) (by omega)]
    simpa [chanOffBuff] using F.bytes i b hb

end OCaml.Vm.Sim
