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
`caml_ml_output_bytes`): the native stack below the C-call sp, newlib's two
`errno` words, the channel record's `offset` and `curr` words and its buffer. -/
def consoleWindows (sp a : Nat) : List W :=
  [⟨sp - 384, sp⟩, ⟨Layout.sym_errno, Layout.sym_errno + 4⟩,
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

/-- The loop registers survive a call that restores `s3`–`s11` and leaves the
HTIF device idle. -/
theorem LoopRegisters.of_restored {c e : Config} (loop : LoopRegisters c)
    (regs : ∀ n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], gpr e n = gpr c n)
    (idle : e.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes = some 0#4) : LoopRegisters e where
  dispatchTable := (regs _ (by decide)).trans loop.dispatchTable
  opcodeBound := (regs _ (by decide)).trans loop.opcodeBound
  pending := (regs _ (by decide)).trans loop.pending
  domain := (regs _ (by decide)).trans loop.domain
  htifIdle := idle
  saved n hn := by
    have sub : ∀ n ∈ unpinnedSaved, n ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27] := by decide
    rw [regs n (sub n hn)]; exact loop.saved n hn

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

end OCaml.Vm.Sim
