import OCaml.Vm.Sim.PrimMlFlush
import OCaml.Vm.Primitives.Console.OutputChar

/-! `caml_ml_output_char` at a `C_CALL2` site: the model inversion (room in
the buffer, or a full buffer written out first) and the byte the machine
stores for the character argument. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- `caml_ml_output_char`'s model: a channel and an int argument, `putChar`
of its low byte, `Val_unit`. -/
theorem output_char_semantics {a b v : Val} {h h' : Heap} {w w' : World}
    (sem : primF1Impl "caml_ml_output_char" [a, b] h w = .ok v h' w') :
    ∃ id n, chanOf? h a = some id ∧ intArg? b = some n ∧
      putChar w id (n % 256).toNat.toUInt8 = some w' ∧ v = Val.unit ∧ h' = h := by
  cases hc : chanOf? h a with
  | none => simp [primF1Impl, hc] at sem
  | some id =>
    cases hn : intArg? b with
    | none => simp [primF1Impl, hc, hn] at sem
    | some n =>
      cases hp : putChar w id (n % 256).toNat.toUInt8 with
      | none => simp [primF1Impl, hc, hn, hp] at sem
      | some w'' =>
        simp [primF1Impl, hc, hn, hp] at sem
        obtain ⟨rfl, rfl, rfl⟩ := sem
        exact ⟨id, n, rfl, rfl, hp, rfl, rfl⟩

/-- The two outcomes of `putChar` on an open output channel. -/
inductive PutCharCase (w : World) (id : Nat) (b : UInt8) (c : Chan) : World → Prop where
  /-- room in the buffer: the byte appended -/
  | room (len : c.buf.length < ioBufferSize) :
      PutCharCase w id b c (w.setChan id { c with buf := c.buf ++ [b] })
  /-- a full buffer: written out, then the byte alone -/
  | full (len : ioBufferSize ≤ c.buf.length) (fits : offsetFits c c.buf.length = true) {w'' : World}
      (write : writeFd w c.fd c.buf = some w'') :
      PutCharCase w id b c (w''.setChan id { c with buf := [b], offset := c.offset + c.buf.length })

/-- Invert `putChar`. -/
theorem putChar_cases {w w' : World} {id : Nat} {b : UInt8} (h : putChar w id b = some w') :
    ∃ c, w.chans[id]? = some c ∧ 0 ≤ c.fd ∧ c.isOut = true ∧ PutCharCase w id b c w' := by
  unfold putChar at h
  cases hc : w.chans[id]? with
  | none => simp [hc] at h
  | some c =>
    simp [hc] at h
    obtain ⟨⟨fd0, out⟩, h⟩ := h
    refine ⟨c, rfl, fd0, out, ?_⟩
    split at h
    · rename_i full
      split at h
      · cases h
      · rename_i fits
        cases hw : writeFd w c.fd c.buf with
        | none => rw [hw] at h; cases h
        | some w'' =>
          rw [hw] at h
          simp only [Option.bind, Option.some.injEq] at h
          subst h
          exact .full full (by simpa using fits) hw
    · rename_i room
      simp only [Option.some.injEq] at h
      subst h
      exact .room (by omega)

/-- **The stored byte**: `sb` of the untagged character argument is its low
byte, the model's `(n % 256)`. -/
theorem char_byte (n : BitVec 63) :
    Vsa.Sim.sbData (Functions.shift_bits_right_arith (tag64 n) 1#6) =
      BitVec.ofNat 8 ((n.toInt % 256).toNat.toUInt8).toNat := by
  have low : Vsa.Sim.sbData (Functions.shift_bits_right_arith (tag64 n) 1#6) = n.setWidth 8 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h1 : Sail.BitVec.toNatInt (1#6) = 1 := by decide
    simp [h1, Vsa.Sim.sbData, Functions.shift_bits_right_arith, tag64, Sail.BitVec.extractLsb,
      BitVec.getLsbD_sshiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend]
    have h8 : i < 8 := by omega
    simp [h8, show 1 + i < 64 by omega, show i < 63 by omega, show i ≤ 7 by omega, show i < 64 by omega]
  rw [low]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have byte : ((n.toInt % 256).toNat.toUInt8).toNat = (n.toInt % 256).toNat := by
    have lt : (n.toInt % 256).toNat < 256 := by omega
    rw [Nat.toUInt8, UInt8.toNat_ofNat']; omega
  rw [byte, BitVec.toInt_eq_toNat_cond]
  split <;> omega

/-- **The channel's record after a byte stored with room**: the byte at the
old `curr`, `curr + 1`, every other field kept. -/
theorem roomed_chanAt {c e : Config} {ch : Nat} {chn : Chan} {chB : BitVec 64} {b : UInt8}
    (repr : ChanAt c ch chn) (open_ : chn.fd ≠ -1) (out : chn.isOut = true)
    (room : chn.buf.length < ioBufferSize) (hc : chB.toNat = ch) (ram : ch + 72 + ioBufferSize < 2 ^ 64)
    (stored : (e.σ.mem[(chB + 72#64 + BitVec.ofNat 64 chn.buf.length).toNat]?).getD 0 = BitVec.ofNat 8 b.toNat)
    (curr : bytesVal .ld (OCaml.Vm.Primitives.read8 e.σ.mem (chB + 24#64).toNat) =
      chB + 72#64 + BitVec.ofNat 64 chn.buf.length + 1#64)
    (keep : ∀ x, ch ≤ x → x < ch + 72 + ioBufferSize → x ≠ ch + 72 + chn.buf.length →
      (x < ch + 24 ∨ ch + 32 ≤ x) → byte e x = byte c x) :
    ChanAt e ch { chn with buf := chn.buf ++ [b] } := by
  have F := repr.fields
  obtain ⟨hbuf, hcur⟩ := out_buffer open_ out
  simp only [ioBufferSize] at room ram keep
  have at72 : (chB + 72#64 + BitVec.ofNat 64 chn.buf.length).toNat = ch + 72 + chn.buf.length := by
    rw [ConsoleWrite.bv_add_toNat (by rw [ConsoleWrite.bv_add_toNat (by omega), hc]; omega),
      ConsoleWrite.bv_add_toNat (by omega), hc]
  have w24 : (word e (ch + 24)).toNat = ch + 72 + (chn.buf.length + 1) := by
    change (bytesT e.σ.mem (ch + 24) 8).toNat = _
    rw [← read8_value, show ch + 24 = (chB + 24#64).toNat by rw [ConsoleWrite.bv_add_toNat (by omega), hc],
      curr, ConsoleWrite.bv_add_toNat (by rw [at72]; omega), at72]
    omega
  refine repr.update (chn' := { chn with buf := chn.buf ++ [b] }) ⟨rfl, rfl, rfl⟩
    (fun x lo hi o k => keep x lo (by omega) (by omega) k) ?_ ?_ ?_ ?_ ?_
  · rw [show word e (ch + 8) = word c (ch + 8) from
      Reloc.bytesT_congr fun j hj => keep _ (by omega) (by omega) (by omega) (by omega)]
    simpa only [chanOffOffset] using F.offset
  · simp only [Chan.cursor, open_, out, ↓reduceIte, List.length_append, List.length_singleton]
    exact w24
  · intro i x hx
    simp only [Chan.buffer, open_, out, ↓reduceIte] at hx
    have hi := (List.getElem?_eq_some_iff.mp hx).1
    simp only [List.length_append, List.length_singleton] at hi
    by_cases last : i = chn.buf.length
    · subst last
      rw [byte_total, ← at72, stored]
      rw [List.getElem?_append_right (by omega)] at hx
      simp at hx
      rw [hx]
    · have lt : i < chn.buf.length := by omega
      rw [List.getElem?_append_left lt] at hx
      rw [keep _ (by omega) (by omega) (by omega) (by omega)]
      have := F.bytes i x (by rw [hbuf]; exact hx)
      simpa only [chanOffBuff] using this
  · simp [Chan.cursor, open_, out, ioBufferSize]; omega
  · simp [Chan.buffer, open_, out, ioBufferSize]; omega

/-- A clear unbuffered flag survives the signed word load. -/
theorem flags_word {c : Config} {a : Nat} (h : word32 c a &&& chanFlagUnbuffered = 0#32) :
    bytesVal .lw (OCaml.Vm.Primitives.read8 c.σ.mem a) &&& 16#64 = 0#64 := by
  rw [lw_read8]
  change LeanRV64DExecutable.Functions.sign_extend (m := 64) (word32 c a) &&& 16#64 = 0#64
  simp only [chanFlagUnbuffered] at h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (fun x => x.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this ⊢
  simp [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend]
  by_cases i4 : i = 4
  · subst i4; simpa using this
  · have key : ∀ j, j < 64 → j ≠ 4 → (16#64).getLsbD j = false := by decide
    simp [key i hi i4]

/-- **`caml_ml_output_char` with room in the buffer, framed.** -/
theorem oc_room_framed {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain : Nat} {env ra : BitVec 64} {c : Config} {args : List Val} {l a id ch : Nat} {chn : Chan}
    {D : InvocationData} {n : BitVec 63} {fd rp lr : BitVec 64}
    (setup : CcallSetupPost ra args L P s pl cp sp high domain 0x80016350 env c)
    (arg : ChannelArg s c pl cp l a id ch chn) (inv : Invocation D c) (valid : NativeValid D)
    (I : ConsoleWrite.OcInput ra (BitVec.ofNat 64 D.nativeSp) (BitVec.ofNat 64 a) (tag64 n) (word c (a + 8))
      fd rp (word c Layout.sym_Caml_state) lr chn.buf.length c)
    (open_ : chn.fd ≠ -1) (out : chn.isOut = true) (room : chn.buf.length < ioBufferSize)
    (outside : PayloadChanOutside (consoleLog D.nativeSp ch) P s c pl cp sp id)
    (bindings : BindingsOutside (consoleLog D.nativeSp ch) P c)
    (stable : ConsoleStable L)
    (sem : primF1Impl "caml_ml_output_char" args s.heap s.world = .ok Val.unit s.heap
      (s.world.setChan id { chn with buf := chn.buf ++ [(n.toInt % 256).toNat.toUInt8] })) :
    FnSummary (BitVec.ofNat 64 0x80016350) (fun x => x = c)
      (FramedPrimitivePost L.runtimeOk P s pl cp sp high "caml_ml_output_char" args Val.unit 1#64 s.heap
        (s.world.setChan id { chn with buf := chn.buf ++ [(n.toInt % 256).toNat.toUInt8] })
        (consoleLog D.nativeSp ch) c ra) := by
  have G := (console_geometry setup.geometry arg valid).lits
  have F := arg.repr.fields
  obtain ⟨hbuf, hcur⟩ := out_buffer open_ out
  have OL := I.layout
  have bs := OL.bufStack
  have br := OL.bufRoots
  have bram := OL.bufRam
  have nlow := G.low
  have nhigh := G.high
  have chh := G.chanHigh
  have hc : (word c (a + 8)).toNat = ch := arg.pointer
  have hs : (BitVec.ofNat 64 D.nativeSp).toNat = D.nativeSp := by rw [BitVec.toNat_ofNat]; omega
  rw [hc] at bs br bram
  rw [hs] at bs
  have dh := G.domHigh
  have hd : (word c Layout.sym_Caml_state + 288#64).toNat = (word c Layout.sym_Caml_state).toNat + 288 := by
    rw [ConsoleWrite.bv_add_toNat (by omega)]
  simp only [ioBufferSize] at room
  have off : ∀ k, k ≤ 72 → (word c (a + 8) + BitVec.ofNat 64 k).toNat = ch + k := fun k hk => by
    rw [ConsoleWrite.bv_add_toNat (by rw [hc]; omega), hc]
  have currWord : bytesVal .ld (OCaml.Vm.Primitives.read8 c.σ.mem (word c (a + 8) + 24#64).toNat) =
      word c (a + 8) + 72#64 + BitVec.ofNat 64 chn.buf.length := by
    rw [off 24 (by decide), read8_value]
    apply BitVec.eq_of_toNat_eq
    have cw := F.curr
    simp only [chanOffCurr, chanOffBuff, hcur] at cw
    change (word c (ch + 24)).toNat = _
    rw [cw, ConsoleWrite.bv_add_toNat (by rw [off 72 (by decide)]; omega), off 72 (by decide)]
  have endWord : bytesVal .ld (OCaml.Vm.Primitives.read8 c.σ.mem (word c (a + 8) + 16#64).toNat) =
      word c (a + 8) + 72#64 + 65536#64 := by
    rw [off 16 (by decide), read8_value]
    apply BitVec.eq_of_toNat_eq
    have ew := F.bufEnd
    simp only [chanOffEnd, chanOffBuff, ioBufferSize] at ew
    change (word c (ch + 16)).toNat = _
    rw [ew, ConsoleWrite.bv_add_toNat (by rw [off 72 (by decide)]; omega), off 72 (by decide)]
  have flags : bytesVal .lw (OCaml.Vm.Primitives.read8 c.σ.mem (word c (a + 8) + 68#64).toNat) &&& 16#64 = 0#64 := by
    rw [off 68 (by decide)]; exact flags_word (by simpa only [chanOffFlags] using F.flags)
  refine ⟨fun c0 ⟨pc0, e0⟩ => ?_⟩
  subst c0
  obtain ⟨e, run, post, outEq⟩ := ConsoleWrite.oc_room I pc0 room currWord endWord flags
  have byteAt : (word c (a + 8) + 72#64 + BitVec.ofNat 64 chn.buf.length).toNat = ch + 72 + chn.buf.length := by
    rw [ConsoleWrite.bv_add_toNat (by rw [off 72 (by decide)]; omega), off 72 (by decide)]
  have frame : ∀ x, (x < D.nativeSp - 112 ∨ D.nativeSp ≤ x) → x ≠ ch + 72 + chn.buf.length →
      (x < ch + 24 ∨ ch + 32 ≤ x) →
      (x < (word c Layout.sym_Caml_state).toNat + 288 ∨ (word c Layout.sym_Caml_state).toNat + 296 ≤ x) →
      (e.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := fun x st ne cu ro =>
    post.frame x (by rw [hs]; exact st) (by rw [byteAt]; exact ne) (by rw [hc]; exact cu) ro
  have memory : ∀ x, OutL (consoleLog D.nativeSp ch) x → byte e x = byte c x := by
    apply footprint_memory (dom := (word c Layout.sym_Caml_state).toNat) (lr := lr)
    · have r := I.rootsWord; rw [hd, read8_value] at r; exact r
    · have r := post.roots; rw [hd, read8_value] at r; exact r
    · intro x hx hr
      simp only [consoleLog, OutL, Layout.sym_errno, Layout.sym_impure_data, ioBufferSize, and_true] at hx
      exact frame x (by omega) (by omega) (by omega) hr
  have repr' := roomed_chanAt (b := (n.toInt % 256).toNat.toUInt8) arg.repr open_ out
    (by simp only [ioBufferSize]; omega) hc (by simp only [ioBufferSize]; omega)
    (by rw [post.byte, char_byte]) post.curr
    (fun x lo hi ne cu => by
      simp only [ioBufferSize] at hi
      rw [byte_total, byte_total]
      exact frame x (by omega) ne cu (by omega))
  exact ⟨e, run, framed_of_ret setup inv valid (by simp only [Layout.sym_stack_top]; omega)
    ⟨post.good, post.image, post.minstret, post.tick, post.idle, post.pc, post.result, post.stack, post.saved, post.gprs⟩
    memory outside bindings stable arg.chan arg.record rfl rfl rfl repr'
    (outEq.trans setup.input.data.world.output) sem⟩

/-- **The channel's record after a byte stored into a full buffer**: the old
buffer written out (`offset` advanced), the byte at the buffer's start,
`curr` one past it. -/
theorem fulled_chanAt {c e : Config} {ch : Nat} {chn : Chan} {chB : BitVec 64} {b : UInt8}
    (repr : ChanAt c ch chn) (open_ : chn.fd ≠ -1) (out : chn.isOut = true)
    (fits : offsetFits chn chn.buf.length = true) (hc : chB.toNat = ch) (ram : ch + 72 + ioBufferSize < 2 ^ 64)
    (stored : (e.σ.mem[(chB + 72#64 + BitVec.ofNat 64 0).toNat]?).getD 0 = BitVec.ofNat 8 b.toNat)
    (curr : bytesVal .ld (OCaml.Vm.Primitives.read8 e.σ.mem (chB + 24#64).toNat) =
      chB + 72#64 + BitVec.ofNat 64 0 + 1#64)
    (offset : bytesVal .ld (OCaml.Vm.Primitives.read8 e.σ.mem (chB + 8#64).toNat) =
      word c (ch + 8) + BitVec.ofNat 64 chn.buf.length)
    (keep : ∀ x, ch ≤ x → x < ch + 72 → (x < ch + 8 ∨ ch + 16 ≤ x) → (x < ch + 24 ∨ ch + 32 ≤ x) →
      byte e x = byte c x) :
    ChanAt e ch { chn with buf := [b], offset := chn.offset + chn.buf.length } := by
  have F := repr.fields
  have len := F.bufferLe
  obtain ⟨hbuf, hcur⟩ := out_buffer open_ out
  rw [hbuf] at len
  simp only [ioBufferSize] at len ram
  have fits' : chn.offset + chn.buf.length < 2 ^ 63 := of_decide_eq_true fits
  have at72 : (chB + 72#64 + BitVec.ofNat 64 0).toNat = ch + 72 := by
    rw [BitVec.add_zero, ConsoleWrite.bv_add_toNat (by omega), hc]
  have w8 : word e (ch + 8) = word c (ch + 8) + BitVec.ofNat 64 chn.buf.length := by
    change bytesT e.σ.mem (ch + 8) 8 = _
    rw [← read8_value, ← offset, show (chB + 8#64).toNat = ch + 8 by
      rw [ConsoleWrite.bv_add_toNat (by omega), hc]]
  have w24 : (word e (ch + 24)).toNat = ch + 72 + 1 := by
    change (bytesT e.σ.mem (ch + 24) 8).toNat = _
    rw [← read8_value, show ch + 24 = (chB + 24#64).toNat by rw [ConsoleWrite.bv_add_toNat (by omega), hc],
      curr, ConsoleWrite.bv_add_toNat (by rw [at72]; omega), at72]
  have off := F.offset
  simp only [chanOffOffset] at off
  refine repr.update (chn' := { chn with buf := [b], offset := chn.offset + chn.buf.length }) ⟨rfl, rfl, rfl⟩
    keep ?_ ?_ ?_ ?_ ?_
  · rw [w8, toInt_add_small _ _ (by omega) (by omega), off]
  · rw [w24]; simp [Chan.cursor, open_, out]
  · intro i x hx
    simp only [Chan.buffer, open_, out, ↓reduceIte] at hx
    have hi := (List.getElem?_eq_some_iff.mp hx).1
    simp only [List.length_singleton] at hi
    have i0 : i = 0 := by omega
    subst i0
    simp at hx
    rw [byte_total, Nat.add_zero, ← at72, stored, hx]
  · simp [Chan.cursor, open_, out, ioBufferSize]
  · simp [Chan.buffer, open_, out, ioBufferSize]

/-- **`caml_ml_output_char` on a full buffer, framed**: the buffer written to
the console, then the byte at the buffer's start. -/
theorem oc_full_framed {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain : Nat} {env ra : BitVec 64} {c : Config} {args : List Val} {l a id ch : Nat} {chn : Chan}
    {D : InvocationData} {n : BitVec 63} {lr : BitVec 64} {st : TCB.Os.Stream}
    (setup : CcallSetupPost ra args L P s pl cp sp high domain 0x80016350 env c)
    (arg : ChannelArg s c pl cp l a id ch chn) (inv : Invocation D c) (valid : NativeValid D)
    (rt : ConsoleWrite.ConsoleRuntime c) (console : chn.fd = 1 ∨ chn.fd = 2) (out : chn.isOut = true)
    (I : ConsoleWrite.OcInput ra (BitVec.ofNat 64 D.nativeSp) (BitVec.ofNat 64 a) (tag64 n) (word c (a + 8))
      (BitVec.ofInt 64 chn.fd) ConsoleWrite.impureData (word c Layout.sym_Caml_state) lr chn.buf.length c)
    (full : chn.buf.length = ioBufferSize) (fits : offsetFits chn chn.buf.length = true) (streamOut : st ≠ .stdin)
    (outside : PayloadChanOutside (consoleLog D.nativeSp ch) P s c pl cp sp id)
    (bindings : BindingsOutside (consoleLog D.nativeSp ch) P c)
    (stable : ConsoleStable L)
    (sem : primF1Impl "caml_ml_output_char" args s.heap s.world = .ok Val.unit s.heap
      ((ConsoleWrite.wroteWorld s.world st chn.buf).setChan id
        { chn with buf := [(n.toInt % 256).toNat.toUInt8], offset := chn.offset + chn.buf.length })) :
    FnSummary (BitVec.ofNat 64 0x80016350) (fun x => x = c)
      (FramedPrimitivePost L.runtimeOk P s pl cp sp high "caml_ml_output_char" args Val.unit 1#64 s.heap
        ((ConsoleWrite.wroteWorld s.world st chn.buf).setChan id
          { chn with buf := [(n.toInt % 256).toNat.toUInt8], offset := chn.offset + chn.buf.length })
        (consoleLog D.nativeSp ch) c ra) := by
  have G := (console_geometry setup.geometry arg valid).lits
  have F := arg.repr.fields
  have open_ : chn.fd ≠ -1 := by omega
  obtain ⟨hbuf, hcur⟩ := out_buffer open_ out
  have FM := flush_mem setup arg valid rt console out
  have nlow := G.low
  have nhigh := G.high
  have chh := G.chanHigh
  have chd := G.chanDom
  have chl := G.chanLow
  have dh := G.domHigh
  rw [hbuf, full] at chh chd
  simp only [ioBufferSize] at full chh chd
  have hc : (word c (a + 8)).toNat = ch := arg.pointer
  have hs : (BitVec.ofNat 64 D.nativeSp).toNat = D.nativeSp := by rw [BitVec.toNat_ofNat]; omega
  have hd : (word c Layout.sym_Caml_state + 288#64).toNat = (word c Layout.sym_Caml_state).toNat + 288 := by
    rw [ConsoleWrite.bv_add_toNat (by omega)]
  have off : ∀ k, k ≤ 72 → (word c (a + 8) + BitVec.ofNat 64 k).toNat = ch + k := fun k hk => by
    rw [ConsoleWrite.bv_add_toNat (by rw [hc]; omega), hc]
  have endWord : bytesVal .ld (OCaml.Vm.Primitives.read8 c.σ.mem (word c (a + 8) + 16#64).toNat) =
      word c (a + 8) + 72#64 + 65536#64 := by
    rw [off 16 (by decide), read8_value]
    apply BitVec.eq_of_toNat_eq
    have ew := F.bufEnd
    simp only [chanOffEnd, chanOffBuff, ioBufferSize] at ew
    change (word c (ch + 16)).toNat = _
    rw [ew, ConsoleWrite.bv_add_toNat (by rw [off 72 (by decide)]; omega), off 72 (by decide)]
  have flags : bytesVal .lw (OCaml.Vm.Primitives.read8 c.σ.mem (word c (a + 8) + 68#64).toNat) &&& 16#64 = 0#64 := by
    rw [off 68 (by decide)]; exact flags_word (by simpa only [chanOffFlags] using F.flags)
  refine ⟨fun c0 ⟨pc0, e0⟩ => ?_⟩
  subst c0
  obtain ⟨e, run, post⟩ := ConsoleWrite.oc_full I pc0 FM full endWord flags
  have C := ConsoleWrite.consoleLits
  have byteAt : (word c (a + 8) + 72#64 + BitVec.ofNat 64 0).toNat = ch + 72 := by
    rw [BitVec.add_zero, off 72 (by decide)]
  have frame : ∀ x, (x < D.nativeSp - 384 ∨ D.nativeSp ≤ x) → (x < 0x80064d48 ∨ 0x80064d48 + 4 ≤ x) →
      (x < 0x80064668 ∨ 0x80064668 + 4 ≤ x) → (x < ch + 8 ∨ ch + 16 ≤ x) → (x < ch + 24 ∨ ch + 32 ≤ x) →
      x ≠ ch + 72 →
      (x < (word c Layout.sym_Caml_state).toNat + 288 ∨ (word c Layout.sym_Caml_state).toNat + 296 ≤ x) →
      (e.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := fun x st er rp o k ne ro =>
    post.frame x (by rw [hs]; exact st) (by rw [C.errno]; exact er) (by rw [C.impureData]; exact rp)
      (by rw [hc]; exact o) (by rw [hc]; exact k) (by rw [byteAt]; exact ne) ro
  have memory : ∀ x, OutL (consoleLog D.nativeSp ch) x → byte e x = byte c x := by
    apply footprint_memory (dom := (word c Layout.sym_Caml_state).toNat) (lr := lr)
    · have r := I.rootsWord; rw [hd, read8_value] at r; exact r
    · have r := post.roots; rw [hd, read8_value] at r; exact r
    · intro x hx hr
      simp only [consoleLog, OutL, Layout.sym_errno, Layout.sym_impure_data, ioBufferSize, and_true] at hx
      exact frame x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hr
  have repr' := fulled_chanAt (b := (n.toInt % 256).toNat.toUInt8) arg.repr open_ out fits hc
    (by simp only [ioBufferSize]; omega) (by rw [post.byte, char_byte]) post.curr post.offset
    (fun x lo hi o k => by
      rw [byte_total, byte_total]
      exact frame x (by omega) (by omega) (by omega) o k (by omega) (by omega))
  have console' : output e.σ = bytesToString ((ConsoleWrite.wroteWorld s.world st chn.buf).setChan id
      { chn with buf := [(n.toInt % 256).toNat.toUInt8], offset := chn.offset + chn.buf.length }).console := by
    change output e.σ = bytesToString (ConsoleWrite.wroteWorld s.world st chn.buf).console
    rw [ConsoleWrite.wroteWorld_console _ _ streamOut, bytesToString_append, ← setup.input.data.world.output]
    exact post.output
  exact ⟨e, run, framed_of_ret setup inv valid (by simp only [Layout.sym_stack_top]; omega)
    ⟨post.good, post.image, post.minstret, post.tick, post.idle, post.pc, post.result, post.stack, post.saved, post.gprs⟩
    memory outside bindings stable arg.chan arg.record rfl rfl rfl repr' console' sem⟩

/-- **`caml_ml_output_char`'s input** at a represented console channel and an
int argument, from the geometry of the channel's whole record. -/
theorem oc_input {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain entry : Nat} {env ra : BitVec 64} {c : Config} {args : List Val} {l a id ch : Nat}
    {chn : Chan} {D : InvocationData} {n : BitVec 63}
    (setup : CcallSetupPost ra args L P s pl cp sp high domain entry env c)
    (arg : ChannelArg s c pl cp l a id ch chn) (inv : Invocation D c) (valid : NativeValid D)
    (rt : ConsoleWrite.ConsoleRuntime c) (console : chn.fd = 1 ∨ chn.fd = 2) (out : chn.isOut = true)
    (G : ConsoleWrite.ConsoleGeometry D.nativeSp ch (word c Layout.sym_Caml_state).toNat a 65536)
    (second : args[1]? = some (.int n))
    (saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], (gprGet c.σ n).isSome) :
    ConsoleWrite.OcInput ra (BitVec.ofNat 64 D.nativeSp) (BitVec.ofNat 64 a) (tag64 n) (word c (a + 8))
      (BitVec.ofInt 64 chn.fd) ConsoleWrite.impureData (word c Layout.sym_Caml_state)
      (word c ((word c Layout.sym_Caml_state).toNat + 288)) chn.buf.length c := by
  have GL := G.lits
  have open_ : chn.fd ≠ -1 := by omega
  obtain ⟨hbuf, hcur⟩ := out_buffer open_ out
  have len := arg.repr.bufferLe
  rw [hbuf] at len
  simp only [ioBufferSize] at len
  have hfd : BitVec.ofInt 64 chn.fd = 1#64 ∨ BitVec.ofInt 64 chn.fd = 2#64 := by
    rcases console with e | e <;> rw [e] <;> decide
  have hs : (BitVec.ofNat 64 D.nativeSp).toNat = D.nativeSp := by
    rw [BitVec.toNat_ofNat]; have := GL.high; omega
  have hv : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; have := GL.valHigh; omega
  have charReg : gpr c (10 + 1) = some (tag64 n) := setup.input.arguments.get second rfl
  exact
    { flush_entry setup arg inv valid saved with
      charReg := charReg
      layout := G.ocLayout arg.pointer hv rfl hs hfd len
      lockNull := rt.lockNull
      unlockNull := rt.unlockNull }

end OCaml.Vm.Sim
