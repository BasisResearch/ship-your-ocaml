import OCaml.Vm.Sim.ConsoleCall
import OCaml.RefinementF1
import OCaml.Vm.Sim.PrimMlOutputChar
import OCaml.Vm.Primitives.Flush.MlOutput
import OCaml.Vm.Primitives.StringContract
import OCaml.Vm.Sim.PrimMlFlush
import OCaml.Vm.Primitives.Console.OutputBytes
import OCaml.Vm.Primitives.Console.World

/-! `caml_ml_output_bytes`' copy loop against the model's `putBlock`: each
iteration either appends the remaining bytes to the buffer (room) or fills
the buffer, writes it to the console and continues with the rest. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable
open ConsoleWrite (ObHead ObSource ConsoleGeometry ObInput)

/-- **The copy loop's state** at `t` (the loop head or its exit): the
machine loop state, `bs` still to copy from `str + p`, the model channel
`chn` in world `w` represented at `ch`, the console as the model's. -/
structure ObLoop (t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v : BitVec 64) (v id : Nat)
    (st : TCB.Os.Stream) (c0 : Config) (w : World) (chn : Chan) (bs : List UInt8) (p : Nat) (d : Config) :
    Prop where
  head : ObHead t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v (BitVec.ofNat 64 bs.length)
    (BitVec.ofNat 64 p) c0 d
  geo : ConsoleGeometry sp.toNat ch.toNat dom.toNat v 65536
  chan : w.chans[id]? = some chn
  repr : ChanAt d ch.toNat chn
  console : chn.fd = 1 ∨ chn.fd = 2
  out : chn.isOut = true
  stream : TCB.Os.lookupFd w.os chn.fd.toNat = some (.stream st)
  live : w.os.proc.exited = none
  streamOut : st ≠ .stdin
  output : Vsa.Machine.output d.σ = bytesToString w.console
  source : ObSource ch (str.toNat + p) bs.length
  sourceRoots : str.toNat + p + bs.length ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ str.toNat + p
  bytes : ∀ i (x : UInt8), bs[i]? = some x → byte c0 (str.toNat + p + i) = BitVec.ofNat 8 x.toNat
  rt : ConsoleWrite.ConsoleRuntime c0
  gprs : GprsKept c0 d

/-- A source byte reads as at the loop's entry. -/
theorem ObLoop.byte_now {t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v : BitVec 64} {v id : Nat}
    {st : TCB.Os.Stream} {c0 : Config} {w : World} {chn : Chan} {bs : List UInt8} {p : Nat} {d : Config}
    (L : ObLoop t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 w chn bs p d)
    {j : Nat} (hj : j < bs.length) : byte d (str.toNat + p + j) = byte c0 (str.toNat + p + j) := by
  have G := L.geo.lits
  have l1 := G.low; have l4 := G.chanHigh; have l5 := G.chanLow; have l8 := G.domHigh; have l7 := G.domLow
  have lo := L.source.low; have hi := L.source.high; have ap := L.source.apart; have rr := L.sourceRoots
  simp only [Layout.sym_bss_end, DlHeap.heapEnd] at lo hi
  rw [byte_total, byte_total]
  exact L.head.frame _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- `str + p` as the machine's source register holds it. -/
theorem ObLoop.src_toNat {t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v : BitVec 64} {v id : Nat}
    {st : TCB.Os.Stream} {c0 : Config} {w : World} {chn : Chan} {bs : List UInt8} {p : Nat} {d : Config}
    (L : ObLoop t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 w chn bs p d) :
    (BitVec.ofNat 64 p + str).toNat = str.toNat + p := by
  have lo := L.source.low; have hi := L.source.high
  simp only [Layout.sym_bss_end, DlHeap.heapEnd] at lo hi
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- A chunk below `2^31`: the source lies in the heap. -/
theorem ObLoop.small {t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v : BitVec 64} {v id : Nat}
    {st : TCB.Os.Stream} {c0 : Config} {w : World} {chn : Chan} {bs : List UInt8} {p : Nat} {d : Config}
    (L : ObLoop t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 w chn bs p d) :
    bs.length < 2 ^ 31 := by
  have lo := L.source.low; have hi := L.source.high
  simp only [Layout.sym_bss_end, DlHeap.heapEnd] at lo hi
  omega

/-- The console statics at any loop state: the loop writes none of them. -/
theorem ObHead.runtime {t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos : BitVec 64} {v : Nat}
    {c0 d : Config} (H : ObHead t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos c0 d)
    (geo : ConsoleGeometry sp.toNat ch.toNat dom.toNat v 65536) (rt : ConsoleWrite.ConsoleRuntime c0) :
    ConsoleWrite.ConsoleRuntime d := by
  have G := geo.lits
  have l1 := G.low; have l5 := G.chanLow; have l7 := G.domLow
  refine OCaml.Vm.Gc.ConsoleRuntime.transfer (fun x hx sa => Reloc.bytesT_congr fun j hj => ?_) rt
  have er := sa ⟨Layout.sym_errno, Layout.sym_errno + 4⟩ (by simp [OCaml.Vm.Gc.ignoredStatics])
  have im := sa ⟨Layout.sym_impure_data, Layout.sym_impure_data + 4⟩ (by simp [OCaml.Vm.Gc.ignoredStatics])
  simp only [Layout.sym_errno, Layout.sym_impure_data, Layout.sym_bss_end] at er im hx
  change byte d (x + j) = byte c0 (x + j)
  rw [byte_total, byte_total]
  exact H.frame _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- **The room iteration**: the remaining bytes fit; they are appended to
the buffer and the loop exits. -/
theorem ob_iter_room {ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v : BitVec 64} {v id : Nat}
    {st : TCB.Os.Stream} {c0 : Config} {w : World} {chn : Chan} {bs : List UInt8} {p : Nat} {d : Config}
    (L : ObLoop 0x80016600#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 w chn bs p d)
    (ready : LibraryReady d) (room : bs.length < ioBufferSize - chn.buf.length) :
    ∃ e, Steps d e ∧ ObLoop 0x80016658#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0
      (w.setChan id { chn with buf := chn.buf ++ bs }) { chn with buf := chn.buf ++ bs } [] (p + bs.length) e := by
  have G := L.geo.lits
  have l1 := G.low; have l4 := G.chanHigh; have l5 := G.chanLow; have l8 := G.domHigh; have l7 := G.domLow
  have cd := G.chanDom
  have F := L.repr.fields
  have open_ : chn.fd ≠ -1 := by have := L.console; omega
  obtain ⟨hbuf, hcur⟩ := out_buffer open_ L.out
  have W := ChanAt.words L.repr L.console L.out (by omega)
  simp only [ioBufferSize] at room
  have small := L.small
  have hs := L.src_toNat
  obtain ⟨e1, run1, S⟩ := ConsoleWrite.ob_small L.geo L.head small ready
  obtain ⟨e2, run2, T⟩ := ConsoleWrite.ob_test (k := chn.buf.length) true L.geo S.head S.eight S.eleven S.fifteen
    small (by omega) (by rw [S.memory]; exact W.curr) (by rw [S.memory]; exact W.bufEnd)
    (by simp; omega) S.ready
  rw [if_pos rfl] at T
  have lo := L.source.low; have hi := L.source.high; have ap := L.source.apart
  simp only [Layout.sym_bss_end, DlHeap.heapEnd] at lo hi
  obtain ⟨e3, run3, H3, C⟩ := ConsoleWrite.ob_room L.geo T.head T.eight T.twelve T.ten T.fifteen (by omega)
    (by rw [hs]; exact L.source) (by rw [T.memory, S.memory]; exact W.curr) T.ready
  have mem2 : ∀ x, byte e2 x = byte d x := fun x => by simp only [byte, T.memory, S.memory]
  have keep3 : ∀ x, (x < ch.toNat + 72 + chn.buf.length ∨ ch.toNat + 72 + chn.buf.length + bs.length ≤ x) →
      (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → byte e3 x = byte d x := fun x a b => (C.kept x a b).trans (mem2 x)
  have h24 : (ch + 24#64).toNat = ch.toNat + 24 := ConsoleWrite.bv_add_toNat (by omega)
  have outN : chn.buf.length + bs.length ≤ 65536 := by omega
  refine ⟨e3, run1.trans (run2.trans run3), ?_, L.geo, ?_, ?_, L.console, L.out, L.stream, L.live, L.streamOut, ?_,
    ⟨by simp only [Layout.sym_bss_end]; omega, by simp only [DlHeap.heapEnd, List.length_nil]; omega,
      by simp only [List.length_nil]; omega⟩,
    by have rr := L.sourceRoots; simp only [List.length_nil]; omega, fun i x hx => by simp at hx,
    L.rt,
    L.gprs.trans (S.gprs.trans (T.gprs.trans C.gprs))⟩
  · rw [List.length_nil, BitVec.ofNat_add]; exact H3
  · obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp L.chan
    simp [World.setChan, List.getElem?_set_self hlt]
  · refine ChanAt.update L.repr ⟨rfl, rfl, rfl⟩ (fun x _ _ a b => keep3 x (Or.inl (by omega)) (by omega))
      ?_ ?_ ?_ ?_ ?_
    · rw [show word e3 (ch.toNat + 8) = word d (ch.toNat + 8) from
        Reloc.bytesT_congr fun j hj => keep3 _ (Or.inl (by omega)) (Or.inl (by omega))]
      simpa [chanOffOffset] using F.offset
    · have cw := C.currWord
      rw [read8_value, h24] at cw
      change (Vsa.Sim.bytesT e3.σ.mem (ch.toNat + 24) 8).toNat = _
      rw [cw]
      simp only [Chan.cursor, open_, L.out, ↓reduceIte, List.length_append]
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add]; simp; omega
    · intro i b hb
      simp only [Chan.buffer, open_, L.out, ↓reduceIte] at hb
      by_cases hi : i < chn.buf.length
      · rw [List.getElem?_append_left hi] at hb
        rw [keep3 _ (Or.inl (by omega)) (Or.inr (by omega))]
        exact F.bytes i b (by rw [hbuf]; exact hb)
      · rw [List.getElem?_append_right (by omega)] at hb
        have hj := (List.getElem?_eq_some_iff.mp hb).1
        have cp := C.copied (i - chn.buf.length) hj
        rw [show ch.toNat + 72 + chn.buf.length + (i - chn.buf.length) = ch.toNat + 72 + i by omega] at cp
        rw [cp, mem2, hs, L.byte_now hj]
        exact L.bytes _ b hb
    · simp only [Chan.cursor, open_, L.out, ↓reduceIte, List.length_append, ioBufferSize]; omega
    · simp only [Chan.buffer, open_, L.out, ↓reduceIte, List.length_append, ioBufferSize]; omega
  · rw [C.output, T.output, S.output, L.output]; rfl

/-- **The full iteration**: the buffer's free space is filled from the
source, the whole buffer is written to the console, and the loop goes on with
the rest (or exits when nothing is left). -/
theorem ob_iter_full {ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v : BitVec 64} {v id : Nat}
    {st : TCB.Os.Stream} {c0 : Config} {w : World} {chn : Chan} {bs : List UInt8} {p : Nat} {d : Config}
    (L : ObLoop 0x80016600#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 w chn bs p d)
    (ready : LibraryReady d) (full : ioBufferSize - chn.buf.length ≤ bs.length)
    (fits : offsetFits chn (chn.buf ++ bs.take (ioBufferSize - chn.buf.length)).length = true) :
    ∃ e, Steps d e ∧ ObLoop (if decide (0 < bs.length - (ioBufferSize - chn.buf.length)) then 0x80016600#64
        else 0x80016658#64) ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0
      ((ConsoleWrite.wroteWorld w st (chn.buf ++ bs.take (ioBufferSize - chn.buf.length))).setChan id
        (ConsoleWrite.filledChan chn bs))
      (ConsoleWrite.filledChan chn bs) (bs.drop (ioBufferSize - chn.buf.length))
      (p + (ioBufferSize - chn.buf.length)) e ∧ LibraryReady e := by
  have G := L.geo.lits
  have l1 := G.low; have l4 := G.chanHigh; have l5 := G.chanLow; have l8 := G.domHigh; have l7 := G.domLow
  have cd := G.chanDom
  have F := L.repr.fields
  have open_ : chn.fd ≠ -1 := by have := L.console; omega
  obtain ⟨hbuf, hcur⟩ := out_buffer open_ L.out
  have W := ChanAt.words L.repr L.console L.out (by omega)
  have bufLe := F.bufferLe
  rw [hbuf] at bufLe
  simp only [ioBufferSize] at full fits bufLe
  have fits' : chn.offset + (chn.buf ++ bs.take (65536 - chn.buf.length)).length < 2 ^ 63 := of_decide_eq_true fits
  have small := L.small
  have hs := L.src_toNat
  have lo := L.source.low; have hi := L.source.high; have ap := L.source.apart; have rr := L.sourceRoots
  simp only [Layout.sym_bss_end, DlHeap.heapEnd] at lo hi
  have fullLen : (chn.buf ++ bs.take (65536 - chn.buf.length)).length = 65536 := by
    simp only [List.length_append, List.length_take]; omega
  obtain ⟨e1, run1, S⟩ := ConsoleWrite.ob_small L.geo L.head small ready
  obtain ⟨e2, run2, T⟩ := ConsoleWrite.ob_test (k := chn.buf.length) false L.geo S.head S.eight S.eleven S.fifteen
    small (by omega) (by rw [S.memory]; exact W.curr) (by rw [S.memory]; exact W.bufEnd)
    (by simp; omega) S.ready
  rw [if_neg (by decide)] at T
  obtain ⟨e3, run3, H3, n19, C, ready3⟩ := ConsoleWrite.ob_fill L.geo T.head T.ten T.eleven T.nineteen (by omega)
    (by rw [hs]; exact ⟨by simp only [Layout.sym_bss_end]; omega, by simp only [DlHeap.heapEnd]; omega,
      by omega⟩)
    (by rw [T.memory, S.memory]; exact W.curr) T.ready
  have mem2 : ∀ x, byte e2 x = byte d x := fun x => by simp only [byte, T.memory, S.memory]
  have keep3 : ∀ x, (x < ch.toNat + 72 + chn.buf.length ∨
      ch.toNat + 72 + chn.buf.length + (65536 - chn.buf.length) ≤ x) →
      (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → byte e3 x = byte d x := fun x a b => (C.kept x a b).trans (mem2 x)
  have rd3 : ∀ a, a + 8 ≤ ch.toNat + 72 → (a + 8 ≤ ch.toNat + 24 ∨ ch.toNat + 32 ≤ a) →
      OCaml.Vm.Primitives.read8 e3.σ.mem a = OCaml.Vm.Primitives.read8 d.σ.mem a := fun a x y =>
    ConsoleWrite.read8_same fun i hi => by rw [← byte_total, ← byte_total]; exact keep3 _ (Or.inl (by omega)) (by omega)
  have h8 : (ch + 8#64).toNat = ch.toNat + 8 := ConsoleWrite.bv_add_toNat (by omega)
  have h16 : (ch + 16#64).toNat = ch.toNat + 16 := ConsoleWrite.bv_add_toNat (by omega)
  have h24 : (ch + 24#64).toNat = ch.toNat + 24 := ConsoleWrite.bv_add_toNat (by omega)
  have hfd : BitVec.ofInt 64 chn.fd = 1#64 ∨ BitVec.ofInt 64 chn.fd = 2#64 := by
    rcases L.console with e | e <;> rw [e] <;> decide
  obtain ⟨e4, run4, H4, eight4, Wr⟩ := ConsoleWrite.ob_flushed (off := word d (ch.toNat + 8))
    (bs := chn.buf ++ bs.take (65536 - chn.buf.length)) L.geo H3 n19 (ObHead.runtime H3 L.geo L.rt) hfd
    (by rw [rd3 _ (by omega) (Or.inl (by omega))]; exact W.fd)
    (by rw [h16, rd3 _ (by omega) (Or.inl (by omega)), ← h16]; exact W.bufEnd)
    (by have wo := W.offset; rw [h8] at wo ⊢; rw [rd3 _ (by omega) (Or.inl (by omega))]; exact wo) fullLen
    (by
      intro i x hx
      have hi' := (List.getElem?_eq_some_iff.mp hx).1
      rw [fullLen] at hi'
      rw [show (ch + 72#64 + BitVec.ofNat 64 i).toNat = ch.toNat + 72 + i by
        rw [ConsoleWrite.bv_add_toNat (by rw [ConsoleWrite.bv_add_toNat (by omega)]; omega),
          ConsoleWrite.bv_add_toNat (by omega)], ← byte_total]
      by_cases hk : i < chn.buf.length
      · rw [List.getElem?_append_left hk] at hx
        rw [keep3 _ (Or.inl (by omega)) (Or.inr (by omega))]
        exact F.bytes i x (by rw [hbuf]; exact hx)
      · rw [List.getElem?_append_right (by omega)] at hx
        have hj : i - chn.buf.length < 65536 - chn.buf.length := by omega
        rw [List.getElem?_take_of_lt hj] at hx
        have hr := (List.getElem?_eq_some_iff.mp hx).1
        have cp := C.copied (i - chn.buf.length) hj
        rw [show ch.toNat + 72 + chn.buf.length + (i - chn.buf.length) = ch.toNat + 72 + i by omega] at cp
        rw [cp, mem2, hs, L.byte_now hr]
        exact L.bytes _ x hx)
    (fun n hn => ready3.gprs n (by simp at hn; omega) (by simp at hn; omega))
  have subN : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (65536 - chn.buf.length) =
      BitVec.ofNat 64 (bs.length - (65536 - chn.buf.length)) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  rw [subN] at H4
  obtain ⟨e5, run5, N⟩ := ConsoleWrite.ob_next (decide (0 < bs.length - (65536 - chn.buf.length))) L.geo H4 eight4
    (ConsoleWrite.blt_small_zero _ (by omega))
  -- the record header outside `offset`/`curr` is as at the loop's start
  have hdr : ∀ x, ch.toNat ≤ x → x < ch.toNat + 72 → (x < ch.toNat + 8 ∨ ch.toNat + 16 ≤ x) →
      (x < ch.toNat + 24 ∨ ch.toNat + 32 ≤ x) → byte e5 x = byte d x := fun x a b o k => by
    rw [byte_total, byte_total,
      N.head.frame x (by omega) (by omega) (by omega) o k (by omega) (by omega),
      L.head.frame x (by omega) (by omega) (by omega) o k (by omega) (by omega)]
  have word4 : ∀ a, word e5 a = word e4 a := fun a => by simp only [word, N.memory]
  refine ⟨e5, run1.trans (run2.trans (run3.trans (run4.trans run5))), ⟨?_, L.geo, ?_, ?_, L.console, L.out,
    L.stream, L.live, L.streamOut, ?_,
    ⟨by simp only [Layout.sym_bss_end, ioBufferSize]; omega,
      by simp only [DlHeap.heapEnd, List.length_drop, ioBufferSize]; omega,
      by simp only [List.length_drop, ioBufferSize]; omega⟩,
    by simp only [List.length_drop, ioBufferSize]; omega, ?_, L.rt,
    L.gprs.trans (S.gprs.trans (T.gprs.trans (C.gprs.trans (Wr.gprs.trans N.gprs))))⟩,
    ready3.of_kept (Wr.gprs.trans N.gprs) N.head.idle⟩
  · rw [List.length_drop, BitVec.ofNat_add]; exact N.head
  · obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp L.chan
    simp [World.setChan, ConsoleWrite.wroteWorld_chans, List.getElem?_set_self hlt]
  · refine ChanAt.update L.repr ⟨rfl, rfl, rfl⟩ hdr ?_ ?_ ?_ ?_ ?_
    · rw [word4]
      change (Vsa.Sim.bytesT e4.σ.mem (ch.toNat + 8) 8).toInt = _
      rw [← h8, ← read8_value, Wr.offset, fullLen]
      have fo := F.offset; simp only [chanOffOffset] at fo
      simp only [ConsoleWrite.filledChan, ioBufferSize]
      rw [fullLen, toInt_add_small _ _ (by omega) (by rw [fo]; omega), fo]
    · rw [word4]
      change (Vsa.Sim.bytesT e4.σ.mem (ch.toNat + 24) 8).toNat = _
      rw [← h24, ← read8_value, Wr.curr, ConsoleWrite.bv_add_toNat (by omega)]
      simp [ConsoleWrite.filledChan, Chan.cursor, open_, L.out]
    · intro i b hb; simp [ConsoleWrite.filledChan, Chan.buffer, open_, L.out] at hb
    · simp [ConsoleWrite.filledChan, Chan.cursor, open_, L.out, ioBufferSize]
    · simp [ConsoleWrite.filledChan, Chan.buffer, open_, L.out, ioBufferSize]
  · rw [N.output, Wr.output, C.output, T.output, S.output, L.output]
    show _ = bytesToString (ConsoleWrite.wroteWorld w st _).console
    rw [ConsoleWrite.wroteWorld_console _ _ L.streamOut, bytesToString_append, bytesToString_append,
      bytesToString_append]; rfl
  · intro i x hx
    simp only [ioBufferSize] at hx ⊢
    rw [List.getElem?_drop] at hx
    rw [show str.toNat + (p + (65536 - chn.buf.length)) + i = str.toNat + p + (65536 - chn.buf.length + i) by omega]
    exact L.bytes _ x hx

/-- `caml_ml_output_bytes` returned: the console return, nothing written
outside the console footprint, the final channel record and console. -/
structure ObDone (ra sp ch : BitVec 64) (chn : Chan) (w : World) (c e : Config) : Prop where
  ret : ConsoleRet ra sp c e
  memory : ∀ x, OutL (consoleLog sp.toNat ch.toNat) x → byte e x = byte c x
  repr : ChanAt e ch.toNat chn
  console : Vsa.Machine.output e.σ = bytesToString w.console

/-- A word read outside the loop's windows reads as at the entry. -/
theorem ObHead.read_entry {t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos : BitVec 64}
    {c0 d : Config} (H : ObHead t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v rem pos c0 d) {a : Nat}
    (x : a + 8 ≤ sp.toNat - 512) (er : a + 8 ≤ 0x80064d48 ∨ 0x80064d48 + 4 ≤ a)
    (im : a + 8 ≤ 0x80064668 ∨ 0x80064668 + 4 ≤ a) (c8 : a + 8 ≤ ch.toNat + 8 ∨ ch.toNat + 16 ≤ a)
    (c24 : a + 8 ≤ ch.toNat + 24 ∨ ch.toNat + 32 ≤ a) (bu : a + 8 ≤ ch.toNat + 72 ∨ ch.toNat + 72 + 65536 ≤ a)
    (ro : a + 8 ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ a) :
    OCaml.Vm.Primitives.read8 d.σ.mem a = OCaml.Vm.Primitives.read8 c0.σ.mem a :=
  ConsoleWrite.read8_same fun i hi => H.frame _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

/-- **Leave the copy loop and return**: reload the saved registers, check the
unbuffered flag, restore `local_roots`. -/
theorem ob_finish {ra sp v str ofs len ch dom lr : BitVec 64} {vN id p : Nat} {st : TCB.Os.Stream}
    {c0 : Config} {w : World} {chn : Chan} {d : Config}
    (I : ObInput ra sp v str ofs len ch dom lr c0)
    (L : ObLoop 0x80016658#64 ra sp ch dom lr str ((gpr c0 9).getD 0) ((gpr c0 18).getD 0) ((gpr c0 20).getD 0)
      ((gpr c0 21).getD 0) ((gpr c0 23).getD 0) ((gpr c0 8).getD 0) ((gpr c0 19).getD 0) ((gpr c0 22).getD 0)
      vN id st c0 w chn [] p d) :
    ∃ e, Steps d e ∧ ObDone ra sp ch chn w c0 e := by
  have G := I.geo.lits
  have l1 := G.low; have l2 := G.high; have l4 := G.chanHigh; have l5 := G.chanLow; have l8 := G.domHigh
  have l7 := G.domLow; have cd := G.chanDom
  have C := ConsoleWrite.consoleLits
  have H := L.head
  have present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr c0 n = some ((gpr c0 n).getD 0) := by
    intro n hn
    have := I.saved n hn
    change gprGet c0.σ n = some ((gprGet c0.σ n).getD 0)
    cases e : gprGet c0.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  have c68 : (ch + 68#64).toNat = ch.toNat + 68 := ConsoleWrite.bv_add_toNat (by omega)
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := ConsoleWrite.bv_add_toNat (by omega)
  obtain ⟨e1, run1, E, R⟩ := ConsoleWrite.ob_restore L.geo H
    (by rw [show (0x80064d08#64 : BitVec 64).toNat = 0x80064d08 from rfl,
          ObHead.read_entry H (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), ← C.state]
        exact I.domWord)
    (by rw [show (0x80064b50#64 : BitVec 64).toNat = 0x80064b50 from rfl,
          ObHead.read_entry H (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), ← C.unlock]
        exact I.unlockNull)
    (by
      have b4 : Vsa.Sim.bytesT d.σ.mem (ch.toNat + 68) 4 = Vsa.Sim.bytesT c0.σ.mem (ch.toNat + 68) 4 :=
        Reloc.bytesT_congr fun j hj => by
          change byte d _ = byte c0 _
          rw [byte_total, byte_total]
          exact H.frame _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have fl := I.flagsClear
      rw [c68, lw_read8] at fl ⊢
      rw [b4]; exact fl)
  obtain ⟨e2, run2, Rt⟩ := ConsoleWrite.ob_exit L.geo I.aligned E
  have mem1 : ∀ x, byte e1 x = byte d x := fun x => by simp only [byte, R.memory]
  have frame2 : ∀ x, (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) → byte e2 x = byte d x := fun x hx => by
    rw [byte_total, byte_total, Rt.frame x hx, ← byte_total, ← byte_total]; exact mem1 x
  refine ⟨e2, run1.trans run2, ⟨Rt.good, Rt.image, Rt.minstret, Rt.tick, Rt.idle, Rt.pc, Rt.result, Rt.stack, ?_,
    L.gprs.trans (R.gprs.trans Rt.gprs)⟩, ?_, ?_, ?_⟩
  · intro n hn
    have k := fun (m : Nat) (hm : m ∉ [1, 2, 9, 10, 15, 18, 20, 21, 23]) (lo : 1 ≤ m) (hi : m ≤ 31) =>
      Rt.kept m lo hi hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [k 8 (by simp) (by decide) (by decide), R.s0]; exact (present 8 (by simp)).symm
    · rw [Rt.s1]; exact (present 9 (by simp)).symm
    · rw [Rt.s2]; exact (present 18 (by simp)).symm
    · rw [k 19 (by simp) (by decide) (by decide), R.s3]; exact (present 19 (by simp)).symm
    · rw [Rt.s4]; exact (present 20 (by simp)).symm
    · rw [Rt.s5]; exact (present 21 (by simp)).symm
    · rw [k 22 (by simp) (by decide) (by decide), R.s6]; exact (present 22 (by simp)).symm
    · rw [Rt.s7]; exact (present 23 (by simp)).symm
    all_goals first
      | (rw [k 24 (by simp) (by decide) (by decide)]; exact R.kept 24 (by simp))
      | (rw [k 25 (by simp) (by decide) (by decide)]; exact R.kept 25 (by simp))
      | (rw [k 26 (by simp) (by decide) (by decide)]; exact R.kept 26 (by simp))
      | (rw [k 27 (by simp) (by decide) (by decide)]; exact R.kept 27 (by simp))
  · apply footprint_memory (dom := dom.toNat) (lr := lr)
    · rw [← read8_value, ← r288]; exact I.rootsWord
    · rw [← read8_value, ← r288]; exact Rt.roots
    · intro x hx hr
      simp only [consoleLog, OutL, Layout.sym_errno, Layout.sym_impure_data, ioBufferSize] at hx
      rw [← byte_total, ← byte_total, frame2 x hr, byte_total, byte_total]
      exact H.frame x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hr
  · exact ChanAt.of_bytes L.repr fun x a b => frame2 x (by omega)
  · rw [Rt.output, R.output, L.output]

/-- The copy loop's measure, read off the machine: twice the remaining
length, plus one while the buffer is full (a full buffer is flushed before
anything is copied). -/
def obMeasure (ch : BitVec 64) (d : Config) : Nat :=
  2 * ((gpr d 9).getD 0).toNat +
    (if bytesVal .ld (OCaml.Vm.Primitives.read8 d.σ.mem (ch + 24#64).toNat) = ch + 72#64 + 65536#64 then 1 else 0)

theorem ObLoop.measure {t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v : BitVec 64} {v id : Nat}
    {st : TCB.Os.Stream} {c0 : Config} {w : World} {chn : Chan} {bs : List UInt8} {p : Nat} {d : Config}
    (L : ObLoop t ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 w chn bs p d) :
    obMeasure ch d = 2 * bs.length + (if chn.buf.length = 65536 then 1 else 0) := by
  have G := L.geo.lits
  have l4 := G.chanHigh
  have W := ChanAt.words L.repr L.console L.out (by omega)
  have F := L.repr.fields
  have open_ : chn.fd ≠ -1 := by have := L.console; omega
  obtain ⟨hbuf, -⟩ := out_buffer open_ L.out
  have bl := F.bufferLe; rw [hbuf] at bl; simp only [ioBufferSize] at bl
  have small := L.small
  unfold obMeasure
  rw [L.head.remReg, W.curr]
  simp only [Option.getD_some, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  congr 1
  by_cases hk : chn.buf.length = 65536
  · simp [hk]
  · rw [if_neg hk, if_neg]
    intro h
    have h' := congrArg (fun x => (x - (ch + 72#64)).toNat) h
    simp at h'; omega

/-- The copy loop's states towards the final model world `wF`: running at
the head with `putBlock` still to reach `wF`, or done at the exit. -/
inductive ObState (ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v : BitVec 64) (v id : Nat)
    (st : TCB.Os.Stream) (c0 : Config) (wF : World) : Config → Prop where
  | running {d : Config} (w : World) (chn : Chan) (bs : List UInt8) (p fuel : Nat)
      (L : ObLoop 0x80016600#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 w chn bs p d)
      (ready : LibraryReady d) (ne : bs ≠ []) (model : putBlock w id bs fuel = some wF) :
      ObState ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 wF d
  | done {d : Config} (chn : Chan) (p : Nat)
      (L : ObLoop 0x80016658#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 wF chn [] p d) :
      ObState ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 wF d

/-- One iteration of the copy loop, against `putBlock`. -/
theorem ob_step {ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v : BitVec 64} {v id : Nat}
    {st : TCB.Os.Stream} {c0 : Config} {wF w : World} {chn : Chan} {bs : List UInt8} {p fuel : Nat} {d : Config}
    (L : ObLoop 0x80016600#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 w chn bs p d)
    (ready : LibraryReady d) (ne : bs ≠ []) (model : putBlock w id bs fuel = some wF) :
    ∃ e, Steps d e ∧ ObState ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 wF e ∧
      obMeasure ch e < obMeasure ch d := by
  obtain ⟨f, rfl⟩ := ConsoleWrite.putBlock_fuel ne model
  have fd0 : 0 ≤ chn.fd := by have := L.console; omega
  have pos : 0 < bs.length := List.length_pos_iff.mpr ne
  have μ := L.measure
  by_cases room : bs.length < ioBufferSize - chn.buf.length
  · obtain ⟨e, run, L'⟩ := ob_iter_room L ready room
    rw [ConsoleWrite.putBlock_room L.chan fd0 L.out ne room] at model
    cases model
    refine ⟨e, run, .done _ _ L', ?_⟩
    rw [L'.measure, μ]
    simp only [ioBufferSize] at room
    simp only [List.length_nil, List.length_append]
    rw [if_neg (by omega)]; omega
  · have full : ioBufferSize - chn.buf.length ≤ bs.length := by omega
    have fits := ConsoleWrite.putBlock_full_fits L.chan fd0 L.out ne full model
    have write := ConsoleWrite.writeFd_stream fd0 L.live L.stream L.streamOut
      (b := chn.buf ++ bs.take (ioBufferSize - chn.buf.length))
    rw [ConsoleWrite.putBlock_full L.chan fd0 L.out ne full fits write] at model
    obtain ⟨e, run, L', ready'⟩ := ob_iter_full L ready full fits
    have bl : chn.buf.length ≤ 65536 := by
      have F := L.repr.fields
      have open_ : chn.fd ≠ -1 := by omega
      obtain ⟨hbuf, -⟩ := out_buffer open_ L.out
      have := F.bufferLe; rw [hbuf] at this; simpa [ioBufferSize] using this
    simp only [ioBufferSize] at full room
    by_cases more : 0 < bs.length - (ioBufferSize - chn.buf.length)
    · rw [if_pos (by simpa using more)] at L'
      refine ⟨e, run, .running _ _ _ _ _ L' ready' ?_ model, ?_⟩
      · intro h; have := congrArg List.length h; simp [ioBufferSize] at this more; omega
      · rw [L'.measure, μ]
        simp only [ConsoleWrite.filledChan, List.length_nil, List.length_drop, ioBufferSize]
        by_cases hk : chn.buf.length = 65536
        · rw [if_pos hk]; simp; omega
        · rw [if_neg hk]; simp; omega
    · rw [if_neg (by simpa using more)] at L'
      have nil : bs.drop (ioBufferSize - chn.buf.length) = [] := by
        apply List.drop_eq_nil_of_le; simp only [ioBufferSize] at more ⊢; omega
      rw [nil] at L' model
      rw [ConsoleWrite.putBlock_nil] at model
      cases model
      refine ⟨e, run, .done _ _ L', ?_⟩
      rw [L'.measure, μ]
      simp only [ConsoleWrite.filledChan, List.length_nil]
      simp; omega

/-- **The copy loop**: from a running state, the machine reaches the loop's
exit with the model's final world. -/
theorem ob_loop {ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v : BitVec 64} {v id : Nat}
    {st : TCB.Os.Stream} {c0 : Config} {wF : World} {d : Config}
    (start : ObState ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 wF d) :
    ∃ e, Steps d e ∧ ∃ chn p,
      ObLoop 0x80016658#64 ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 wF chn [] p e := by
  have body : ∀ n, Vsa.Logic.Triple
      (fun e => ObState ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 wF e ∧
        pcOf e = some 0x80016600#64 ∧ obMeasure ch e = n)
      (fun e => ObState ra sp ch dom lr str s1v s2v s4v s5v s7v s0v s3v s6v v id st c0 wF e ∧
        obMeasure ch e < n) := by
    intro n e pre
    obtain ⟨state, head, measure⟩ := pre
    cases state with
    | running w chn bs p fuel L ready ne model =>
      obtain ⟨e', run, state', lt⟩ := ob_step L ready ne model
      exact ⟨e', run, state', measure ▸ lt⟩
    | done chn p L => exact absurd (L.head.pc.symm.trans head) (by decide)
  obtain ⟨e, run, state, stopped⟩ := Vsa.Sim.loopFromBody (obMeasure ch) body d start
  cases state with
  | running _ _ _ _ _ L _ _ _ => exact absurd L.head.pc stopped
  | done chn p L => exact ⟨e, run, chn, p, L⟩

/-- The model facts at `caml_ml_output_bytes`' entry: the channel `chn` of
world `w` represented at `ch` on a console stream, the `bs` to write at
`str + p` in the heap, and the console statics. -/
structure ObModel (ch dom str : BitVec 64) (id : Nat) (st : TCB.Os.Stream) (w : World) (chn : Chan)
    (bs : List UInt8) (p : Nat) (c : Config) : Prop where
  chan : w.chans[id]? = some chn
  repr : ChanAt c ch.toNat chn
  console : chn.fd = 1 ∨ chn.fd = 2
  out : chn.isOut = true
  stream : TCB.Os.lookupFd w.os chn.fd.toNat = some (.stream st)
  live : w.os.proc.exited = none
  streamOut : st ≠ .stdin
  output : Vsa.Machine.output c.σ = bytesToString w.console
  source : ObSource ch (str.toNat + p) bs.length
  sourceRoots : str.toNat + p + bs.length ≤ dom.toNat + 288 ∨ dom.toNat + 296 ≤ str.toNat + p
  bytes : ∀ i (x : UInt8), bs[i]? = some x → byte c (str.toNat + p + i) = BitVec.ofNat 8 x.toNat
  rt : ConsoleWrite.ConsoleRuntime c
  ready : LibraryReady c

/-- **An empty write**: `caml_ml_output_bytes` with length zero goes straight
to the flag test and returns, writing nothing but its frame. -/
theorem ob_empty {ra sp v str ch dom lr : BitVec 64} {no nl : BitVec 63} {c : Config} {w : World} {chn : Chan}
    (I : ObInput ra sp v str (tag64 no) (tag64 nl) ch dom lr c) (entry : pcOf c = some 0x8001652c#64)
    (lenNonneg : 0 ≤ nl.toInt) (zero : nl.toNat = 0) (repr : ChanAt c ch.toNat chn)
    (output : Vsa.Machine.output c.σ = bytesToString w.console) :
    ∃ e, Steps c e ∧ ObDone ra sp ch chn w c e := by
  have G := I.geo.lits
  have l1 := G.low; have l2 := G.high; have l4 := G.chanHigh; have l5 := G.chanLow; have l8 := G.domHigh
  have l7 := G.domLow; have cd := G.chanDom
  have hlen : Functions.shift_bits_right_arith (tag64 nl) 1#6 = BitVec.ofNat 64 nl.toNat := by
    rw [ConsoleWrite.untag_shift, ConsoleWrite.signExtend_nonneg _ lenNonneg]
  obtain ⟨d1, run1, P⟩ := ConsoleWrite.ob_pro I entry
  have pro : ∀ x, (x < sp.toNat - 176 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
      byte d1 x = byte c x := fun x a b => by rw [byte_total, byte_total]; exact P.outside x a b
  obtain ⟨d2, run2, E, Q⟩ := ConsoleWrite.ob_none I P (by rw [hlen, ConsoleWrite.bge_zero _ (by omega)]; simp [zero])
  obtain ⟨e, run3, Rt⟩ := ConsoleWrite.ob_exit I.geo I.aligned E
  have mem2 : ∀ x, byte d2 x = byte d1 x := fun x => by simp only [byte, Q.memory]
  have frame : ∀ x, (x < sp.toNat - 176 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
      byte e x = byte c x := fun x a b => by
    rw [byte_total, Rt.frame x b, ← byte_total, mem2, pro x a b]
  have present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gpr c n = some ((gpr c n).getD 0) := by
    intro n hn
    have := I.saved n hn
    change gprGet c.σ n = some ((gprGet c.σ n).getD 0)
    cases e : gprGet c.σ n with
    | none => rw [e] at this; cases this
    | some v => rfl
  have r288 : (dom + 288#64).toNat = dom.toNat + 288 := ConsoleWrite.bv_add_toNat (by omega)
  refine ⟨e, run1.trans (run2.trans run3), ⟨Rt.good, Rt.image, Rt.minstret, Rt.tick, Rt.idle, Rt.pc,
    Rt.result, Rt.stack, ?_, P.gprs.trans (Q.gprs.trans Rt.gprs)⟩, ?_, ?_, ?_⟩
  · intro n hn
    have k := fun (m : Nat) (hm : m ∉ [1, 2, 9, 10, 15, 18, 20, 21, 23]) (hp : m ∉ [2, 6, 9, 14, 15, 16, 17, 18, 20,
        21, 23, 28, 29, 30]) (lo : 1 ≤ m) (hi : m ≤ 31) =>
      (Rt.kept m lo hi hm).trans ((Q.regs m lo hi).trans (P.kept m lo hi hp))
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact k 8 (by simp) (by simp) (by decide) (by decide)
    · rw [Rt.s1]; exact (present 9 (by simp)).symm
    · rw [Rt.s2]; exact (present 18 (by simp)).symm
    · exact k 19 (by simp) (by simp) (by decide) (by decide)
    · rw [Rt.s4]; exact (present 20 (by simp)).symm
    · rw [Rt.s5]; exact (present 21 (by simp)).symm
    · exact k 22 (by simp) (by simp) (by decide) (by decide)
    · rw [Rt.s7]; exact (present 23 (by simp)).symm
    all_goals first
      | exact k 24 (by simp) (by simp) (by decide) (by decide)
      | exact k 25 (by simp) (by simp) (by decide) (by decide)
      | exact k 26 (by simp) (by simp) (by decide) (by decide)
      | exact k 27 (by simp) (by simp) (by decide) (by decide)
  · apply footprint_memory (dom := dom.toNat) (lr := lr)
    · rw [← read8_value, ← r288]; exact I.rootsWord
    · rw [← read8_value, ← r288]; exact Rt.roots
    · intro x hx hr
      simp only [consoleLog, OutL] at hx
      rw [← byte_total, ← byte_total]; exact frame x (by omega) hr
  · exact ChanAt.of_bytes repr fun x a b => frame x (by omega) (by omega)
  · rw [Rt.output, Q.output, P.output, output]

/-- **`caml_ml_output_bytes` against `putBlock`**: from its entry, the
machine returns with the channel and console of the model's final world. -/
theorem ob_bytes {ra sp v str ch dom lr : BitVec 64} {no nl : BitVec 63} {id fuel : Nat} {st : TCB.Os.Stream}
    {c : Config} {w wF : World} {chn : Chan} {bs : List UInt8}
    (I : ObInput ra sp v str (tag64 no) (tag64 nl) ch dom lr c) (entry : pcOf c = some 0x8001652c#64)
    (ofsNonneg : 0 ≤ no.toInt) (lenNonneg : 0 ≤ nl.toInt) (len : bs.length = nl.toNat)
    (M : ObModel ch dom str id st w chn bs no.toNat c) (model : putBlock w id bs fuel = some wF) :
    ∃ e chnF, Steps c e ∧ ObDone ra sp ch chnF wF c e ∧ wF.chans[id]? = some chnF := by
  have G := I.geo.lits
  have l1 := G.low; have l2 := G.high; have l4 := G.chanHigh; have l5 := G.chanLow; have l8 := G.domHigh
  have l7 := G.domLow; have cd := G.chanDom
  have lo := M.source.low; have hi := M.source.high
  simp only [Layout.sym_bss_end, DlHeap.heapEnd] at lo hi
  have small : bs.length < 2 ^ 31 := by omega
  have hlen : Functions.shift_bits_right_arith (tag64 nl) 1#6 = BitVec.ofNat 64 bs.length := by
    rw [ConsoleWrite.untag_shift, ConsoleWrite.signExtend_nonneg _ lenNonneg, len]
  have hofs : Functions.shift_bits_right_arith (tag64 no) 1#6 = BitVec.ofNat 64 no.toNat := by
    rw [ConsoleWrite.untag_shift, ConsoleWrite.signExtend_nonneg _ ofsNonneg]
  obtain ⟨d1, run1, P⟩ := ConsoleWrite.ob_pro I entry
  -- bytes the prologue leaves alone
  have pro : ∀ x, (x < sp.toNat - 176 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
      byte d1 x = byte c x := fun x a b => by rw [byte_total, byte_total]; exact P.outside x a b
  by_cases zero : bs = []
  · -- nothing to write
    subst zero
    rw [ConsoleWrite.putBlock_nil] at model
    cases model
    obtain ⟨e, run, D⟩ := ob_empty I entry lenNonneg (by rw [← len]; rfl) M.repr M.output
    exact ⟨e, chn, run, D, M.chan⟩
  · -- copy loop
    obtain ⟨d2, run2, H, En⟩ := ConsoleWrite.ob_go I P (by rw [hlen, ConsoleWrite.bge_zero _ small]; simpa using zero)
    rw [hlen, hofs] at H
    have frame : ∀ x, (x < sp.toNat - 176 ∨ sp.toNat ≤ x) → (x < dom.toNat + 288 ∨ dom.toNat + 296 ≤ x) →
        byte d2 x = byte c x := fun x a b => by rw [byte_total, byte_total]; exact En.outside x a b
    have L : ObLoop 0x80016600#64 ra sp ch dom lr str ((gpr c 9).getD 0) ((gpr c 18).getD 0) ((gpr c 20).getD 0)
        ((gpr c 21).getD 0) ((gpr c 23).getD 0) ((gpr c 8).getD 0) ((gpr c 19).getD 0) ((gpr c 22).getD 0)
        v.toNat id st c w chn bs no.toNat d2 :=
      { head := H, geo := I.geo, chan := M.chan, console := M.console, out := M.out, stream := M.stream,
        live := M.live, streamOut := M.streamOut, source := M.source, sourceRoots := M.sourceRoots,
        bytes := M.bytes, rt := M.rt, gprs := P.gprs.trans En.gprs
        repr := ChanAt.of_bytes M.repr fun x a b => frame x (by omega) (by omega)
        output := by rw [En.output, P.output, M.output] }
    obtain ⟨d3, run3, chnF, pF, Lf⟩ := ob_loop (.running w chn bs no.toNat fuel L
      (M.ready.of_kept (P.gprs.trans En.gprs) H.idle) zero model)
    obtain ⟨e, run4, D⟩ := ob_finish I Lf
    exact ⟨e, chnF, run1.trans (run2.trans (run3.trans run4)), D, Lf.chan⟩

/-- `caml_ml_output`'s model: a channel, a byte slice of a string at
nonnegative offset and length, `putBlock` of the slice, `Val_unit`. -/
theorem output_semantics {a b o n v : Val} {h h' : Heap} {w w' : World}
    (sem : primF1Impl "caml_ml_output" [a, b, o, n] h w = .ok v h' w') :
    ∃ id chn oi ni bs, chanOf? h a = some id ∧ w.chans[id]? = some chn ∧ intArg? o = some oi ∧
      intArg? n = some ni ∧ 0 ≤ oi ∧ 0 ≤ ni ∧
      byteSlice? h b oi.toNat ni.toNat = some bs ∧ putBlock w id bs (ni.toNat + 1) = some w' ∧
      v = Val.unit ∧ h' = h := by
  cases hc : chanOf? h a with
  | none => simp [primF1Impl, hc] at sem
  | some id =>
    cases hk : w.chans[id]? with
    | none => simp [primF1Impl, hc, hk] at sem
    | some chn =>
    cases ho : intArg? o with
    | none => simp [primF1Impl, hc, hk, ho] at sem
    | some oi =>
      cases hn : intArg? n with
      | none => simp [primF1Impl, hc, hk, ho, hn] at sem
      | some ni =>
        by_cases pos : 0 ≤ oi ∧ 0 ≤ ni
        · cases hs : byteSlice? h b oi.toNat ni.toNat with
          | none => simp [primF1Impl, hc, hk, ho, hn, pos, hs] at sem
          | some bs =>
            cases hp : putBlock w id bs (ni.toNat + 1) with
            | none => simp [primF1Impl, hc, hk, ho, hn, pos, hs, hp] at sem
            | some w'' =>
              simp [primF1Impl, hc, hk, ho, hn, pos, hs, hp] at sem
              obtain ⟨rfl, rfl, rfl⟩ := sem
              exact ⟨id, chn, oi, ni, bs, rfl, hk, rfl, rfl, pos.1, pos.2, hs, hp, rfl, rfl⟩
        · simp [primF1Impl, hc, hk, ho, hn, pos] at sem

theorem mapM_id_get : ∀ (cells : List (Option UInt8)) (bs : List UInt8), cells.mapM id = some bs →
    ∀ (i : Nat) (x : UInt8), bs[i]? = some x → cells[i]? = some (some x)
  | [], bs, h, i, x, hx => by simp at h; subst h; simp at hx
  | c :: cs, bs, h, i, x, hx => by
    cases c with
    | none => simp at h
    | some y =>
      cases e : cs.mapM id with
      | none => simp [e] at h
      | some ys =>
        simp [e] at h; subst h
        cases i with
        | zero => simpa using hx
        | succ i => simpa using mapM_id_get cs ys e i x (by simpa using hx)

/-- **A byte slice of a placed string** lies in its block, byte for byte. -/
theorem slice_bytes {c : Config} {pl : Place} {cp : ChanPlace} {h : Heap} {l a off n : Nat} {o : Obj}
    {bs : List UInt8} (layout : ObjAt c pl cp a o) (object : h.get? l = some o)
    (slice : byteSlice? h (.ptr l 0) off n = some bs) :
    bs.length = n ∧ off + n ≤ 8 * o.wosize ∧
      ∀ i (x : UInt8), bs[i]? = some x → byte c (a + off + i) = BitVec.ofNat 8 x.toNat := by
  simp only [byteSlice?, object, Option.bind_eq_bind, Option.bind_some] at slice
  cases o with
  | bytes b =>
    simp only at slice
    split at slice
    · cases slice
      obtain ⟨-, bytes, -⟩ := layout
      refine ⟨by simp; omega, by simp only [Obj.wosize]; omega, fun i x hx => ?_⟩
      have hi := (List.getElem?_eq_some_iff.mp hx).1
      simp only [List.length_take, List.length_drop] at hi
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop] at hx
      rw [show a + off + i = a + (off + i) by omega]
      exact bytes _ x hx
    · cases slice
  | partialBytes b =>
    simp only at slice
    split at slice
    · obtain ⟨-, bytes, -⟩ := layout
      have len := mapM_id_length _ _ slice
      refine ⟨by simp at len; omega, by simp only [Obj.wosize]; omega, fun i x hx => ?_⟩
      have cell := mapM_id_get _ _ slice i x hx
      have hi := (List.getElem?_eq_some_iff.mp cell).1
      simp only [List.length_take, List.length_drop] at hi
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop] at cell
      rw [show a + off + i = a + (off + i) by omega]
      exact bytes _ _ cell x rfl
    · cases slice
  | _ => simp at slice

/-- `caml_ml_output_bytes`' entry facts survive a jump into it. -/
theorem ObInput.jump {ra sp v str ofs len ch dom lr pc value : BitVec 64} {regs : GRegs} {c d : Config}
    (I : ObInput ra sp v str ofs len ch dom lr c) (p : WriteRegistersPost [] [] c pc value regs d) :
    ObInput ra sp v str ofs len ch dom lr d := by
  have keep := fun n (lo : 1 ≤ n) (hi : n ≤ 31) => p.toEffectPost.gpr_frame (by decide) n lo hi (by simp)
  have mem : d.σ.mem = c.σ.mem := by rw [p.memory]; rfl
  exact
    { good := p.good, image := p.image, minstret := p.minstret, tick := p.tick, aligned := I.aligned
      raReg := (keep 1 (by decide) (by decide)).trans I.raReg
      idle := p.toEffectPost.htifIdle I.idle
      saved := fun n hn => by
        have := I.saved n hn
        have b : 1 ≤ n ∧ n ≤ 31 := by simp at hn; omega
        change (gpr d n).isSome; rw [keep n b.1 b.2]; exact this
      stack := (keep 2 (by decide) (by decide)).trans I.stack
      valReg := (keep 10 (by decide) (by decide)).trans I.valReg
      strReg := (keep 11 (by decide) (by decide)).trans I.strReg
      ofsReg := (keep 12 (by decide) (by decide)).trans I.ofsReg
      lenReg := (keep 13 (by decide) (by decide)).trans I.lenReg
      geo := I.geo
      domWord := by rw [mem]; exact I.domWord
      rootsWord := by rw [mem]; exact I.rootsWord
      chanPtr := by rw [mem]; exact I.chanPtr
      lockNull := by rw [mem]; exact I.lockNull
      unlockNull := by rw [mem]; exact I.unlockNull
      flagsClear := by rw [mem]; exact I.flagsClear }

/-- The model facts survive a jump. -/
theorem ObModel.jump {ch dom str pc value : BitVec 64} {id p : Nat} {st : TCB.Os.Stream} {w : World} {chn : Chan}
    {bs : List UInt8} {regs : GRegs} {c d : Config} (M : ObModel ch dom str id st w chn bs p c)
    (q : WriteRegistersPost [] [] c pc value regs d) : ObModel ch dom str id st w chn bs p d := by
  have mem : d.σ.mem = c.σ.mem := by rw [q.memory]; rfl
  have b : ∀ x, byte d x = byte c x := fun x => by simp only [byte, mem]
  exact
    { M with
      repr := ChanAt.of_bytes M.repr fun x _ _ => b x
      output := by rw [← M.output]; unfold Vsa.Machine.output; rw [q.output]
      bytes := fun i x hx => (b _).trans (M.bytes i x hx)
      rt := OCaml.Vm.Gc.ConsoleRuntime.transfer (fun x _ _ => by rw [mem]) M.rt
      ready := M.ready.of_kept (GprsKept.of_pins q (by decide) (by decide) (by simp))
        (q.toEffectPost.htifIdle M.ready.htifIdle) }

/-- A console return from `caml_ml_output_bytes` is one from `caml_ml_output`'s
jump into it. -/
theorem ConsoleRet.jump {ra sp pc value : BitVec 64} {regs : GRegs} {c d e : Config}
    (p : WriteRegistersPost [] [] c pc value regs d) (r : ConsoleRet ra sp d e) : ConsoleRet ra sp c e :=
  { r with
    saved := fun n hn => (r.saved n hn).trans
      (p.toEffectPost.gpr_frame (by decide) n (by simp at hn; omega) (by simp at hn; omega) (by simp))
    gprs := (GprsKept.of_pins p (by decide) (by decide) (by simp)).trans r.gprs }

theorem intArg_some {x : Val} {i : Int} (h : intArg? x = some i) : ∃ n, x = .int n ∧ i = n.toInt := by
  cases x <;> simp [intArg?] at h; exact ⟨_, rfl, h.symm⟩

theorem byteSlice_ptr {h : Heap} {x : Val} {off n : Nat} {bs : List UInt8} (hs : byteSlice? h x off n = some bs) :
    ∃ l o, x = .ptr l 0 ∧ h.get? l = some o := by
  match x, hs with
  | .ptr l 0, hs =>
    cases e : h.get? l with
    | none => simp [byteSlice?, e] at hs
    | some o => exact ⟨l, o, rfl, e⟩
  | .ptr l (k + 1), hs => simp [byteSlice?] at hs
  | .int _, hs | .code _, hs | .atom _, hs | .raw _, hs => simp [byteSlice?] at hs

theorem toInt_toNat_nonneg (n : BitVec 63) (h : 0 ≤ n.toInt) : n.toInt.toNat = n.toNat := by
  have := BitVec.toInt_eq_toNat_cond n
  split at this <;> omega

/-- **`caml_ml_output` at a `C_CALL4` site**: the framed summary, for a
console output channel. -/
theorem output_framed {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain : Nat} {env ra : BitVec 64} {c : Config} {l a id ch : Nat} {chn : Chan}
    {D : InvocationData} {v : Val} {heap : Heap} {world : World}
    (setup : CcallSetupPost ra (s.accu :: s.stack.take 3) L P s pl cp sp high domain 0x800166cc env c)
    (arg : ChannelArg s c pl cp l a id ch chn) (inv : Invocation D c) (valid : NativeValid D)
    (rt : ConsoleWrite.ConsoleRuntime c) (ready : LibraryReady c)
    (consoleOf : chn.isOut = true → chn.fd ≠ -1 → OCaml.ConsoleChan s.world chn)
    (outside : PayloadChanOutside (consoleLog D.nativeSp ch) P s c pl cp sp id)
    (bindings : BindingsOutside (consoleLog D.nativeSp ch) P c)
    (stable : ConsoleStable L)
    (sem : primF1Impl "caml_ml_output" (s.accu :: s.stack.take 3) s.heap s.world = .ok v heap world) :
    FnSummary (BitVec.ofNat 64 0x800166cc) (fun x => x = c)
      (FramedPrimitivePost L.runtimeOk P s pl cp sp high "caml_ml_output" (s.accu :: s.stack.take 3) v 1#64
        heap world (consoleLog D.nativeSp ch) c ra) := by
  -- the model: three stack arguments, a slice of a placed string, `putBlock`
  obtain ⟨x1, x2, x3, rest, hst⟩ : ∃ x1 x2 x3 rest, s.stack = x1 :: x2 :: x3 :: rest := by
    match h : s.stack with
    | x1 :: x2 :: x3 :: rest => exact ⟨x1, x2, x3, rest, rfl⟩
    | [] | [_] | [_, _] => rw [h] at sem; simp [primF1Impl] at sem
  have args : s.accu :: s.stack.take 3 = [s.accu, x1, x2, x3] := by rw [hst]; rfl
  have sem0 := sem
  rw [args] at sem
  obtain ⟨id', -, oi, ni, bs, hc, -, ho, hn, opos, npos, slice, model, rfl, rfl⟩ := output_semantics sem
  have hid : id' = id := by
    rw [arg.accu] at hc; simp [chanOf?, arg.object] at hc; exact hc.symm
  subst id'
  obtain ⟨no, rfl, rfl⟩ := intArg_some ho
  obtain ⟨nl, rfl, rfl⟩ := intArg_some hn
  obtain ⟨ls, o, rfl, hobj⟩ := byteSlice_ptr slice
  have liveS : Live s.heap (roots P s) ls := Live.root (v := .ptr ls 0) (by simp [roots, hst]) rfl
  obtain ⟨sa, o', placedS, ho', layoutS⟩ := setup.input.data.heap.1 ls liveS
  rw [hobj] at ho'; cases ho'
  obtain ⟨blen, extent, sbytes⟩ := slice_bytes layoutS hobj slice
  simp only [toInt_toNat_nonneg _ opos, toInt_toNat_nonneg _ npos] at blen extent sbytes
  -- the machine
  have SG := setup.geometry.toArmGeometry.toStackGeometry
  have G := console_geometry_full setup.geometry arg valid
  have GL := G.lits
  have hl := SG.heapLow ls sa o placedS hobj
  have ha := SG.heapArena ls sa o placedS hobj
  have hc' := (SG.heapChannels ls sa o placedS hobj id chn ch arg.chan arg.record).1
  have hd := (SG.domainHeap ls sa o placedS hobj).1
  simp only [chanOffBuff, ioBufferSize, Layout.domainStateBytes, Layout.sym_bss_end, DlHeap.heapEnd] at hl ha hc' hd
  have hs : (BitVec.ofNat 64 D.nativeSp).toNat = D.nativeSp := by rw [BitVec.toNat_ofNat]; have := GL.high; omega
  have hv : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; have := GL.valHigh; omega
  have hstr : (BitVec.ofNat 64 sa).toNat = sa := by rw [BitVec.toNat_ofNat]; omega
  have E := flush_entry setup arg inv valid setup.calleeSaved
  have F := arg.repr.fields
  have off68 : (word c (a + 8) + 68#64).toNat = ch + 68 := by
    rw [ConsoleWrite.bv_add_toNat (by rw [arg.pointer]; have := GL.chanHigh; omega), arg.pointer]
  have I : ConsoleWrite.ObInput ra (BitVec.ofNat 64 D.nativeSp) (BitVec.ofNat 64 a) (BitVec.ofNat 64 sa)
      (tag64 no) (tag64 nl) (word c (a + 8)) (word c Layout.sym_Caml_state)
      (word c ((word c Layout.sym_Caml_state).toNat + 288)) c :=
    { E.toLeafInput with
      idle := E.idle, saved := E.saved, stack := E.stack, valReg := E.valReg
      strReg := setup.input.arguments.get (i := 1) (by rw [args]; rfl) (show valWord pl (.ptr ls 0) = some (BitVec.ofNat 64 (sa + 8 * 0))
        by simp [valWord, placedS])
      ofsReg := setup.input.arguments.get (i := 2) (v := .int no) (by rw [args]; rfl) rfl
      lenReg := setup.input.arguments.get (i := 3) (v := .int nl) (by rw [args]; rfl) rfl
      geo := by rw [hs, arg.pointer, hv]; exact G
      domWord := E.domWord, rootsWord := E.rootsWord, chanPtr := E.chanPtr
      lockNull := rt.lockNull, unlockNull := rt.unlockNull
      flagsClear := by rw [off68]; exact flags_word (by simpa only [chanOffFlags] using F.flags) }
  have b1 : ∀ {d : Config} {pc' value : BitVec 64} {regs : GRegs}, WriteRegistersPost [] [] c pc' value regs d →
      ∀ x, byte d x = byte c x := fun q x => by simp only [byte, q.memory]; rfl
  by_cases zero : bs = []
  · -- nothing to write: the channel and the world are kept
    subst zero
    rw [ConsoleWrite.putBlock_nil] at model
    cases model
    have hset : s.world.chans = s.world.chans.set id chn := by
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp arg.chan
      rw [← heq, List.set_getElem_self]
    refine ⟨fun c0 ⟨pc0, e0⟩ => ?_⟩
    subst c0
    let R : Nat → BitVec 64 := fun n => if n = 1 then ra else BitVec.ofNat 64 a
    obtain ⟨d1, run1, p1⟩ := (Flush.MlOutput.tail_fast c R ⟨I.good, I.image, I.minstret, I.raReg, I.aligned, I.tick⟩
      ⟨I.raReg, I.valReg, True.intro⟩).run c ⟨pc0, rfl⟩
    obtain ⟨e, run2, Dn⟩ := ob_empty (ObInput.jump I p1) p1.pc npos (by simpa using blen.symm)
      (ChanAt.of_bytes (by rw [arg.pointer]; exact arg.repr) fun x _ _ => b1 p1 x)
      (by rw [← setup.input.data.world.output]; unfold Vsa.Machine.output; rw [p1.output])
    have memory : ∀ x, OutL (consoleLog D.nativeSp ch) x → byte e x = byte c x := fun x hx => by
      rw [Dn.memory x (by rw [hs, arg.pointer]; exact hx), b1 p1]
    exact ⟨e, run1.trans run2, framed_of_ret setup inv valid
      (by simp only [Layout.sym_stack_top]; have := GL.high; omega)
      (ConsoleRet.jump p1 Dn.ret) memory outside bindings stable arg.chan arg.record hset rfl rfl
      (by rw [← arg.pointer]; exact Dn.repr) Dn.console sem0⟩
  -- something to write: an open console output channel
  obtain ⟨fd0, out⟩ := ConsoleWrite.putBlock_open arg.chan zero model
  obtain ⟨console, live, st, stream, streamOut⟩ := consoleOf out (by omega)
  have M : ObModel (word c (a + 8)) (word c Layout.sym_Caml_state) (BitVec.ofNat 64 sa) id st s.world chn bs
      no.toNat c :=
    { chan := arg.chan, repr := by rw [arg.pointer]; exact arg.repr, console := console, out := out
      stream := stream, live := live, streamOut := streamOut, output := setup.input.data.world.output
      source := ⟨by rw [hstr]; simp only [Layout.sym_bss_end]; omega,
        by rw [hstr, blen]; simp only [DlHeap.heapEnd]; omega,
        by rw [hstr, blen, arg.pointer]; omega⟩
      sourceRoots := by rw [hstr, blen]; omega
      bytes := fun i x hx => by rw [hstr]; exact sbytes i x hx
      rt := rt, ready := ready }
  refine ⟨fun c0 ⟨pc0, e0⟩ => ?_⟩
  subst c0
  -- the tail jump into `caml_ml_output_bytes`
  let R : Nat → BitVec 64 := fun n => if n = 1 then ra else BitVec.ofNat 64 a
  obtain ⟨d1, run1, p1⟩ := (Flush.MlOutput.tail_fast c R ⟨I.good, I.image, I.minstret, I.raReg, I.aligned, I.tick⟩
    ⟨I.raReg, I.valReg, True.intro⟩).run c ⟨pc0, rfl⟩
  obtain ⟨e, chnF, run2, Dn, chanF⟩ := ob_bytes (ObInput.jump I p1) p1.pc
    opos npos blen (M.jump p1) model
  obtain ⟨cF, hshape⟩ := ConsoleWrite.putBlock_shape arg.chan model
  have hcF : cF = chnF := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp arg.chan
    rw [hshape] at chanF; simpa [List.getElem?_set_self hlt] using chanF
  subst hcF
  have b1 := b1 p1
  have memory : ∀ x, OutL (consoleLog D.nativeSp ch) x → byte e x = byte c x := fun x hx => by
    rw [Dn.memory x (by rw [hs, arg.pointer]; exact hx), b1]
  exact ⟨e, run1.trans run2, framed_of_ret setup inv valid (by simp only [Layout.sym_stack_top]; have := GL.high; omega)
    (ConsoleRet.jump p1 Dn.ret) memory outside bindings stable arg.chan arg.record
    (by rw [hshape]) (by rw [hshape]) (by rw [hshape]; rfl) (by rw [← arg.pointer]; exact Dn.repr) Dn.console sem0⟩

end OCaml.Vm.Sim
