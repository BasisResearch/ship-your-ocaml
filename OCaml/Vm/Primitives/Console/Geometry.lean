import OCaml.Vm.Primitives.Console.OutputChar
import OCaml.Vm.Primitives.Console.Runtime
import Vsa.Sim.DlHeap

/-! The console-output layouts (`WriteLayout` … `MlFlushLayout`) from one
numeric geometry: a 16-aligned native sp with headroom above the allocator
arena, and the channel record, the `Caml_state` record and the channel's
custom block in the arena above `.bss`, apart from each other. Every static
the console path reads lies below `.bss`'s end, so it misses the native frames
and the arena records. -/
namespace OCaml.Vm.Primitives.ConsoleWrite
open OCaml.Bytecode Vsa.Machine Vsa.Sim
open FdWrite (errnoGlobal impurePtr enterHook leaveHook pendingSignals)

/-- The numeric geometry of a console-output call: native sp `sp`, channel
record `ch` with `len` buffered bytes, `Caml_state` record `dom`, channel
custom block `v`. -/
structure ConsoleGeometry (sp ch dom v len : Nat) : Prop where
  low : Vsa.Sim.DlHeap.heapEnd + 4096 ≤ sp
  high : sp ≤ Layout.sym_stack_top
  aligned : sp % 16 = 0
  chanLow : Layout.sym_bss_end ≤ ch
  chanHigh : ch + 72 + len ≤ Vsa.Sim.DlHeap.heapEnd
  chanAligned : ch % 8 = 0
  domLow : Layout.sym_bss_end ≤ dom
  domHigh : dom + Layout.domainStateBytes ≤ Vsa.Sim.DlHeap.heapEnd
  domAligned : dom % 8 = 0
  chanDom : ch + 72 + len ≤ dom ∨ dom + Layout.domainStateBytes ≤ ch
  valLow : Layout.sym_bss_end ≤ v
  valHigh : v + 16 ≤ Vsa.Sim.DlHeap.heapEnd
  valChan : v + 16 ≤ ch ∨ ch + 72 + len ≤ v
  valDom : v + 16 ≤ dom ∨ dom + Layout.domainStateBytes ≤ v

theorem bv_sub_toNat {s : BitVec 64} {m : Nat} (h : m ≤ s.toNat) : (s - BitVec.ofNat 64 m).toNat = s.toNat - m := by
  rw [BitVec.toNat_sub]; have := s.isLt; simp only [BitVec.toNat_ofNat]; omega

theorem bv_add_toNat {s : BitVec 64} {k : Nat} (h : s.toNat + k < 2 ^ 64) : (s + BitVec.ofNat 64 k).toNat = s.toNat + k := by
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

/-- The statics the console path reads, as literals (rewrite with these before
`omega`, which would otherwise unfold the `def`s). -/
structure ConsoleLits : Prop where
  fsReady : fsReady.toNat = 0x80064918
  impurePtr : impurePtr.toNat = 0x800648f8
  errno : errnoGlobal.toNat = 0x80064d48
  enterHook : enterHook.toNat = 0x80064870
  leaveHook : leaveHook.toNat = 0x80064868
  pending : pendingSignals.toNat = 0x80068690
  quiet : somethingToDo.toNat = 0x80064b30
  state : camlStateGlobal.toNat = 0x80064d08
  lock : channelLock.toNat = 0x80064b58
  unlock : channelUnlock.toNat = 0x80064b50
  impureData : (BitVec.ofNat 64 Layout.sym_impure_data).toNat = 0x80064668
  kind1 : (kindAddress 1#64).toNat = 0x80064db0
  kind2 : (kindAddress 2#64).toNat = 0x80064dc8
  textEnd : Image.textBase + Image.textSize ≤ 0x80062000
  rodataEnd : Image.rodataBase + Image.rodataSize ≤ 0x80062000
  tohost : Layout.sym_tohost = 0x80061fc0

theorem consoleLits : ConsoleLits := by
  constructor <;> first | rfl | decide

/-- The console path's address constants are the ELF's symbols (`Layout.lean`,
generated). -/
theorem console_symbols :
    impurePtr = BitVec.ofNat 64 Layout.sym_impure_ptr ∧ errnoGlobal = BitVec.ofNat 64 Layout.sym_errno ∧
    enterHook = BitVec.ofNat 64 Layout.sym_caml_enter_blocking_section_hook ∧
    leaveHook = BitVec.ofNat 64 Layout.sym_caml_leave_blocking_section_hook ∧
    pendingSignals = BitVec.ofNat 64 Layout.sym_caml_pending_signals ∧
    camlStateGlobal = BitVec.ofNat 64 Layout.sym_Caml_state ∧
    channelLock = BitVec.ofNat 64 Layout.sym_caml_channel_mutex_lock ∧
    channelUnlock = BitVec.ofNat 64 Layout.sym_caml_channel_mutex_unlock ∧
    somethingToDo = BitVec.ofNat 64 Layout.sym_caml_something_to_do := by
  decide

/-- The numeric geometry with its constants unfolded. -/
structure GeometryLits (sp ch dom v len : Nat) : Prop where
  low : 0x86800000 + 4096 ≤ sp
  high : sp ≤ 0x88000000
  aligned : sp % 16 = 0
  chanLow : 0x8007d138 ≤ ch
  chanHigh : ch + 72 + len ≤ 0x86800000
  chanAligned : ch % 8 = 0
  domLow : 0x8007d138 ≤ dom
  domHigh : dom + 928 ≤ 0x86800000
  domAligned : dom % 8 = 0
  chanDom : ch + 72 + len ≤ dom ∨ dom + 928 ≤ ch
  valLow : 0x8007d138 ≤ v
  valHigh : v + 16 ≤ 0x86800000
  valChan : v + 16 ≤ ch ∨ ch + 72 + len ≤ v
  valDom : v + 16 ≤ dom ∨ dom + 928 ≤ v

theorem ConsoleGeometry.lits {sp ch dom v len : Nat} (g : ConsoleGeometry sp ch dom v len) :
    GeometryLits sp ch dom v len := by
  have h1 : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have h2 : Layout.sym_stack_top = 0x88000000 := rfl
  have h3 : Layout.sym_bss_end = 0x8007d138 := rfl
  have h5 : Layout.domainStateBytes = 928 := rfl
  have := g.low; have := g.high; have := g.chanLow; have := g.chanHigh; have := g.domLow; have := g.domHigh
  have := g.chanDom; have := g.valLow; have := g.valHigh; have := g.valChan; have := g.valDom
  rw [h1, h2, h3, h5] at *
  exact ⟨by omega, by omega, g.aligned, by omega, by omega, g.chanAligned, by omega, by omega, g.domAligned,
    by omega, by omega, by omega, by omega, by omega⟩

/-- Image bounds in literal form. -/
structure ImageLits : Prop where
  text : Image.textBase + Image.textSize ≤ 0x80062000
  rodata : Image.rodataBase + Image.rodataSize ≤ 0x80062000
  tohost : Layout.sym_tohost = 0x80061fc0

theorem imageLits : ImageLits := ⟨consoleLits.textEnd, consoleLits.rodataEnd, consoleLits.tohost⟩

theorem ConsoleGeometry.write {sp ch dom v len : Nat} (g : ConsoleGeometry sp ch dom v len)
    {s fd chB : BitVec 64} {off : Nat} (hc : chB.toNat = ch) (hs : s.toNat + off = sp) (hoff : off ≤ 1900)
    (al : off % 16 = 0) (hfd : fd = 1#64 ∨ fd = 2#64) : WriteLayout s fd (chB + 72#64) len := by
  have G := g.lits
  have C := consoleLits
  have hb : (chB + 72#64).toNat = ch + 72 := by
    rw [bv_add_toNat (by have := G.chanHigh; omega), hc]
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned; have l4 := G.chanHigh; have l5 := G.chanLow
  have T := C.textEnd; have R := C.rodataEnd
  rcases hfd with rfl | rfl <;>
  · refine ⟨by omega, by omega, by rw [C.tohost]; omega, by omega, by omega, by omega,
      by rw [C.fsReady]; omega, by first | rw [C.kind1]; omega | rw [C.kind2]; omega, ?_⟩
    rw [hb]; omega

/-- A word of a native frame `off` bytes below a base `b`. -/
theorem frame_window {s : BitVec 64} {b off k : Nat} (hs : s.toNat = b) (hlow : 0x80070000 + off ≤ b)
    (hhigh : b ≤ 0x88000000) (hk : k + 8 ≤ off) (al : (b - off + k) % 8 = 0) :
    WriteWindow (s - BitVec.ofNat 64 off + BitVec.ofNat 64 k) 8 := by
  have e : (s - BitVec.ofNat 64 off + BitVec.ofNat 64 k).toNat = b - off + k := by
    rw [bv_add_toNat (by rw [bv_sub_toNat (by omega)]; omega), bv_sub_toNat (by omega), hs]
  exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, consoleLits.tohost]; omega, by rw [e]; omega⟩

theorem frame_window0 {s : BitVec 64} {b off : Nat} (hs : s.toNat = b) (hlow : 0x80070000 + off ≤ b)
    (hhigh : b ≤ 0x88000000) (hk : 8 ≤ off) (al : (b - off) % 8 = 0) :
    WriteWindow (s - BitVec.ofNat 64 off) 8 := by
  have e : (s - BitVec.ofNat 64 off).toNat = b - off := by rw [bv_sub_toNat (by omega), hs]
  exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, consoleLits.tohost]; omega, by rw [e]; omega⟩

theorem ConsoleGeometry.writeCall {sp ch dom v len : Nat} (g : ConsoleGeometry sp ch dom v len)
    {s fd chB : BitVec 64} {off : Nat} (hc : chB.toNat = ch) (hs : s.toNat + off = sp) (hoff : off ≤ 1800)
    (al : off % 16 = 0) (hfd : fd = 1#64 ∨ fd = 2#64) : WriteCallLayout s fd (chB + 72#64) len := by
  have G := g.lits
  have C := consoleLits
  have hb : (chB + 72#64).toNat = ch + 72 := by
    rw [bv_add_toNat (by have := G.chanHigh; omega), hc]
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned; have l4 := G.chanHigh; have l5 := G.chanLow
  have T := C.textEnd; have R := C.rodataEnd
  have e16 : (s - 16#64).toNat + (off + 16) = sp := by rw [bv_sub_toNat (by omega)]; omega
  rcases hfd with rfl | rfl <;>
  · refine ⟨g.write hc e16 (by omega) (by omega) (by simp),
      frame_window0 rfl (by omega) (by omega) (by decide) (by omega),
      frame_window rfl (by omega) (by omega) (by decide) (by omega),
      by omega, by omega, by rw [C.fsReady]; omega, by first | rw [C.kind1]; omega | rw [C.kind2]; omega,
      by rw [hb]; omega, by rw [C.fsReady, C.errno]; omega,
      by first | rw [C.kind1, C.errno]; omega | rw [C.kind2, C.errno]; omega,
      by rw [hb, C.errno]; omega, by rw [C.errno]; omega⟩

/-- `_impure_ptr`'s reentrancy structure, whose first word is its `errno`. -/
abbrev impureData : BitVec 64 := BitVec.ofNat 64 Layout.sym_impure_data

theorem ConsoleGeometry.writeFd {sp ch dom v len : Nat} (g : ConsoleGeometry sp ch dom v len)
    {s fd chB : BitVec 64} {off : Nat} (hc : chB.toNat = ch) (hs : s.toNat + off = sp) (hoff : off ≤ 1700)
    (al : off % 16 = 0) (hfd : fd = 1#64 ∨ fd = 2#64) : WriteFdLayout s fd (chB + 72#64) impureData len := by
  have G := g.lits
  have C := consoleLits
  have hb : (chB + 72#64).toNat = ch + 72 := by
    rw [bv_add_toNat (by have := G.chanHigh; omega), hc]
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned; have l4 := G.chanHigh; have l5 := G.chanLow
  have T := C.textEnd; have R := C.rodataEnd
  have e80 : (s - 80#64).toNat + (off + 80) = sp := by rw [bv_sub_toNat (by omega)]; omega
  have slots : ∀ k ∈ [8, 16, 24, 32, 40, 48, 56, 64, 72], WriteWindow (s - 80#64 + BitVec.ofNat 64 k) 8 := by
    intro k hk
    have hk' : k + 8 ≤ 80 ∧ k % 8 = 0 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; omega
    exact frame_window rfl (by omega) (by omega) hk'.1 (by omega)
  rcases hfd with rfl | rfl <;>
  · refine ⟨g.writeCall hc e80 (by omega) (by omega) (by simp), slots, by omega, by omega, by omega, by omega,
      by rw [C.fsReady]; omega, by first | rw [C.kind1]; omega | rw [C.kind2]; omega,
      by rw [hb]; omega, by rw [C.errno]; omega, ?_, by rw [C.pending]; omega,
      ⟨by rw [C.impureData]; omega, by rw [C.impureData]; omega, by rw [C.impureData, C.tohost]; omega,
        by rw [C.impureData]⟩,
      by rw [C.impureData]; omega, by rw [C.impureData]; omega, by rw [C.impureData, C.errno]; omega⟩
    intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · rw [C.enterHook]; omega
    · rw [C.leaveHook]; omega
    · rw [C.impurePtr]; omega
    · rw [C.impureData]; omega

/-- A field of a record in the arena above `.bss`. -/
theorem arena_read {chB : BitVec 64} {ch k n : Nat} (hc : chB.toNat = ch) (low : 0x8007d138 ≤ ch)
    (high : ch + k + n ≤ 0x86800000) : ReadWindow (chB + BitVec.ofNat 64 k) n := by
  have e : (chB + BitVec.ofNat 64 k).toNat = ch + k := by rw [bv_add_toNat (by omega), hc]
  exact ⟨by rw [e]; omega, by rw [e]; omega, Or.inr (by rw [e, consoleLits.tohost]; omega)⟩

theorem arena_write {chB : BitVec 64} {ch k : Nat} (hc : chB.toNat = ch) (low : 0x8007d138 ≤ ch)
    (high : ch + k + 8 ≤ 0x86800000) (al : (ch + k) % 8 = 0) : WriteWindow (chB + BitVec.ofNat 64 k) 8 := by
  have e : (chB + BitVec.ofNat 64 k).toNat = ch + k := by rw [bv_add_toNat (by omega), hc]
  exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, consoleLits.tohost]; omega, by rw [e]; omega⟩

theorem ConsoleGeometry.flush {sp ch dom v len : Nat} (g : ConsoleGeometry sp ch dom v len)
    {s fd chB : BitVec 64} {off : Nat} (hc : chB.toNat = ch) (hs : s.toNat + off = sp) (hoff : off ≤ 1600)
    (al : off % 16 = 0) (hfd : fd = 1#64 ∨ fd = 2#64) : FlushLayout s chB fd impureData len := by
  have G := g.lits
  have C := consoleLits
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned; have l4 := G.chanHigh; have l5 := G.chanLow
  have l6 := G.chanAligned
  have T := C.textEnd; have R := C.rodataEnd
  have e80 : (s - 80#64).toNat + (off + 80) = sp := by rw [bv_sub_toNat (by omega)]; omega
  have slots : ∀ k ∈ [24, 32, 40, 48, 56, 64, 72], WriteWindow (s - 80#64 + BitVec.ofNat 64 k) 8 := by
    intro k hk
    have hk' : k + 8 ≤ 80 ∧ k % 8 = 0 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; omega
    exact frame_window rfl (by omega) (by omega) hk'.1 (by omega)
  have fdW : ReadWindow chB 4 := by
    have := arena_read (k := 0) (n := 4) hc (by omega) (by omega)
    simpa using this
  rcases hfd with rfl | rfl <;>
  · refine ⟨g.writeFd hc e80 (by omega) (by omega) (by simp), slots, by omega, by omega, by omega, by omega,
      ?_, by rw [C.pending]; omega, by rw [hc]; omega, by rw [hc]; omega, by rw [hc]; omega,
      by rw [hc, C.errno]; omega, by rw [hc, C.impureData]; omega, fdW,
      arena_read hc (by omega) (by omega), arena_write hc (by omega) (by omega) (by omega),
      arena_write hc (by omega) (by omega) (by omega), by rw [hc]; omega, by rw [hc]; omega⟩
    intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [C.fsReady]; omega
    · first | rw [C.kind1]; omega | rw [C.kind2]; omega
    · rw [C.enterHook]; omega
    · rw [C.leaveHook]; omega
    · rw [C.impurePtr]; omega
    · rw [C.impureData]; omega
    · rw [C.errno]; omega
    · rw [C.quiet]; omega

theorem ConsoleGeometry.mlFlush {sp ch dom v len : Nat} (g : ConsoleGeometry sp ch dom v len)
    {s vB chB domB fd : BitVec 64} (hc : chB.toNat = ch) (hv : vB.toNat = v) (hd : domB.toNat = dom)
    (hs : s.toNat = sp) (hfd : fd = 1#64 ∨ fd = 2#64) : MlFlushLayout s vB chB fd impureData domB len := by
  have G := g.lits
  have C := consoleLits
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned; have l4 := G.chanHigh; have l5 := G.chanLow
  have l7 := G.domLow; have l8 := G.domHigh; have l9 := G.domAligned; have l10 := G.chanDom
  have l11 := G.valLow; have l12 := G.valHigh; have l13 := G.valChan; have l14 := G.valDom
  have T := C.textEnd; have R := C.rodataEnd
  have r288 : (domB + 288#64).toNat = dom + 288 := by rw [bv_add_toNat (by omega), hd]
  have v8 : (vB + 8#64).toNat = v + 8 := by rw [bv_add_toNat (by omega), hv]
  have slots : ∀ k ∈ [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104],
      WriteWindow (s - 112#64 + BitVec.ofNat 64 k) 8 := by
    intro k hk
    have hk' : k + 8 ≤ 112 ∧ k % 8 = 0 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; omega
    exact frame_window hs (by omega) (by omega) hk'.1 (by omega)
  have word : ∀ a, 0x80062000 ≤ a → a + 8 ≤ 0x8007d138 → (a + 8 ≤ 0x80064d48 ∨ 0x80064d48 + 4 ≤ a) →
      (a + 8 ≤ 0x80064668 ∨ 0x80064668 + 4 ≤ a) → WordApart s chB impureData domB a :=
    fun a lo hi e r => ⟨by omega, by rw [C.errno]; exact e, by rw [C.impureData]; exact r, by rw [hc]; omega,
      by rw [hd]; omega⟩
  have reads : ∀ x, FlushReads chB fd len x → (x < s.toNat - 112 ∨ s.toNat ≤ x) ∧
      (x < (domB + 288#64).toNat ∨ (domB + 288#64).toNat + 8 ≤ x) := by
    intro x hx
    rw [r288, hs]
    rcases hx with ⟨h1, h2⟩ | ⟨a, ha, h1, h2⟩ | ⟨h1, h2⟩
    · rw [hc] at h1 h2; omega
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases hfd with rfl | rfl <;>
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | (rw [C.fsReady] at h1 h2; omega) | (rw [C.kind1] at h1 h2; omega) | (rw [C.kind2] at h1 h2; omega)
        | (rw [C.enterHook] at h1 h2; omega) | (rw [C.leaveHook] at h1 h2; omega)
        | (rw [C.impurePtr] at h1 h2; omega) | (rw [C.quiet] at h1 h2; omega)
    · rw [C.pending] at h1 h2; omega
  refine ⟨slots, by omega, by omega, by omega, by omega, arena_write hd (by omega) (by omega) (by omega),
    by omega, by omega, by omega, ⟨by omega, by rw [C.errno]; omega, by rw [C.impureData]; omega, by rw [hc]; omega⟩,
    ?_, arena_read hv (by omega) (by omega), by rw [C.errno]; omega,
    by rw [C.impureData]; omega, reads⟩
  intro a ha
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · rw [C.state]; exact word _ (by omega) (by omega) (by omega) (by omega)
  · rw [C.lock]; exact word _ (by omega) (by omega) (by omega) (by omega)
  · rw [C.unlock]; exact word _ (by omega) (by omega) (by omega) (by omega)
  · rw [v8]
    exact ⟨by omega, by rw [C.errno]; omega, by rw [C.impureData]; omega, by rw [hc]; omega, by rw [hd]; omega⟩

/-- `caml_ml_flush`'s prologue/epilogue frame, open or closed channel. -/
theorem ConsoleGeometry.mlFlushFrame {sp ch dom v len : Nat} (g : ConsoleGeometry sp ch dom v len)
    {s vB chB domB : BitVec 64} (hc : chB.toNat = ch) (hv : vB.toNat = v) (hd : domB.toNat = dom)
    (hs : s.toNat = sp) : MlFlushFrame s vB chB domB := by
  have G := g.lits
  have C := consoleLits
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned; have l4 := G.chanHigh; have l5 := G.chanLow
  have l7 := G.domLow; have l8 := G.domHigh; have l9 := G.domAligned; have l10 := G.chanDom
  have l11 := G.valLow; have l12 := G.valHigh; have l13 := G.valChan; have l14 := G.valDom
  have T := C.textEnd; have R := C.rodataEnd
  have v8 : (vB + 8#64).toNat = v + 8 := by rw [bv_add_toNat (by omega), hv]
  have slots : ∀ k ∈ [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104],
      WriteWindow (s - 112#64 + BitVec.ofNat 64 k) 8 := by
    intro k hk
    have hk' : k + 8 ≤ 112 ∧ k % 8 = 0 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; omega
    exact frame_window hs (by omega) (by omega) hk'.1 (by omega)
  have fdW : ReadWindow chB 4 := by
    have := arena_read (k := 0) (n := 4) hc (by omega) (by omega)
    simpa using this
  exact ⟨slots, by omega, by omega, by omega, by omega, arena_write hd (by omega) (by omega) (by omega),
    by omega, by omega, by omega, by omega, ⟨by rw [C.state]; omega, by rw [C.state]; omega⟩,
    ⟨by rw [v8]; omega, by rw [v8]; omega⟩, arena_read hv (by omega) (by omega), fdW, ⟨by omega, by omega⟩⟩

/-- A geometry for a longer record holds for a shorter one. -/
theorem ConsoleGeometry.mono {sp ch dom v len len' : Nat} (g : ConsoleGeometry sp ch dom v len) (le : len' ≤ len) :
    ConsoleGeometry sp ch dom v len' :=
  { g with
    chanHigh := by have := g.chanHigh; omega
    chanDom := by have := g.chanDom; omega
    valChan := by have := g.valChan; omega }

/-- `caml_ml_output_char`'s layout, from the geometry of the channel's whole
record (`chanOffBuff + ioBufferSize`). -/
theorem ConsoleGeometry.ocLayout {sp ch dom v len : Nat} (g : ConsoleGeometry sp ch dom v 65536)
    {s vB chB domB fd : BitVec 64} (hc : chB.toNat = ch) (hv : vB.toNat = v) (hd : domB.toNat = dom)
    (hs : s.toNat = sp) (hfd : fd = 1#64 ∨ fd = 2#64) (le : len ≤ 65536) :
    OcLayout s vB chB fd impureData domB len := by
  have G := g.lits
  have C := consoleLits
  have l1 := G.low; have l2 := G.high; have l3 := G.aligned; have l4 := G.chanHigh; have l5 := G.chanLow
  have l6 := G.chanAligned; have l7 := G.domLow; have l10 := G.chanDom
  have T := C.textEnd; have R := C.rodataEnd
  exact ⟨(g.mono le).mlFlush hc hv hd hs hfd,
    frame_window0 hs (by omega) (by omega) (by decide) (by omega),
    arena_read hc (by omega) (by omega), arena_write hc (by omega) (by omega) (by omega),
    arena_read hc (by omega) (by omega),
    ⟨by rw [hc]; omega, by rw [hc]; omega, by rw [hc, C.tohost]; omega⟩,
    by rw [hc]; omega, by rw [hc]; omega, by rw [hc, hs]; omega, by rw [hc, C.errno]; omega,
    by rw [hc, C.impureData]; omega, by rw [hc, hd]; omega, by rw [hc]; simp only [Layout.sym_bss_end]; omega⟩

end OCaml.Vm.Primitives.ConsoleWrite
