import OCaml.Vm.Primitives.Format.ParseFormat
import OCaml.Vm.Primitives.Format.StringLengthCall
import OCaml.Vm.Primitives.LibraryStrlenCall
import OCaml.Vm.Primitives.Memmove
import OCaml.Vm.Primitives.LibraryEffects
import OCaml.Vm.Boot.Startup.NativeFrame
import OCaml.Vm.Boot.Startup.LibraryText

/-!
# `parse_format` as a call summary

`parse_format(fmt, suffix, buf)` (ints.c) copies the OCaml format string
`fmt` (length `n`) into the 32-byte buffer `buf`, then the C suffix (here
`ARCH_INTNAT_PRINTF_FORMAT` = `"l"`) before the conversion character, then
the conversion and a terminator, and returns the conversion character. The
path is the generated block family of `--ocaml-format` with three calls
spliced in: `caml_string_length` (`string_length_call`), `strlen` on the
suffix (`strlen_call`) and two `memmove`s (`memmove_call`).

The composition is split by phase to stay within the elaboration budget:
`measure` runs the prologue and both length calls.
-/

namespace OCaml.Vm.Primitives.Format.ParseFormat
set_option autoImplicit false
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast OCaml.Vm.Primitives
open OCaml.Vm.Boot.Startup

/-- A present register reads as its own value. -/
theorem gpr_getD {c : Config} {k : Nat} (h : (gprGet c.σ k).isSome) :
    gprGet c.σ k = some ((gprGet c.σ k).getD 0) := by
  cases e : gprGet c.σ k with
  | none => rw [e] at h; cases h
  | some v => rfl

/-- The registers at the entry, as the blocks' symbolic inputs. -/
def entryRegs (c : Config) : Nat → BitVec 64 := fun k => (gprGet c.σ k).getD 0

/-- parse_format's frame slot `off` (below `sp - 48`), normalized once. -/
theorem frame_slot {sp : BitVec 64} (frame : NativeFrame sp 48) (off : Nat) (bound : off ≤ 48) :
    sp - 48#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (nativeFrameBase sp 48 + off) := by
  rw [BitVec.sub_eq_add_neg]
  exact frame.address off bound

theorem frame_base {sp : BitVec 64} (frame : NativeFrame sp 48) :
    sp - 48#64 = BitVec.ofNat 64 (nativeFrameBase sp 48) := by
  have := frame_slot frame 0 (by decide)
  rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, Nat.add_zero] at this

theorem frame_word {sp : BitVec 64} (frame : NativeFrame sp 48) (off : Nat) (bound : off + 8 ≤ 48)
    (aligned : off % 8 = 0) : WriteWindow (sp - 48#64 + BitVec.ofNat 64 off) 8 := by
  rw [frame_slot frame off (by omega)]
  exact frame.word bound aligned

/-- The prologue's six saves lie in the frame. -/
theorem proLog_inside {R : Nat → BitVec 64} {loads : List (List (BitVec 8))} {sp : BitVec 64}
    (stack : R 2 = sp) (frame : NativeFrame sp 48) :
    LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (proLog R loads) := by
  have slot (off : Nat) (bound : off + 8 ≤ 48) :
      (sp - 48#64 + BitVec.ofNat 64 off).toNat = nativeFrameBase sp 48 + off := by
    rw [frame_slot frame off (by omega)]; exact frame.slot_nat (by omega)
  have base : (sp - 48#64).toNat = nativeFrameBase sp 48 := by
    rw [frame_base frame]; simpa using frame.slot_nat (off := 0) (by decide)
  have top : nativeFrameBase sp 48 + 48 = sp.toNat := by
    have := frame.lower; unfold nativeFrameBase; simp only [Vsa.Sim.DlHeap.heapEnd] at this; omega
  simp only [proLog, stack, LogInW, InsideW]
  rw [slot 40 (by decide), slot 32 (by decide), slot 16 (by decide), slot 8 (by decide), base,
    slot 24 (by decide)]
  refine ⟨Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩,
    Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega

/-- Every listed GPR holds its own value, at a library-ready state. -/
theorem holds_entry {live : Nat → Prop} {c : Config} (good : VsaOk live c) :
    ∀ keys : List Nat, (∀ k ∈ keys, 1 ≤ k ∧ k ≤ 31) →
      GHolds c.σ (keys.map fun k => (k, entryRegs c k))
  | [], _ => trivial
  | k :: keys, hk =>
    ⟨gpr_getD (good.gpr k (hk k (by simp)).1 (hk k (by simp)).2),
      holds_entry good keys fun j hj => hk j (List.mem_cons_of_mem _ hj)⟩

/-- parse_format's entry: arguments, a 48-byte native frame, a placed OCaml
format string apart from it, and library readiness (`VsaOk`, the global
pointer). -/
structure MeasureInput (live : Nat → Prop) (ra sp : BitVec 64) (f buf n : Nat) (c : Config) : Prop
    extends LeafInput ra c where
  libraryGood : VsaOk live c
  globalPointer : ROHolds (vsaModel live) c roR []
  stack : gpr c 2 = some sp
  fmt : gpr c 10 = some (BitVec.ofNat 64 f)
  suffix : gpr c 11 = some 0x80055088#64
  buffer : gpr c 12 = some (BitVec.ofNat 64 buf)
  frame : NativeFrame sp 48
  geometry : StringGeometry f n
  shape : StringShape c f n
  /-- the string object, header included, misses the frame -/
  apart : f + 8 * ((n + 8) / 8) ≤ nativeFrameBase sp 48 ∨ sp.toNat + 8 ≤ f

/-- The registers `measure_length` may change. -/
def lengthWritten : List Nat := [1, 2, 8, 10, 15, 18, 20]

/-- After the prologue and `caml_string_length`: back at `0x80010428` with
the length in `a0`, the frame saves in memory and library readiness kept. -/
structure LengthDone (live : Nat → Prop) (sp : BitVec 64) (f buf n : Nat) (before after : Config) : Prop
    extends LeafInput pro_call.link after where
  libraryGood : VsaOk live after
  globalPointer : ROHolds (vsaModel live) after roR []
  pc : OCaml.Vm.pcOf after = some pro_call.link
  memory : after.σ.mem = writeLog before.σ.mem (proLog (entryRegs before) [])
  output : after.σ.sailOutput = before.σ.sailOutput
  length : gpr after 10 = some (BitVec.ofNat 64 n)
  stack : gpr after 2 = some (sp - 48#64)
  buffer : gpr after 8 = some (BitVec.ofNat 64 buf)
  suffix : gpr after 18 = some 0x80055088#64
  fmt : gpr after 20 = some (BitVec.ofNat 64 f)
  kept : ∀ k, 1 ≤ k → k ≤ 31 → k ∉ lengthWritten → gpr after k = gpr before k

theorem entry_value {c : Config} {k : Nat} {v : BitVec 64} (h : gpr c k = some v) : entryRegs c k = v := by
  simp only [entryRegs]; change (gpr c k).getD 0 = v; rw [h]; rfl

/-- **The prologue and `caml_string_length`.** -/
theorem measure_length {live : Nat → Prop} {ra sp : BitVec 64} {f buf n : Nat} (c : Config)
    (h : MeasureInput live ra sp f buf n c) :
    FnSummary 0x800103fc#64 (fun d => d = c) (LengthDone live sp f buf n c) := by
  let R := entryRegs c
  have hR1 : R 1 = ra := entry_value h.raReg
  have hR2 : R 2 = sp := entry_value h.stack
  have hR10 : R 10 = BitVec.ofNat 64 f := entry_value h.fmt
  have hR11 : R 11 = 0x80055088#64 := entry_value h.suffix
  have hR12 : R 12 = BitVec.ofNat 64 buf := entry_value h.buffer
  have regs : GHolds c.σ (pro_input R) :=
    holds_entry h.libraryGood [1, 2, 8, 9, 10, 11, 12, 18, 19, 20] (by decide)
  have leaf : LeafInput (R 1) c := by rw [hR1]; exact h.toLeafInput
  have w4 : WriteWindow (R 2 - 48#64) 8 := by
    rw [hR2, frame_base h.frame]; simpa using h.frame.word (off := 0) (by decide) (by decide)
  have S := pro_fast c R leaf regs (by rw [hR2]; exact frame_word h.frame 40 (by decide) (by decide))
    (by rw [hR2]; exact frame_word h.frame 32 (by decide) (by decide))
    (by rw [hR2]; exact frame_word h.frame 16 (by decide) (by decide))
    (by rw [hR2]; exact frame_word h.frame 8 (by decide) (by decide)) w4
    (by rw [hR2]; exact frame_word h.frame 24 (by decide) (by decide))
    (h.frame.image_outside (proLog_inside hR2 h.frame))
  apply summary_bind S (fun _ p => p.pc)
  intro e p
  have args : GHolds e.σ [(2, R 2 - 48#64), (8, R 12), (10, R 10), (18, R 11), (20, R 10)] :=
    holds_project p.regs (by simp [pro_regs, lookupG])
  have J := call_registers_summary pro_call_shape pro_call_decode e (pro_call_pins p.image) p.good p.image
    p.tick p.minstret _ args (by change KeysOK [2, 8, 10, 18, 20]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  apply summary_bind J (fun _ q => q.pc)
  intro entered q
  have memE : entered.σ.mem = writeLog c.σ.mem (proLog R []) := q.memory.trans p.memory
  have lower := h.geometry.lower
  have out (x w : Nat) (lo : f - 8 ≤ x) (hi : x + w ≤ f + 8 * ((n + 8) / 8)) :
      OutLRange (proLog R []) x w := by
    apply OCaml.Vm.Sim.outLRange_of_windows (proLog_inside hR2 h.frame)
    refine ⟨?_, trivial⟩
    rcases h.apart with below | above
    · exact Or.inl (by dsimp only; omega)
    · exact Or.inr (by dsimp only; omega)
  have header : word entered (f - 8) = word c (f - 8) :=
    Reloc.bytesT_congr (copied_of_writeLog memE (out _ 8 (Nat.le_refl _) (by omega)))
  have padding : byte entered (f + 8 * ((n + 8) / 8) - 1) = byte c (f + 8 * ((n + 8) / 8) - 1) :=
    Reloc.bytesT_congr (copied_of_writeLog memE (out _ 1 (by omega) (by omega)))
  have shapeE : StringShape entered f n :=
    ⟨by rw [header]; exact h.shape.headerSize, by rw [padding]; exact h.shape.padding⟩
  have leafE : LeafInput pro_call.link entered :=
    ⟨q.good, q.image, q.minstret, gholds_lookup (n := 1) _ q.regs rfl, by decide, q.tick⟩
  have argument : gpr entered 10 = some (BitVec.ofNat 64 f) := by
    rw [← hR10]; exact gholds_lookup (n := 10) _ q.regs rfl
  have L := StringLength.string_length_call entered pro_call.link leafE argument h.geometry shapeE
  apply L.weaken (fun _ eq => eq)
  intro after r
  have goodE : VsaOk live e := p.vsaOk h.libraryGood (by decide) (by simp [pro_regs, keysG])
  have goodQ : VsaOk live entered := q.vsaOk_of_present goodE (by decide) (by simp [keysG])
    (fun a ha => by rw [q.memory]; exact goodE.live a ha)
  have goodR : VsaOk live after := r.vsaOk goodQ (by decide) (by simp [StringLength.lengthWrites, keysG])
  have gpE := p.toEffectPost.readOnly_log (live := live) (text := []) (by decide) (by decide)
    h.globalPointer (fun _ hp => nomatch hp)
  have gpQ := (show WritePost [1] [] e pro_call.target (R 10) entered from q.toEffectPost).readOnly_log
    (live := live) (text := []) (by decide) (by decide) gpE (fun _ hp => nomatch hp)
  have gpR := r.toEffectPost.readOnly_log (live := live) (text := []) (by decide) (by decide)
    gpQ (fun _ hp => nomatch hp)
  have frameR (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ StringLength.lengthWrites) :
      gpr after k = gpr entered k := r.toEffectPost.gpr_frame (by decide) k lo hi out
  have frameQ (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1]) : gpr entered k = gpr e k :=
    q.toEffectPost.gpr_frame (by decide) k lo hi out
  have frameP (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [2, 8, 18, 20]) : gpr e k = gpr c k :=
    p.toEffectPost.gpr_frame (by decide) k lo hi out
  have atE (k : Nat) {v : BitVec 64} (hv : lookupG k ((1, pro_call.link) ::
      [(2, R 2 - 48#64), (8, R 12), (10, R 10), (18, R 11), (20, R 10)]) = some v) : gpr entered k = some v :=
    gholds_lookup _ q.regs hv
  refine ⟨⟨r.good, r.image, r.minstret, gholds_lookup (n := 1) _ r.regs rfl, by decide, r.tick⟩,
    goodR, gpR, r.pc, ?_, ?_, r.result, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r.memory]; exact memE
  · exact r.output.trans (q.output.trans p.output)
  · rw [frameR 2 (by decide) (by decide) (by decide), atE 2 rfl, hR2]
  · rw [frameR 8 (by decide) (by decide) (by decide), atE 8 rfl, hR12]
  · rw [frameR 18 (by decide) (by decide) (by decide), atE 18 rfl, hR11]
  · rw [frameR 20 (by decide) (by decide) (by decide), atE 20 rfl, hR10]
  · intro k lo hi out
    simp only [lengthWritten, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    rw [frameR k lo hi (by simp [StringLength.lengthWrites]; omega),
      frameQ k lo hi (by simp; omega), frameP k lo hi (by simp; omega)]

/-- The global pointer survives any run that keeps `gp`. -/
theorem globalPointer_of_gpr {live : Nat → Prop} {before after : Config}
    (keep : gpr after 3 = gpr before 3) (h : ROHolds (vsaModel live) before roR []) :
    ROHolds (vsaModel live) after roR [] := by
  refine ⟨fun q hq => ?_, fun _ hq => nomatch hq⟩
  have old := h.1 q hq
  obtain rfl := List.mem_singleton.1 hq
  change vsaReg after 3 = _
  change vsaReg before 3 = _ at old
  simp only [vsaReg] at old ⊢
  change (gpr after 3).getD 0 = _
  change (gpr before 3).getD 0 = _ at old
  rw [keep]; exact old

/-- The C suffix `ARCH_INTNAT_PRINTF_FORMAT` = `"l"`, in `.rodata`. -/
def suffixAddr : Nat := 0x80055088

theorem suffix_bytes {c : Config} (image : ExecutableImage c) :
    imgM c.σ.mem suffixAddr = 0x6c#8 ∧ imgM c.σ.mem (suffixAddr + 1) = 0#8 := by
  have b0 := image.rodata 7944 (by decide)
  have b1 := image.rodata 7945 (by decide)
  refine ⟨?_, ?_⟩
  · change (c.σ.mem[suffixAddr]?).getD 0 = _
    rw [show suffixAddr = Image.rodataBase + 7944 from rfl, b0]; decide
  · change (c.σ.mem[suffixAddr + 1]?).getD 0 = _
    rw [show suffixAddr + 1 = Image.rodataBase + 7945 from rfl, b1]; decide

/-- The registers `measure` may change. -/
def measureWritten : List Nat := [1, 2, 8, 10, 11, 12, 13, 14, 15, 18, 19, 20]

/-- After both length calls: at the fit check (`0x80010434`) with `s3` the
format's length and `a0` the suffix's. -/
structure Measured (live : Nat → Prop) (sp : BitVec 64) (f buf n : Nat) (before after : Config) : Prop
    extends LeafInput suffix_call.link after where
  libraryGood : VsaOk live after
  globalPointer : ROHolds (vsaModel live) after roR []
  pc : OCaml.Vm.pcOf after = some suffix_call.link
  memory : Vsa.Densify.MemEqv after.σ.mem (writeLog before.σ.mem (proLog (entryRegs before) []))
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  suffixLength : gpr after 10 = some 1#64
  length : gpr after 19 = some (BitVec.ofNat 64 n)
  stack : gpr after 2 = some (sp - 48#64)
  buffer : gpr after 8 = some (BitVec.ofNat 64 buf)
  suffix : gpr after 18 = some 0x80055088#64
  fmt : gpr after 20 = some (BitVec.ofNat 64 f)
  kept : ∀ k, 1 ≤ k → k ≤ 31 → k ∉ measureWritten → gpr after k = gpr before k

/-- **Both length calls.** -/
theorem measure {live : Nat → Prop} {ra sp : BitVec 64} {f buf n : Nat} (c : Config)
    (codeLive : ∀ p ∈ snpText, live p.1) (liveImage : ImageLive live)
    (h : MeasureInput live ra sp f buf n c) :
    FnSummary 0x800103fc#64 (fun d => d = c) (Measured live sp f buf n c) := by
  apply summary_bind (measure_length c h) (fun _ d => d.pc)
  intro d dl
  let R := entryRegs d
  have regs : GHolds d.σ (suffix_input R) := holds_entry dl.libraryGood [1, 2, 8, 10, 18, 20] (by decide)
  have S := suffix_fast d R (by rw [show R 1 = pro_call.link from entry_value dl.raReg]; exact dl.toLeafInput) regs
  apply summary_bind S (fun _ p => p.pc)
  intro e p
  have args : GHolds e.σ [(10, R 18)] := holds_project p.regs (by simp [suffix_regs, lookupG])
  have J := call_registers_summary suffix_call_shape suffix_call_decode e (suffix_call_pins p.image) p.good
    p.image p.tick p.minstret _ args (by change KeysOK [10]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  apply summary_bind J (fun _ q => q.pc)
  intro entered q
  have goodE : VsaOk live e := p.vsaOk dl.libraryGood (by decide) (by simp [suffix_regs, keysG])
  have goodQ : VsaOk live entered := q.vsaOk_of_present goodE (by decide) (by simp [keysG])
    (fun a ha => by rw [q.memory]; exact goodE.live a ha)
  have frameQ (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1]) : gpr entered k = gpr e k :=
    q.toEffectPost.gpr_frame (by decide) k lo hi out
  have frameP (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [10, 19]) : gpr e k = gpr d k :=
    p.toEffectPost.gpr_frame (by decide) k lo hi out
  have hR18 : R 18 = 0x80055088#64 := entry_value dl.suffix
  have bytes := suffix_bytes q.image
  have string : StrRead entered.σ.mem (List.range' suffixAddr 2) (fun _ => False) entered.σ.mem suffixAddr 1
      (imgM entered.σ.mem) :=
    { win := fun x low high => Or.inl ⟨List.mem_range'_1.2 ⟨low, by omega⟩, rfl⟩
      nz := fun i hi => by rw [show i = 0 by omega, Nat.add_zero, bytes.1]; decide
      nul := bytes.2
      lo := by decide
      hi := by decide
      htif := by decide }
  have readOnly : ROHolds (vsaModel live) entered roR
      (snpText ++ dataOf entered.σ.mem (List.range' suffixAddr 2)) := by
    have gp := globalPointer_of_gpr (live := live) ((frameQ 3 (by decide) (by decide) (by decide)).trans
      ((frameP 3 (by decide) (by decide) (by decide)).trans
        (dl.kept 3 (by decide) (by decide) (by decide)))) h.globalPointer
    refine ⟨gp.1, ?_⟩
    intro r hr
    rcases List.mem_append.1 hr with snp | data
    · change (entered.σ.mem[r.1]?).getD 0 = r.2
      rw [snp_text_loaded q.image r snp]; rfl
    · obtain ⟨a, _, rfl⟩ := List.mem_map.1 data
      rfl
  have arg : gpr entered 10 = some (BitVec.ofNat 64 suffixAddr) := by
    rw [show BitVec.ofNat 64 suffixAddr = R 18 from hR18.symm]
    exact gholds_lookup (n := 10) _ q.regs rfl
  have L := strlen_call entered codeLive string goodQ q.image liveImage readOnly arg
    (gholds_lookup (n := 1) _ q.regs rfl) (by decide)
  apply L.weaken (fun _ eq => eq)
  intro after r
  have frameR (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [10, 11, 12, 13, 14, 15]) :
      gpr after k = gpr entered k := r.registers k lo hi out
  have back (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1, 10, 11, 12, 13, 14, 15, 19]) :
      gpr after k = gpr d k := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    rw [frameR k lo hi (by simp; omega), frameQ k lo hi (by simp; omega), frameP k lo hi (by simp; omega)]
  refine ⟨r.toLeafInput, r.libraryGood, ?_, r.pc, ?_, ?_, r.result, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact globalPointer_of_gpr ((back 3 (by decide) (by decide) (by decide)).trans
      (dl.kept 3 (by decide) (by decide) (by decide))) h.globalPointer
  · intro x
    have m := r.memory x
    have pm : e.σ.mem = d.σ.mem := p.memory
    rw [q.memory, pm, dl.memory] at m
    exact m
  · exact r.output.trans (by simp only [Vsa.Machine.output, q.output, p.output, dl.output])
  · rw [frameR 19 (by decide) (by decide) (by decide), frameQ 19 (by decide) (by decide) (by decide)]
    rw [show gpr e 19 = some (R 10) from gholds_lookup (n := 19) _ p.regs rfl]
    exact congrArg some (entry_value dl.length)
  · rw [back 2 (by decide) (by decide) (by decide), dl.stack]
  · rw [back 8 (by decide) (by decide) (by decide), dl.buffer]
  · rw [back 18 (by decide) (by decide) (by decide), dl.suffix]
  · rw [back 20 (by decide) (by decide) (by decide), dl.fmt]
  · intro k lo hi out
    simp only [measureWritten, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    rw [back k lo hi (by simp; omega), dl.kept k lo hi (by simp [lengthWritten]; omega)]

end OCaml.Vm.Primitives.Format.ParseFormat
