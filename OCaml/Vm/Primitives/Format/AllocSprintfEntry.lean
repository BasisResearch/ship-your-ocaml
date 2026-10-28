import OCaml.Vm.Primitives.Format.AllocSprintf
import OCaml.Vm.Primitives.Format.VsnprintfLong
import OCaml.Vm.Primitives.Format.ParseFormatCall
import OCaml.Vm.Primitives.InitializedString

/-! The real variadic prologue and decoded vsnprintf call. All data
requirements refer to the incoming memory, before its eleven stores. -/
namespace OCaml.Vm.Primitives.Format.AllocSprintfLong
open Vsa.Machine Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open OCaml.Vm.Boot.Startup

/-- Read a selected scalar store after a separated suffix. -/
theorem stored_word (m : Mem) (earlier later : List WEntry) (a : Nat) (value : BitVec 64)
    (outside : OutLRange later a 8) :
    bytesT (writeLog m (earlier ++ [(a, 8, value)] ++ later)) a 8 = value := by
  rw [writeLog_append, bytesT_writeLog_out _ outside, writeLog_append]
  exact word_writeLog _ _ _

/-- The symbolic library load and native total-word view agree. -/
theorem ldv_word (m : Mem) (a : Nat) : ldv .ld m a = bytesT m a 8 := by
  rw [← read8_value]
  rfl

/-- The eleven actual stores, with the caller's stack expressed as a natural
address. In particular seven consecutive varargs end at the caller's sp. -/
def entryLog (R : Nat → BitVec 64) (sp : Nat) : List WEntry :=
  [(sp + 160, 8, R 8), (sp + 144, 8, R 18), (sp + 184, 8, R 11),
   (sp + 192, 8, R 12), (sp + 200, 8, R 13), (sp + 216, 8, R 15),
   (sp + 168, 8, R 1), (sp + 208, 8, R 14), (sp + 224, 8, R 16),
   (sp + 232, 8, R 17), (sp + 8, 8, BitVec.ofNat 64 (sp + 184))]

theorem entry_log {R : Nat → BitVec 64} {sp : Nat}
    (stack : R 2 = BitVec.ofNat 64 (sp + 240)) (bound : sp + 240 < 2^64) :
    AllocSprintf.proLog R [] = entryLog R sp := by
  have base : R 2 - 240#64 = BitVec.ofNat 64 sp := by rw [stack]; bv_omega
  simp only [AllocSprintf.proLog, base, ofNat_add_ofNat, entryLog]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show sp + 160 < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp + 144 < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp + 184 < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp + 192 < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp + 200 < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp + 216 < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp + 168 < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp + 208 < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp + 224 < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp + 232 < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp + 8 < 2^64 by omega)]

/-- The prologue's stores lie in one native stack window. -/
theorem entry_inside (R : Nat → BitVec 64) (sp : Nat) :
    LogInW [⟨sp, sp + 240⟩] (entryLog R sp) := by
  simp [entryLog, LogInW, InsideW]

/-- The write-window frame is shared by every prologue read and caller frame. -/
theorem entry_frame (R : Nat → BitVec 64) (sp : Nat) (m : Mem) (x : Nat)
    (outside : x < sp ∨ sp + 240 ≤ x) :
    (writeLog m (entryLog R sp))[x]? = m[x]? :=
  frameOn_writeLog _ _ _ (entry_inside R sp) x ⟨outside, trivial⟩

/-- All readbacks used by the formatter: the first vararg and its native
save bank. They follow from stores, with no incoming slot-value assumptions. -/
structure EntryWords (R : Nat → BitVec 64) (sp : Nat) (m : Mem) : Prop where
  argument : bytesT m (sp + 184) 8 = R 11
  ra : bytesT m (sp + 168) 8 = R 1
  s0 : bytesT m (sp + 160) 8 = R 8
  s2 : bytesT m (sp + 144) 8 = R 18

theorem entry_words (R : Nat → BitVec 64) (sp : Nat) (m : Mem) :
    EntryWords R sp (writeLog m (entryLog R sp)) := by
  constructor
  · exact stored_word m ((entryLog R sp).take 2) ((entryLog R sp).drop 3)
      (sp + 184) (R 11) (by simp [entryLog, OutLRange])
  · exact stored_word m ((entryLog R sp).take 6) ((entryLog R sp).drop 7)
      (sp + 168) (R 1) (by simp [entryLog, OutLRange])
  · exact stored_word m [] ((entryLog R sp).drop 1)
      (sp + 160) (R 8) (by simp [entryLog, OutLRange])
  · exact stored_word m ((entryLog R sp).take 1) ((entryLog R sp).drop 2)
      (sp + 144) (R 18) (by simp [entryLog, OutLRange])

/-- Runtime locale/table and parsed `%ld` facts. The parser's four bytes are
read-only at the original caller sp, beyond all seven spills. -/
structure DecimalData (Dt : Mem) (DA : List Nat) (sp : Nat) (m : Mem) : Prop where
  data : DataOff Dt DA (sp + 48) (sp + 16) 128
  dot : DotAt Dt DA
  impure : InDA DA 0x800648f8 0x80064900
  decimalPoint : ldv .ld m 0x800645a0 = 0x80053180#64
  mbtowc : ldv .ld m 0x80064588 = 0x80045798#64
  multibyte : ldv .lbu m 0x80064600 = 1#64
  formatGeom : FmtGeom DA (sp + 240) 3
  percent : imgM Dt (sp + 240) = 37#8
  long : imgM Dt (sp + 241) = 0x6c#8
  decimal : imgM Dt (sp + 242) = 0x64#8
  nul : imgM Dt (sp + 243) = 0#8

/-- Prologue conditions at the real original native entry. -/
structure EntryInput (live : Nat → Prop) (Dt : Mem) (DA : List Nat)
    (R : Nat → BitVec 64) (sp : Nat) (c : Config) : Prop extends LeafInput (R 1) c where
  goodLibrary : VsaOk live c
  registers : GHolds c.σ (AllocSprintf.pro_input R)
  stack : R 2 = BitVec.ofNat 64 (sp + 240)
  format : R 10 = BitVec.ofNat 64 (sp + 240)
  lower : 0x8007d138 + 1024 ≤ sp
  upper : sp + 240 ≤ 0x88000000
  alignment : sp % 16 = 0
  windows : ∀ k ∈ [160, 144, 184, 192, 200, 216, 168, 208, 224, 232, 8],
    WriteWindow (R 2 - 240#64 + BitVec.ofNat 64 k) 8
  imageOutside : ImageOutside (AllocSprintf.proLog R [])
  codeLive : ∀ b ∈ snpText, live b.1
  readOnly : ROHolds (vsaModel live) c roR (snpText ++ dataOf Dt DA)
  readsOutside : ∀ p ∈ snpText ++ dataOf Dt DA, OutL (AllocSprintf.proLog R []) p.1
  separate : LocalSeparation roR (snpText ++ dataOf Dt DA) nRegs (snpS (sp + 48) (sp + 16) 128)
  data : DecimalData Dt DA sp c.σ.mem

/-- Actual call boundary, including a symbolic input derived from native
observations and a decimal contract derived from the prologue stores. -/
structure VsnEntered (live : Nat → Prop) (Dt : Mem) (DA : List Nat)
    (R : Nat → BitVec 64) (sp : Nat) (before after : Config) : Prop where
  leaf : LeafInput AllocSprintf.pro_call.link after
  pc : OCaml.Vm.pcOf after = some 0x8004018c#64
  memory : after.σ.mem = writeLog before.σ.mem (entryLog R sp)
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  same : GprsSame before after [1, 2, 8, 10, 11, 12, 13, 18]
  entry : VsnLongEntry Dt DA (sp + 48) (sp + 16) 128 (sp + 240) (sp + 184)
    (R 11) ((vsaModel live).reg after) after.σ.mem
  input : SymbolicInput live (snpText ++ dataOf Dt DA) nRegs
    (snpS (sp + 48) (sp + 16) 128) ((vsaModel live).reg after) after.σ.mem after

/-- Select the real vsnprintf argument registers without expanding a machine state. -/
theorem pro_arguments {σ : MState} {R : Nat → BitVec 64} {sp : Nat}
    (stack : R 2 = BitVec.ofNat 64 (sp + 240))
    (format : R 10 = BitVec.ofNat 64 (sp + 240))
    (regs : GHolds σ (AllocSprintf.pro_regs R [])) :
    GHolds σ [(2, BitVec.ofNat 64 sp), (10, BitVec.ofNat 64 (sp + 16)),
      (11, 128#64), (12, BitVec.ofNat 64 (sp + 240)), (13, BitVec.ofNat 64 (sp + 184))] := by
  have base : R 2 + 18446744073709551376#64 = BitVec.ofNat 64 sp := by rw [stack]; bv_omega
  have dest : R 2 + 18446744073709551392#64 = BitVec.ofNat 64 (sp + 16) := by rw [stack]; bv_omega
  have arg : R 2 + 18446744073709551560#64 = BitVec.ofNat 64 (sp + 184) := by rw [stack]; bv_omega
  exact holds_project regs (by simp [AllocSprintf.pro_regs, lookupG, base, dest, arg, format])

/-- The actual 240-byte prologue, all seven spills and decoded vsnprintf JAL. -/
theorem enter {live Dt DA R sp} (c : Config) (h : EntryInput live Dt DA R sp c) :
    FnSummary 0x80013ec4#64 (fun d => d = c) (VsnEntered live Dt DA R sp c) := by
  have logEq := entry_log h.stack (by have := h.upper; omega)
  have bound := h.upper
  have lower := h.lower
  have pro := AllocSprintf.pro_fast c R h.toLeafInput h.registers
    (h.windows 160 (by simp)) (h.windows 144 (by simp)) (h.windows 184 (by simp))
    (h.windows 192 (by simp)) (h.windows 200 (by simp)) (h.windows 216 (by simp))
    (h.windows 168 (by simp)) (h.windows 208 (by simp)) (h.windows 224 (by simp))
    (h.windows 232 (by simp)) (h.windows 8 (by simp)) h.imageOutside
  apply summary_bind pro (fun _ p => p.pc)
  intro prepared p
  have good := p.vsaOk h.goodLibrary (by decide) (by simp [AllocSprintf.pro_regs, keysG])
  have args : GHolds prepared.σ [(2, BitVec.ofNat 64 sp),
      (10, BitVec.ofNat 64 (sp + 16)), (11, 128#64),
      (12, BitVec.ofNat 64 (sp + 240)), (13, BitVec.ofNat 64 (sp + 184))] := pro_arguments h.stack h.format p.regs
  have J := call_registers_summary AllocSprintf.pro_call_shape AllocSprintf.pro_call_decode
    prepared (AllocSprintf.pro_call_pins p.image) p.good p.image p.tick p.minstret _ args
    (by change KeysOK [2, 10, 11, 12, 13]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  apply J.weaken (fun _ eq => eq)
  intro entered q
  have good' := q.vsaOk (log := []) good (by decide) (by simp [keysG])
  have memory : entered.σ.mem = writeLog c.σ.mem (entryLog R sp) := by
    simpa only [AllocSprintf.pro_loads, logEq] using q.memory.trans p.memory
  have readonly := p.toEffectPost.readOnly_log (by decide) (by decide) h.readOnly h.readsOutside
  have readonly' := readonly_transport readonly
    (fun pair member => by
      have eq : pair = (3, gpV) := List.mem_singleton.mp member
      subst pair
      exact q.toEffectPost.observed_gpr (by decide) 3 (by decide) (by decide) (by decide))
    (fun _ => by rw [q.memory])
  have reg : ∀ n value, 1 ≤ n → n ≤ 31 → lookupG n ((1, AllocSprintf.pro_call.link) ::
      [(2, BitVec.ofNat 64 sp), (10, BitVec.ofNat 64 (sp + 16)), (11, 128#64),
       (12, BitVec.ofNat 64 (sp + 240)), (13, BitVec.ofNat 64 (sp + 184))]) = some value →
      (vsaModel live).reg entered n = value := by
    intro n value lo hi lookup
    have present := gholds_lookup _ q.regs lookup
    change vsaReg entered n = value
    rw [vsaReg_gpr (by change n ≠ 32; omega), present]; rfl
  have leaf : LeafInput AllocSprintf.pro_call.link entered :=
    ⟨q.good, q.image, q.minstret, gholds_lookup _ q.regs rfl, by decide, q.tick⟩
  have ldframe : ∀ k a, a + widthOfM k ≤ sp → ldv k entered.σ.mem a = ldv k c.σ.mem a := by
    intro k a high
    apply ldv_agree
    intro i hi
    change (entered.σ.mem[a + i]?).getD 0 = (c.σ.mem[a + i]?).getD 0
    rw [memory, entry_frame R sp c.σ.mem (a + i) (.inl (by omega))]
  have words := entry_words R sp c.σ.mem
  rw [← memory] at words
  have layout := vsnprintf_layout h.lower (by omega) h.alignment
  refine ⟨leaf, q.pc, memory, ?_, ?_, ?_, ⟨good', readonly', fun _ _ _ => rfl, fun _ _ => rfl⟩⟩
  · simp only [Vsa.Machine.output, q.output, p.output]
  · exact ((GprsSame.of_post p (by decide)).trans (GprsSame.of_post q (by decide))).mono
      (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; omega)
  · refine ⟨⟨layout.geom, .inr (by omega)⟩, ?_, reg 10 _ (by decide) (by decide) rfl, reg 11 _ (by decide) (by decide) rfl,
      reg 12 _ (by decide) (by decide) rfl, reg 13 _ (by decide) (by decide) rfl, ?_, h.data.data, h.data.dot, h.data.impure,
      (ldframe .ld _ (by simp only [widthOfM]; omega)).trans h.data.decimalPoint,
      (ldframe .ld _ (by simp only [widthOfM]; omega)).trans h.data.mbtowc,
      (ldframe .lbu _ (by simp only [widthOfM]; omega)).trans h.data.multibyte,
      h.data.formatGeom, h.data.percent, ?_, ?_, ?_, ?_, layout.args.head (by decide), .inr (by omega)⟩
    · simpa only [show sp + 48 - 48 = sp by omega] using reg 2 _ (by decide) (by decide) rfl
    · rw [reg 1 _ (by decide) (by decide) rfl]; decide
    · simpa only [show sp + 240 + 1 = sp + 241 by omega] using h.data.long
    · simpa only [show sp + 240 + 2 = sp + 242 by omega] using h.data.decimal
    · simpa only [show sp + 240 + 3 = sp + 243 by omega] using h.data.nul
    · rw [toNat_ofNat_lt (by omega)]
      rw [ldv_word]; exact words.argument

end OCaml.Vm.Primitives.Format.AllocSprintfLong
