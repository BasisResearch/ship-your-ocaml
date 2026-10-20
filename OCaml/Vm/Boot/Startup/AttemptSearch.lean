import OCaml.Vm.Boot.Startup.DomainRecord
import OCaml.Vm.Boot.Startup.SearchExeReset
import OCaml.Vm.Boot.Startup.SearchInPathSlash
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-! caml_attempt_open(&exe_name, &trail, flag) from caml_main's frame at
`parameterStack`, through `caml_search_exe_in_path(exe_name)`: the saves,
`caml_ext_table_init(&path, 8)`, `getenv("PATH")` (absent), the empty path
decomposition, `caml_search_in_path` (a fresh copy of the name, for a plain or
a `/`-rooted name), the frees and the return. Both of caml_main's attempts
run this. -/

/-- A name `caml_search_in_path` copies without consulting the path. -/
def SearchName (m : Vsa.MemRepr.Mem) (p : BitVec 64) (len : Nat) : Prop :=
  PlainName m p len ∨ RootedName m p len

structure AttemptSearched (H : List (Nat × Nat)) (capacity : Nat) (ra s0 s1 s2 s3 s4 flag name : BitVec 64)
    (len : Nat) (before after : Config) where
  copy : BitVec 64
  result : gprGet after.σ 10 = some copy
  pc : PCAt jal_800048ec_call.link after
  stack : gprGet after.σ 2 = some attemptStack
  trail : gprGet after.σ 8 = some trailSlot
  slot : gprGet after.σ 19 = some exeNameSlot
  flagReg : gprGet after.σ 20 = some flag
  /-- caml_main's s5–s11 are untouched. -/
  upper : ∀ k, 21 ≤ k → k ≤ 27 → gprGet after.σ k = gprGet before.σ k
  ready : RuntimeReady ((copy.toNat, len + 1) :: H) capacity attemptStack jal_800048ec_call.link after
  fresh : heapStart ≤ copy.toNat ∧ copy.toNat + (len + 1) ≤ heapEnd
  aligned : copy.toNat % 16 = 0
  disjoint : ∀ e ∈ H, ∀ a, InExt (copy.toNat, len + 1) a → ¬ InExt e a
  bytes : ∀ k, k ≤ len → (after.σ.mem[copy.toNat + k]?).getD 0 = (WhileMinImage.initialMem[name.toNat + k]?).getD 0
  /-- caml_attempt_open's six saves. -/
  slots : ∀ off value, (off, value) ∈ attemptOpenSlots ra s0 s1 s2 s3 s4 →
    bytesT after.σ.mem (nativeFrameBase parameterStack 64 + off) 8 = value
  caller : CallerFrame parameterStack before after
  /-- Every block of `H` is untouched. -/
  live : LiveFrame H before after
  kept : EmbedFrame before after
  late : LateImage after
  run : Steps before after

theorem attempt_open_search (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (ra s0 s1 s2 s3 s4 flag name : BitVec 64) (len : Nat)
    (ready : RuntimeReady H ((capacity + charge) + 64) parameterStack ra c)
    (regs : GHolds c.σ (attemptOpenInput parameterStack ra s0 s1 s2 s3 s4 exeNameSlot ++
      [(11, trailSlot), (12, flag)]))
    (late : LateImage c) (exeName : bytesT c.σ.mem exeNameSlot.toNat 8 = name)
    (embedded : ∀ k, k ≤ len → EmbedByte (name.toNat + k))
    (kind : ∀ d : Config, EmbedImage d → SearchName d.σ.mem name len)
    (small : len ≤ 64) (charged : vsaChg (len + 1) charge) :
    FnSummary 0x800048c0#64 (fun d => d = c)
      (fun after => Nonempty (AttemptSearched H capacity ra s0 s1 s2 s3 s4 flag name len c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have entry := (gholds_append _ _).1 regs
  -- caml_attempt_open: saves
  have attemptFrame : NativeFrame parameterStack 64 := by constructor <;> decide
  obtain ⟨atSaved, run2, save⟩ := (attempt_open_save c parameterStack ra s0 s1 s2 s3 s4 exeNameSlot
    ready.toLeafInput attemptFrame entry.1).run c ⟨pc, rfl⟩
  have savedReady := ready.stack_log save (by decide)
    (by simp only [attemptOpenSaved, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ save.regs (by rfl)) (gholds_lookup (n := 1) _ save.regs (by rfl))
    ready.aligned attemptFrame (attemptOpenLog_inside attemptFrame)
  have savedArg (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [2, 19])
      (h : gprGet c.σ n = some v) : gprGet atSaved.σ n = some v :=
    (save.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans h
  have aboveSaved : CallerFrame parameterStack c atSaved :=
    CallerFrame.of_log save.memory (attemptOpenLog_inside attemptFrame)
  have nameSaved : bytesT atSaved.σ.mem exeNameSlot.toNat 8 = name := by
    rw [word_observed (m := c.σ.mem) _ (fun i _ => aboveSaved.byte _ (by
      show parameterStack.toNat ≤ exeNameSlot.toNat + i
      have : parameterStack.toNat ≤ exeNameSlot.toNat := by decide
      omega))]
    exact exeName
  -- *name; call caml_search_exe_in_path
  obtain ⟨atSearch, run3, nameCall⟩ := (attempt_open_name atSaved ra parameterStack s1 s2 exeNameSlot trailSlot flag
    savedReady.toLeafInput
    ⟨gholds_lookup (n := 10) _ save.regs (by rfl),
      savedArg 11 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 11) _ entry.2 (by rfl)),
      savedArg 12 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 12) _ entry.2 (by rfl)),
      gholds_lookup (n := 19) _ save.regs (by rfl), gholds_lookup (n := 2) _ save.regs (by rfl),
      gholds_lookup (n := 9) _ save.regs (by rfl), gholds_lookup (n := 18) _ save.regs (by rfl), trivial⟩
    (by constructor <;> decide)).run atSaved ⟨save.pc, rfl⟩
  rw [nameSaved] at nameCall
  have nameReady := savedReady.effect nameCall (by decide)
    (by simp only [attemptOpenRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ nameCall.regs (by rfl)) (gholds_lookup (n := 1) _ nameCall.regs (by rfl)) (by decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  -- caml_search_exe_in_path: saves; caml_ext_table_init(&path, 8)
  have searchFrame : NativeFrame attemptStack 48 := by constructor <;> decide
  obtain ⟨atTable, run4, search⟩ := (search_exe_prefix atSearch attemptStack jal_800048ec_call.link trailSlot
    s1 name nameReady.toLeafInput searchFrame
    ⟨gholds_lookup (n := 2) _ nameCall.regs (by rfl), gholds_lookup (n := 8) _ nameCall.regs (by rfl),
      gholds_lookup (n := 10) _ nameCall.regs (by rfl), gholds_lookup (n := 1) _ nameCall.regs (by rfl),
      gholds_lookup (n := 9) _ nameCall.regs (by rfl), trivial⟩).run atSearch ⟨nameCall.pc, rfl⟩
  have tableReady := nameReady.stack_log search (by decide)
    (by simp only [searchExeArgs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ search.regs (by rfl)) (gholds_lookup (n := 1) _ search.regs (by rfl))
    (by decide) searchFrame (searchExeLog_inside searchFrame)
  have tableFrame : NativeFrame searchStack 560 := by constructor <;> decide
  obtain ⟨source, run5, ⟨T⟩⟩ := (ext_table_init atTable H (capacity + charge) 64 searchStack
    jal_8002554c_call.link name searchStack 8#64 tableReady tableFrame
    (ExtTableSite.at_sp (tableFrame.resize (by decide) (by decide)) (by decide))
    (gholds_lookup (n := 8) _ search.regs (by rfl)) (gholds_lookup (n := 10) _ search.regs (by rfl))
    (gholds_lookup (n := 11) _ search.regs (by rfl)) (by constructor <;> decide)).run atTable ⟨search.pc, rfl⟩
  have readyS := T.ready
  -- registers caml_attempt_open keeps across the search
  have toTable (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31)
      (unwritten : n ∉ [2, 11, 8, 10, 1] ∧ n ∉ [20, 8, 10, 1]) (h : gprGet atSaved.σ n = some v) :
      gprGet atTable.σ n = some v :=
    (search.toEffectPost.gpr_frame (by decide) n lower upper unwritten.1).trans
      ((nameCall.toEffectPost.gpr_frame (by decide) n lower upper unwritten.2).trans h)
  have slotSource : gprGet source.σ 19 = some exeNameSlot :=
    T.keep_saved (by decide) (toTable 19 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ save.regs rfl))
  have flagSource : gprGet source.σ 20 = some flag :=
    T.keep_upper (by decide) (by decide)
      ((search.toEffectPost.gpr_frame (by decide) 20 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 20) _ nameCall.regs rfl))
  have upperSource (k : Nat) (lo : 21 ≤ k) (hi : k ≤ 27) (v : BitVec 64) (h : gprGet c.σ k = some v) :
      gprGet source.σ k = some v :=
    T.keep_upper (by omega) hi (toTable k v (by omega) (by omega) (by simp; omega)
      (savedArg k v (by omega) (by omega) (by simp; omega) h))
  have keptSource : EmbedFrame c source :=
    (EmbedFrame.stack save.memory (attemptOpenLog_inside attemptFrame) (by decide)).trans
      ((EmbedFrame.of_memory nameCall.memory).trans
        ((EmbedFrame.stack search.memory (searchExeLog_inside searchFrame) (by decide)).trans
          (T.embed_frame tableFrame (ExtTableSite.at_sp (tableFrame.resize (by decide) (by decide)) (by decide))
            (by decide))))
  have lateSource : LateImage source := late.frame keptSource
  -- getenv("PATH"): absent
  obtain ⟨atGetenv, run6, pcall⟩ := (search_exe_path source _ readyS.toLeafInput).run source ⟨T.post.pc, rfl⟩
  have keep (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [10, 1]) :
      gprGet atGetenv.σ n = some (vsaReg source n) :=
    (pcall.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans (gpr_of_ready readyS n lower upper)
  have same : atGetenv.σ.mem = source.σ.mem := pcall.memory
  have lateG := lateSource.frame (EmbedFrame.of_memory same)
  have envWord (a : Nat) (inside : ∀ i, i < 8 → EmbedByte (a + i)) :
      bytesT atGetenv.σ.mem a 8 = bytesT WhileMinImage.initialMem a 8 := lateG.embed.word a inside
  have entryByte : (atGetenv.σ.mem[(0x8680007f#64 : BitVec 64).toNat]?).getD 0 = BitVec.ofNat 8 79 := by
    have byte := lateG.embed.byte WhileMinImage.envEntry (embed_bytes (n := 1) (by decide) 0 (by decide))
    have value := cstr_getD WhileMinImage.env_string 0 (by decide)
    exact byte.trans value
  have nameByte : (atGetenv.σ.mem[pathName0.toNat]?).getD 0 = BitVec.ofNat 8 80 :=
    cstr_getD (path_name_0 pcall.image).bytes 0 (by decide)
  have frame112 : NativeFrame searchStack 112 := by constructor <;> decide
  have input : GetenvMissInput searchStack (BitVec.ofNat 64 WhileMinImage.envArray) 0x8680007f#64 pathName0
      jal_80025558_call.link name (vsaReg source 9) (vsaReg source 18)
      (vsaReg source 19) (vsaReg source 20) (vsaReg source 21) (vsaReg source 22) pathChars0
      (BitVec.ofNat 8 79) (BitVec.ofNat 8 80) atGetenv := {
    toLeafInput := pcall.leaf (by rfl) (by decide)
    frame := frame112
    regs := ⟨gholds_lookup (n := 10) _ pcall.regs (by rfl),
      (pcall.frame .x2 (by decide) (by decide)).trans readyS.stack, gholds_lookup (n := 1) _ pcall.regs (by rfl),
      trivial⟩
    saved := ⟨keep 9 (by decide) (by decide) (by decide), keep 18 (by decide) (by decide) (by decide),
      keep 19 (by decide) (by decide) (by decide), keep 20 (by decide) (by decide) (by decide),
      keep 21 (by decide) (by decide) (by decide), keep 22 (by decide) (by decide) (by decide), trivial⟩
    saved0 := (pcall.frame .x8 (by decide) (by decide)).trans (gholds_lookup (n := 8) _ T.post.regs (by rfl))
    query := path_name_0 pcall.image
    positive := by decide
    small := by decide
    nameBelow := by decide
    environment := lateG.environ
    envNonzero := by decide
    array := by constructor <;> decide
    first := by
      rw [show (BitVec.ofNat 64 WhileMinImage.envArray).toNat = WhileMinImage.envArray from by decide,
        envWord _ (embed_bytes (by decide))]
      exact WhileMinImage.env_first
    entryNonnull := by decide
    next := by constructor <;> decide
    last := by
      rw [show (BitVec.ofNat 64 WhileMinImage.envArray + 8#64).toNat = WhileMinImage.envArray + 8 from by decide,
        envWord _ (embed_bytes (by decide))]
      exact WhileMinImage.env_end
    arrayBelow := by decide
    firstBelow := by decide
    entryWindow := by constructor <;> decide
    nameWindow := by constructor <;> decide
    entryByte := entryByte
    nameByte := by rw [show pathName0.toNat = pathName0.toNat + 0 from rfl]; exact nameByte
    differ := by decide
    entryBelow := by decide
    unaligned := by decide }
  obtain ⟨atD, run7, missed⟩ := (getenv_miss atGetenv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ input).run atGetenv
    ⟨pcall.pc, rfl⟩
  have frame32 : NativeFrame searchStack 32 := by constructor <;> decide
  have readyG := readyS.stack_log pcall (by decide) (by simp only [keysG]; decide) (by decide)
    ((pcall.frame .x2 (by decide) (by decide)).trans readyS.stack) (gholds_lookup (n := 1) _ pcall.regs (by rfl))
    (by decide) frame112 (by simp only [LogInW])
  have readyD := readyG.stack_log missed (by decide)
    (by simp only [getenvReturnRegs, getenvMissKeptRegs, getenvSavedRegs, findMissScratch, List.cons_append,
      List.nil_append, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ missed.regs (by rfl)) (gholds_lookup (n := 1) _ missed.regs (by rfl))
    (by decide) frame112 (getenvMissLog_inside frame112)
  -- s4–s11 of caml_attempt_open at getenv's return
  have upperD (k : Nat) (lo : 20 ≤ k) (hi : k ≤ 27) : gprGet atD.σ k = some (vsaReg source k) := by
    by_cases low : k ≤ 22
    · have cases : k = 20 ∨ k = 21 ∨ k = 22 := by omega
      rcases cases with rfl | rfl | rfl
      · exact gholds_lookup (n := 20) _ missed.regs (by rfl)
      · exact gholds_lookup (n := 21) _ missed.regs (by rfl)
      · exact gholds_lookup (n := 22) _ missed.regs (by rfl)
    · exact (missed.toEffectPost.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega)).trans
        (keep k (by omega) (by omega) (by simp; omega))
  -- caml_decompose_path(&path, NULL)
  obtain ⟨atDec, run8, dcall⟩ := (search_exe_decompose atD _ searchStack 0#64 readyD.toLeafInput
    ⟨gholds_lookup (n := 10) _ missed.regs (by rfl), gholds_lookup (n := 2) _ missed.regs (by rfl),
      trivial⟩).run atD ⟨missed.pc, rfl⟩
  have readyDec := readyD.stack_log dcall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ dcall.regs (by rfl)) (gholds_lookup (n := 1) _ dcall.regs (by rfl))
    (by decide) frame32 (by simp only [LogInW])
  have s2D : gprGet atDec.σ 18 = some (vsaReg source 18) :=
    (dcall.toEffectPost.gpr_frame (by decide) 18 (by decide) (by decide) (by decide)).trans
      (gholds_lookup (n := 18) _ missed.regs (by rfl))
  obtain ⟨atS, run9, dnull⟩ := (decompose_null atDec searchStack jal_80025564_call.link (vsaReg source 18)
    searchStack readyDec.toLeafInput frame32
    ⟨gholds_lookup (n := 2) _ dcall.regs (by rfl), gholds_lookup (n := 1) _ dcall.regs (by rfl), s2D,
      gholds_lookup (n := 11) _ dcall.regs (by rfl), gholds_lookup (n := 10) _ dcall.regs (by rfl),
      trivial⟩).run atDec ⟨dcall.pc, rfl⟩
  have readyS2 := readyDec.stack_log dnull (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ dnull.regs (by rfl)) (gholds_lookup (n := 1) _ dnull.regs (by rfl))
    (by decide) frame32 (decomposeLog_inside frame32)
  have carried (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31)
      (unwritten : n ∉ [2, 1, 18, 10] ∧ n ∉ [11, 10] ++ [1]) (hv : gprGet atD.σ n = some v) :
      gprGet atS.σ n = some v :=
    (dnull.toEffectPost.gpr_frame (by decide) n lower upper unwritten.1).trans
      ((dcall.toEffectPost.gpr_frame (by decide) n lower upper unwritten.2).trans hv)
  have s0S : gprGet atS.σ 8 = some name :=
    carried 8 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ missed.regs (by rfl))
  -- caml_search_in_path(&path, name)
  obtain ⟨atP, run10, scall⟩ := (search_exe_search atS _ searchStack name 0#64 readyS2.toLeafInput
    ⟨s0S, gholds_lookup (n := 10) _ dnull.regs (by rfl), gholds_lookup (n := 2) _ dnull.regs (by rfl),
      trivial⟩).run atS ⟨dnull.pc, rfl⟩
  have readyP := readyS2.stack_log scall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ scall.regs (by rfl)) (gholds_lookup (n := 1) _ scall.regs (by rfl))
    (by decide) frame32 (by simp only [LogInW])
  have toP (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [11, 9, 10] ++ [1])
      (hv : gprGet atS.σ n = some v) : gprGet atP.σ n = some v :=
    (scall.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans hv
  have callerP : CallerFrame searchStack source atP :=
    (CallerFrame.of_memory pcall.memory).trans ((CallerFrame.of_log missed.memory
      (getenvMissLog_inside frame112)).trans ((CallerFrame.of_memory dcall.memory).trans
      ((CallerFrame.of_log dnull.memory (decomposeLog_inside frame32)).trans (CallerFrame.of_memory scall.memory))))
  have keptP : EmbedFrame source atP :=
    (EmbedFrame.of_memory pcall.memory).trans ((EmbedFrame.stack missed.memory
      (getenvMissLog_inside frame112) (by decide)).trans ((EmbedFrame.of_memory dcall.memory).trans
      ((EmbedFrame.stack dnull.memory (decomposeLog_inside frame32) (by decide)).trans
        (EmbedFrame.of_memory scall.memory))))
  have lateP : LateImage atP := lateSource.frame keptP
  have frameP : NativeFrame searchStack (176 + (48 + allocHeadroom)) := by constructor <;> decide
  have readyP16 : RuntimeReady (((vsaReg T.allocation.allocation.allocated 10).toNat,
      (extTableRequest 8#64).toNat) :: H) (capacity + charge) searchStack jal_80025574_call.link atP := readyP
  have searchRegs : GHolds atP.σ [(8, name), (9, 0#64), (18, vsaReg source 18), (19, vsaReg source 19),
      (10, searchStack), (11, name)] :=
    ⟨gholds_lookup (n := 8) _ scall.regs (by rfl), gholds_lookup (n := 9) _ scall.regs (by rfl),
      toP 18 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ dnull.regs (by rfl)),
      toP 19 _ (by decide) (by decide) (by decide)
        (carried 19 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ missed.regs (by rfl))),
      gholds_lookup (n := 10) _ scall.regs (by rfl), gholds_lookup (n := 11) _ scall.regs (by rfl), trivial⟩
  have bound0 := embedded 0 (Nat.zero_le _)
  have source' (k : Nat) (hk : k ≤ len) : StrdupKept (((vsaReg T.allocation.allocation.allocated 10).toNat,
      (extTableRequest 8#64).toNat) :: H) (nativeStack searchStack 176) (name.toNat + k) := by
    obtain ⟨lo, hi⟩ := embedded k hk
    have limit : embedLimit + 48 + allocHeadroom < (nativeStack searchStack 176).toNat := by decide
    exact Or.inr (Or.inl ⟨lo, by omega⟩)
  have outside' (k : Nat) (hk : k ≤ len) :
      name.toNat + k < nativeFrameBase searchStack 176 ∨ searchStack.toNat ≤ name.toNat + k := by
    obtain ⟨lo, hi⟩ := embedded k hk
    have limit : embedLimit ≤ nativeFrameBase searchStack 176 := by decide
    exact Or.inl (by omega)
  have geo : name.toNat + (len + 1) ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 16 ≤ name.toNat := by
    obtain ⟨lo, hi⟩ := bound0
    right; unfold heapEnd Layout.sym_tohost at *; omega
  obtain ⟨atF, run11, ⟨found⟩⟩ : ∃ atF, Steps atP atF ∧ Nonempty (SearchInPathDone
      (((vsaReg T.allocation.allocation.allocated 10).toNat, (extTableRequest 8#64).toNat) :: H) capacity searchStack
      jal_80025574_call.link name 0#64 (vsaReg source 18) (vsaReg source 19) name len atP atF) := by
    rcases kind atP lateP.embed with plain | rooted
    · have empty : LPins4 atP.σ.mem searchStack.toNat (List.replicate 4 0#8) := by
        have zero (i : Nat) (hi : i < 4) : (atP.σ.mem[searchStack.toNat + i]?).getD 0 = 0#8 :=
          (callerP.byte _ (Nat.le_add_right _ _)).trans
            (T.size_byte (by constructor <;> decide)
              (ExtTableSite.at_sp ((show NativeFrame searchStack 560 by constructor <;> decide).resize (by decide)
                (by decide)) (by decide)) i hi)
        exact ⟨zero 0 (by decide), zero 1 (by decide), zero 2 (by decide), zero 3 (by decide)⟩
      exact (search_in_path_plain atP _ capacity charge searchStack jal_80025574_call.link name 0#64
        (vsaReg source 18) (vsaReg source 19) searchStack name len readyP16 frameP searchRegs plain source' outside'
        geo (by constructor <;> decide) (Nat.le_refl _) empty (by omega) charged).run atP ⟨scall.pc, rfl⟩
    · exact (search_in_path_rooted atP _ capacity charge searchStack jal_80025574_call.link name 0#64
        (vsaReg source 18) (vsaReg source 19) searchStack name len readyP16 frameP searchRegs rooted source' outside'
        geo (by omega) charged).run atP ⟨scall.pc, rfl⟩
  -- s0 = the copy; caml_stat_free(tofree = NULL)
  have readyF := found.ready
  obtain ⟨atFree, run12, fcall⟩ := (search_exe_free_tofree atF _ found.copy 0#64 readyF.toLeafInput
    ⟨found.result, found.saved1, trivial⟩).run atF ⟨found.pc, rfl⟩
  have readyFree := readyF.stack_log fcall (by decide) (by simp only [keysG]; decide) (by decide)
    ((fcall.frame .x2 (by decide) (by decide)).trans found.stack) (gholds_lookup (n := 1) _ fcall.regs (by rfl))
    (by decide) frame32 (by simp only [LogInW])
  obtain ⟨atT, run13, freedNull⟩ := (stat_free_null atFree _ readyFree.toLeafInput
    ⟨gholds_lookup (n := 10) _ fcall.regs (by rfl), trivial⟩ readyFree.poolZero).run atFree ⟨fcall.pc, rfl⟩
  have readyT := readyFree.effect freedNull (by decide) (by simp only [keysG]; decide) (by decide)
    ((freedNull.frame .x2 (by decide) (by decide)).trans readyFree.stack)
    (gholds_lookup (n := 1) _ freedNull.regs (by rfl)) (by decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  -- caml_ext_table_free(&path, 0)
  obtain ⟨atE, run14, tcall⟩ := (search_exe_free_table atT _ searchStack readyT.toLeafInput
    ⟨readyT.stack, trivial⟩).run atT ⟨freedNull.pc, rfl⟩
  have readyE := readyT.stack_log tcall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ tcall.regs (by rfl)) (gholds_lookup (n := 1) _ tcall.regs (by rfl))
    (by decide) frame32 (by simp only [LogInW])
  have toE (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31)
      (unwritten : n ∉ [10, 11] ++ [1] ∧ n ∉ [15, 14, 11, 10] ∧ n ∉ [8, 10] ++ [1])
      (hv : gprGet atF.σ n = some v) : gprGet atE.σ n = some v :=
    (tcall.toEffectPost.gpr_frame (by decide) n lower upper unwritten.1).trans
      ((freedNull.toEffectPost.gpr_frame (by decide) n lower upper unwritten.2.1).trans
        ((fcall.toEffectPost.gpr_frame (by decide) n lower upper unwritten.2.2).trans hv))
  have callerF : CallerFrame searchStack atP atF :=
    ⟨fun a bound => found.kept a (Or.inl (Nat.le_trans (by decide) bound)) (Or.inr bound)⟩
  have callerE : CallerFrame searchStack source atE :=
    callerP.trans (callerF.trans ((CallerFrame.of_memory fcall.memory).trans
      ((CallerFrame.of_memory freedNull.memory).trans (CallerFrame.of_memory tcall.memory))))
  have contentsE : bytesT atE.σ.mem (searchStack + 8#64).toNat 8 =
      vsaReg T.allocation.allocation.allocated 10 := by
    rw [show (searchStack + 8#64).toNat = searchStack.toNat + Layout.off_ext_table_contents from by decide,
      word_observed _ (fun i _ => callerE.byte _ (by omega))]
    exact T.contents_word
  have bounds := readyE.block_bounds (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  obtain ⟨atR, run15, ⟨tableFreed⟩⟩ := (ext_table_free_empty atE _ _ _ _ searchStack _ 0#64 searchStack
    (readyE.perm (List.Perm.swap _ _ _)) (by constructor <;> decide)
    (ExtTableSite.at_sp (by constructor <;> decide) (by decide)) (Nat.le_refl _)
    ⟨gholds_lookup (n := 2) _ tcall.regs (by rfl),
      toE 9 _ (by decide) (by decide) (by decide) found.saved1,
      gholds_lookup (n := 1) _ tcall.regs (by rfl), gholds_lookup (n := 10) _ tcall.regs (by rfl),
      gholds_lookup (n := 11) _ tcall.regs (by rfl), trivial⟩
    (by constructor <;> decide) contentsE bounds.1 bounds.2).run atE ⟨tcall.pc, rfl⟩
  -- the saved slots of caml_search_exe_in_path survive every call
  have base : nativeFrameBase attemptStack 48 = searchStack.toNat := by decide
  have slotWord (off : Nat) (value : BitVec 64)
      (member : (off, value) ∈ searchExeSlots jal_800048ec_call.link trailSlot s1) :
      bytesT atR.σ.mem (nativeFrameBase attemptStack 48 + off) 8 = value := by
    have range : 24 ≤ off ∧ off + 8 ≤ 48 := by
      simp only [searchExeSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      omega
    rw [word_observed (m := atTable.σ.mem) _ (fun i _ => by
      rw [tableFreed.byte (by constructor <;> decide) (by decide) (Nat.le_refl _) bounds.1 bounds.2
          (Or.inl (by rw [base]; omega)),
        callerE.byte _ (by rw [base]; omega),
        T.above (by constructor <;> decide) (by rw [base]; omega)
          (by rw [base]; unfold Layout.ext_table_bytes; omega)]),
      search.memory]
    apply searchFrame.word_log_read
    · intro k v hk
      simp only [searchExeSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
      omega
    · simp [searchExeSlots]
    · exact member
  have copyE : gprGet atE.σ 8 = some found.copy :=
    (tcall.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by decide)).trans
      ((freedNull.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 8) _ fcall.regs (by rfl)))
  obtain ⟨atRet, run16, returned⟩ := (search_exe_return atR attemptStack jal_800048ec_call.link trailSlot
    s1 found.copy _ tableFreed.ready.toLeafInput searchFrame
    ⟨tableFreed.ready.stack, (tableFreed.saved_gpr (k := 8) (by decide) (by decide)).trans copyE, trivial⟩
    (slotWord 40 _ (by simp [searchExeSlots])) (slotWord 32 _ (by simp [searchExeSlots]))
    (slotWord 24 _ (by simp [searchExeSlots])) (by decide)).run atR
    ⟨library_pc tableFreed.freed.free.good tableFreed.freed.free.result.frame.pc, rfl⟩
  have readyRet := tableFreed.ready.stack_log returned (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ returned.regs (by rfl)) (gholds_lookup (n := 1) _ returned.regs (by rfl))
    (by decide) searchFrame (by simp only [LogInW])
  have sameRet : atRet.σ.mem = atR.σ.mem := returned.memory
  have sameE : atE.σ.mem = atF.σ.mem :=
    (show atE.σ.mem = atT.σ.mem from tcall.memory).trans
      ((show atT.σ.mem = atFree.σ.mem from freedNull.memory).trans fcall.memory)
  have frameFree : NativeFrame searchStack (32 + allocHeadroom) := by constructor <;> decide
  -- callee-saved registers from getenv's return to the search's
  have toRet (n : Nat) (lo : 19 ≤ n) (hi : n ≤ 27) (v : BitVec 64) (hv : gprGet atS.σ n = some v) :
      gprGet atRet.σ n = some v := by
    have range : 1 ≤ n ∧ n ≤ 31 := by omega
    have atF' : gprGet atF.σ n = some v := by
      by_cases h19 : n = 19
      · subst h19
        have e : some v = some (vsaReg source 19) :=
          (toP 19 _ (by decide) (by decide) (by decide) hv).symm.trans searchRegs.2.2.2.1
        rw [found.saved3, ← e]
      · rw [found.upper n (by omega) hi]
        exact toP n v range.1 range.2 (by simp; omega) hv
    exact (returned.toEffectPost.gpr_frame (by decide) n range.1 range.2 (by simp; omega)).trans
      ((tableFreed.saved_gpr (k := n) (by simp [abiSaved]; omega) (by omega)).trans
        (toE n v range.1 range.2 (by simp; omega) atF'))
  have vsaSource (k : Nat) (v : BitVec 64) (h : gprGet source.σ k = some v) : vsaReg source k = v :=
    vsaReg_of_gprGet (by unfold VsaIris.PC; intro e; subst e; simp [gprGet] at h) h
  have slotRet : gprGet atRet.σ 19 = some exeNameSlot := by
    have h := carried 19 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ missed.regs (by rfl))
    rw [vsaSource 19 _ slotSource] at h
    exact toRet 19 (by decide) (by decide) _ h
  have flagRet : gprGet atRet.σ 20 = some flag := by
    have h := carried 20 _ (by decide) (by decide) (by decide) (upperD 20 (by decide) (by decide))
    rw [vsaSource 20 _ flagSource] at h
    exact toRet 20 (by decide) (by decide) _ h
  have upperRet (k : Nat) (lo : 21 ≤ k) (hi : k ≤ 27) : gprGet atRet.σ k = gprGet c.σ k := by
    have atC := gpr_of_ready ready k (by omega) (by omega)
    have h := carried k _ (by omega) (by omega) (by simp; omega) (upperD k (by omega) hi)
    rw [vsaSource k _ (upperSource k lo hi _ atC)] at h
    rw [atC]
    exact toRet k (by omega) hi _ h
  have callerA : CallerFrame attemptStack atSaved atRet := by
    constructor
    intro a bound
    have above : searchStack.toNat + 48 ≤ a := by
      have : searchStack.toNat + 48 = attemptStack.toNat := by decide
      omega
    rw [sameRet, tableFreed.byte (by constructor <;> decide) (by decide) (Nat.le_refl _) bounds.1 bounds.2
        (Or.inl (by omega)),
      callerE.byte _ (by omega),
      T.above (by constructor <;> decide) (by omega) (by unfold Layout.ext_table_bytes; omega),
      search.memory, frameOn_writeLog _ _ _ (searchExeLog_inside searchFrame) a ⟨Or.inr bound, trivial⟩,
      nameCall.memory]
    rfl
  have liveRet (e : Nat × Nat) (he : e ∈ H) (x : Nat) (inside : InExt e x) :
      (atRet.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    obtain ⟨q, m⟩ := e
    have bounds := ready.block_bounds (q := q) (n := m) he
    unfold InExt at inside
    have hx : heapStart ≤ x ∧ x < heapEnd := ⟨by omega, by omega⟩
    have low (b : Nat) (hb : heapEnd ≤ b) : x < b := by omega
    obtain ⟨-, -, -, tableApart⟩ := T.allocation.allocation.allocation.allocation.result.fresh.destruct
    have apartT : ¬ InExt ((vsaReg T.allocation.allocation.allocated 10).toNat, (extTableRequest 8#64).toNat) x :=
      fun inT => tableApart _ he x inT inside
    rw [sameRet, tableFreed.live_byte frameFree (Nat.le_refl _) (List.mem_cons_of_mem _ he) inside apartT hx, sameE,
      found.kept x (Or.inr (Or.inr (Or.inr ⟨q, m, List.mem_cons_of_mem _ he, bounds.1, bounds.2, inside.1,
        inside.2⟩))) (Or.inl (low _ (by decide))),
      show atP.σ.mem = atS.σ.mem from scall.memory, dnull.memory,
      frameOn_writeLog _ _ _ (decomposeLog_inside frame32) x ⟨Or.inl (low _ (by decide)), trivial⟩,
      show atDec.σ.mem = atD.σ.mem from dcall.memory, missed.memory,
      frameOn_writeLog _ _ _ (getenvMissLog_inside frame112) x ⟨Or.inl (low _ (by decide)), trivial⟩, same,
      T.live_byte tableFrame (Nat.le_refl _) he inside bounds, search.memory,
      frameOn_writeLog _ _ _ (searchExeLog_inside searchFrame) x ⟨Or.inl (low _ (by decide)), trivial⟩,
      show atSearch.σ.mem = atSaved.σ.mem from nameCall.memory, save.memory,
      frameOn_writeLog _ _ _ (attemptOpenLog_inside attemptFrame) x ⟨Or.inl (low _ (by decide)), trivial⟩]
  have keptRet : EmbedFrame atP atRet := by
    have strdup : EmbedFrame atP atF :=
      ⟨fun a ha => found.kept a (ha.strdup_kept (by decide))
        (Or.inl (by
          have := ha.lt
          have limit : embedLimit < nativeFrameBase searchStack 176 := by decide
          omega))⟩
    exact strdup.trans ((EmbedFrame.of_memory sameE).trans ((tableFreed.embed_frame frameFree
      (by decide) (Nat.le_refl _) bounds.1 bounds.2).trans (EmbedFrame.of_memory sameRet)))
  refine ⟨atRet, run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans (run9.trans
    (run10.trans (run11.trans (run12.trans (run13.trans (run14.trans (run15.trans run16))))))))))))), ⟨{
      copy := found.copy
      result := gholds_lookup (n := 10) _ returned.regs (by rfl)
      pc := returned.pc
      stack := gholds_lookup (n := 2) _ returned.regs (by rfl)
      trail := gholds_lookup (n := 8) _ returned.regs (by rfl)
      slot := slotRet
      flagReg := flagRet
      upper := upperRet
      ready := readyRet
      fresh := found.fresh
      aligned := found.aligned
      disjoint := fun e he => found.disjoint e (List.mem_cons_of_mem _ he)
      bytes := fun k hk => by
        have inside : InExt (found.copy.toNat, len + 1) (found.copy.toNat + k) := ⟨by omega, by omega⟩
        rw [sameRet, tableFreed.live_byte frameFree (Nat.le_refl _) (List.mem_cons_self ..) inside
          (found.disjoint _ (List.mem_cons_self ..) _ inside) ⟨by have := found.fresh.1; omega,
            by have := found.fresh.2; omega⟩, sameE, found.bytes k hk]
        exact lateP.embed.byte _ (embedded k hk)
      slots := fun off value member => by
        have base64 : nativeFrameBase parameterStack 64 = attemptStack.toNat := by decide
        rw [word_observed (m := atSaved.σ.mem) _ (fun i _ => callerA.byte _ (by rw [base64] at *; omega)),
          save.memory]
        apply attemptFrame.word_log_read
        · intro k v hk
          simp only [attemptOpenSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
          omega
        · simp [attemptOpenSlots]
        · exact member
      caller := aboveSaved.trans (callerA.mono (by decide))
      live := ⟨liveRet⟩
      kept := keptSource.trans (keptP.trans keptRet)
      late := lateP.frame keptRet
      run := run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans (run9.trans
        (run10.trans (run11.trans (run12.trans (run13.trans (run14.trans (run15.trans run16))))))))))))) }⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
