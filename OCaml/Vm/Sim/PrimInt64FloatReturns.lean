import OCaml.Vm.Sim.CcallAllocation
import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Gc.G1Guards

/-! `caml_int64_float_of_bits` at a C_CALL callee entry: the boxed double is
reserved below `young_ptr` (`ccall_allocation_entry`), the fast path's
memory facts come from the reserved block, and its exact log is the
reservation followed by the header and the bits. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.DoubleAllocation

theorem outLRange_left {left right : List WEntry} {a n : Nat} (h : OutLRange (left ++ right) a n) :
    OutLRange left a n := by
  induction left with
  | nil => trivial
  | cons e left ih => exact ⟨h.1, ih h.2⟩

theorem outLRange_right {left right : List WEntry} {a n : Nat} (h : OutLRange (left ++ right) a n) :
    OutLRange right a n := by
  induction left with
  | nil => exact h
  | cons e left ih => exact ih h.2

theorem ImageOutside.left {l1 l2 : List WEntry} (h : ImageOutside (l1 ++ l2)) : ImageOutside l1 :=
  ⟨outLRange_left h.text, outLRange_left h.rodata⟩

theorem ImageOutside.right {l1 l2 : List WEntry} (h : ImageOutside (l1 ++ l2)) : ImageOutside l2 :=
  ⟨outLRange_right h.text, outLRange_right h.rodata⟩

theorem RamWriteAt.window {x w : Nat} (h : RamWriteAt x w) : WriteWindow (BitVec.ofNat 64 x) w := by
  have e : (BitVec.ofNat 64 x).toNat = x := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; have := h.upper; omega
  have ht := h.htif
  simp only [tohostAddr, LibraryLayout.tohostAddr] at ht
  exact ⟨by rw [e]; exact h.lower, by rw [e]; exact h.upper, by rw [e]; exact ht, by rw [e]; exact h.aligned⟩

/-- The double's two stores at the block `a`. -/
def doubleBlock (bits : BitVec 64) (a : Nat) : List WEntry :=
  initializeLog (BitVec.ofNat 64 (a - 8)) (BitVec.ofNat 64 (a - 8)) bits

theorem ofNat_sub {x k : Nat} (hk : k ≤ x) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp; omega

/-- **`caml_int64_float_of_bits` at the callee entry.** -/
theorem int64_float_entry {ra : BitVec 64} {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high domain : Nat} {env : BitVec 64} {l : Nat} {bits : BitVec 64}
    {c : Config} (allocFrame : AllocFrame L)
    (accu : s.accu = .ptr l 0) (object : s.heap.get? l = some (.int64 bits))
    (budget : (s.heap.alloc (.double bits)).1.words ≤ L.budget.heapWords)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes)
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain Layout.sym_caml_int64_float_of_bits env c)
    (placed : pl.φ (s.heap.alloc (.double bits)).2 =
      some ((BitVec.ofNat 64 (runtimeFields c).youngPtr - 16#64).toNat + 8)) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_int64_float_of_bits) (fun x => x = c)
      (CcallReturn ra L P { s with pc := s.pc + 2, accu := Val.ptr (s.heap.alloc (.double bits)).2 0, heap := (s.heap.alloc (.double bits)).1, world := s.world }
        pl cp sp high (BitVec.ofNat 64 domain) (BitVec.ofNat 64 (sp - 16))
        (BitVec.ofNat 64 ((BitVec.ofNat 64 (runtimeFields c).youngPtr - 16#64).toNat + 8)) env) := by
  have ng := setup.geometry.nursery
  have wos : (Obj.double bits).wosize = 1 := rfl
  have y16 : 16 ≤ (runtimeFields c).youngPtr := by
    have h1 := ng.statics; have h2 := setup.geometry.room.nursery
    simp only [Gc.nurseryFree] at h1; simp only [Layout.sym_bss_end] at h1; omega
  have eplace : (BitVec.ofNat 64 (runtimeFields c).youngPtr - 16#64).toNat + 8 =
      (runtimeFields c).youngPtr - 8 * (Obj.double bits).wosize := by
    rw [wos, ofNat_sub (k := 16) (by omega) (by have := ng.top; omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := ng.top; omega)]
    omega
  have placed' : pl.φ (s.heap.alloc (.double bits)).2 =
      some ((runtimeFields c).youngPtr - 8 * (Obj.double bits).wosize) := by rw [placed, eplace]
  rw [eplace]
  -- the argument
  have live : Live s.heap (roots P s) l := Live.root (v := .ptr l 0) (by simp [roots, accu]) rfl
  obtain ⟨a', o', argPlaced, argObject, -⟩ := setup.input.data.heap.1 l live
  have oo : o' = .int64 bits := Option.some.inj (argObject.symm.trans object)
  subst oo
  have g := setup.geometry
  have argLow := g.heapLow l a' _ argPlaced object
  have argHigh := g.heapArena l a' _ argPlaced object
  have argWos : (Obj.int64 bits).wosize = 2 := rfl
  rw [argWos] at argHigh
  have he : Vsa.Sim.DlHeap.heapEnd ≤ 0x100000000 := by decide
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have ht : 0x80000000 ≤ Layout.sym_tohost := by decide
  have insideOf : ∀ a, ReservedBlock c a (Obj.double bits).wosize →
      LogInW [⟨a - 8, a + 8 * (Obj.double bits).wosize⟩] (doubleBlock bits a) := by
    intro a b
    have := b.top; have := b.room
    rw [wos] at *
    have e1 : (BitVec.ofNat 64 (a - 8)).toNat = a - 8 := by rw [BitVec.toNat_ofNat]; omega
    have e2 : (BitVec.ofNat 64 (a - 8) + 8#64).toNat = a := by
      rw [BitVec.toNat_add, e1]; simp; omega
    exact ⟨Or.inl ⟨by simp only [e1]; omega, by simp only [e1]; omega⟩,
      Or.inl ⟨by simp only [e2]; omega, by simp only [e2]; omega⟩, trivial⟩
  refine ccall_allocation_entry (writes := doubleWrites) (name := "caml_int64_float_of_bits") allocFrame budget
    stackFits (fun _ _ h => by cases h) (by decide) (fun a => doubleBlock bits a) insideOf
    (fun a input b runtime => ?_) setup placed'
  -- the generated contract at the reservation `a`
  have b1 := b
  rw [wos] at b1
  have top := b1.top; have room := b1.room; have al := b1.aligned
  have ngc := ng
  obtain ⟨D, hD⟩ : ∃ D, word c Layout.sym_Caml_state = D := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : BitVec 64, BitVec.ofNat 64 (a + 8) = Y := ⟨_, rfl⟩
  obtain ⟨Lm, hLm⟩ : ∃ Lm, word c (limitSlot D).toNat = Lm := ⟨_, rfl⟩
  have dh := ng.domainHigh
  have dl := ng.domainLow
  rw [hD] at dh dl
  have eslot : (youngSlot D).toNat = D.toNat + Layout.off_young_ptr := by
    simp only [youngSlot, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Layout.off_young_ptr, Layout.domainStateBytes] at *; omega
  have elimit : (limitSlot D).toNat = D.toNat + Layout.off_young_limit := by
    simp only [limitSlot, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Layout.off_young_limit, Layout.domainStateBytes] at *; omega
  have slotBV : youngSlot D = BitVec.ofNat 64 (D.toNat + Layout.off_young_ptr) := by
    apply BitVec.eq_of_toNat_eq; rw [eslot, BitVec.toNat_ofNat]
    simp only [Layout.off_young_ptr, Layout.domainStateBytes] at *; omega
  have limitBV : limitSlot D = BitVec.ofNat 64 (D.toNat + Layout.off_young_limit) := by
    apply BitVec.eq_of_toNat_eq; rw [elimit, BitVec.toNat_ofNat]
    simp only [Layout.off_young_limit, Layout.domainStateBytes] at *; omega
  have eY16 : Y - 16#64 = BitVec.ofNat 64 (a - 8) := by rw [← hY]; exact ofNat_sub (k := 16) (by omega) (by omega)
  have eY8 : Y - 16#64 + 8#64 = BitVec.ofNat 64 a := by
    rw [eY16]; apply BitVec.eq_of_toNat_eq; simp; omega
  have ea : (Y - 16#64).toNat + 8 = a := by rw [eY16, BitVec.toNat_ofNat]; omega
  have elog : allocationLog D Y bits = allocLog c a (doubleBlock bits a) := by
    simp only [allocationLog, reserveLog, allocLog, grabReserveLog, doubleBlock, eslot, eY16, hD, List.cons_append,
      List.nil_append]
  have yw : (word c (D.toNat + Layout.off_young_ptr)).toNat = a + 8 := by
    have := b1.young; simp only [runtimeFields, domainWord, hD] at this; omega
  have youngValue : word c (youngSlot D).toNat = Y := by
    rw [eslot, ← hY]; apply BitVec.eq_of_toNat_eq; rw [yw, BitVec.toNat_ofNat]; omega
  have domainValue : word c domainGlobal.toNat = D := by
    simp only [domainGlobal, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by decide), hD]
  have pay := input.payloadOutside.domain
  simp only [allocLog, hD] at pay
  have free := b1.free (insideOf a b)
  have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  have dApart := b.domainApart ng
  rw [wos, hD] at dApart
  have fast : FastMemory bits D Y Lm c :=
    { domainValue, youngValue, limitValue := hLm
      youngWrite := by rw [slotBV, ← hD]; exact RamWriteAt.window ng.young_write
      limitRead := by rw [limitBV, ← hD]; exact RamReadAt.window ng.limit_read
      headerWrite := by rw [eY16]; exact RamWriteAt.window (b1.write (x := a - 8) (by omega) (by omega) (by omega))
      dataWrite := by rw [eY8]; exact RamWriteAt.window (b1.write (x := a) (by omega) (by omega) (by omega))
      room := Gc.G1Room.double_room setup.geometry.room domainValue youngValue hLm
        (by simp only [Layout.off_young_ptr, Layout.domainStateBytes] at *; omega)
        (by rw [Heap.words_alloc] at budget; rw [wos] at budget; omega)
      reserveImage := by
        have := (setup.geometry.toStackGeometry.young_image (a := a))
        simpa only [reserveLog, grabReserveLog, eslot, eY16, hD] using this
      initializeImage := by
        have := ng.toWindowSeparated.image free
        simpa only [doubleBlock, eY16] using this
      globalOutsideReserve := by
        have := outLRange_left pay
        simpa only [reserveLog, grabReserveLog, eslot, eY16, domainGlobal, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show Layout.sym_Caml_state < 2 ^ 64 by decide)] using this
      globalOutsideHeader := by
        have := outLRange_left (left := headerLog _) (outLRange_right pay)
        simpa only [doubleBlock, initializeLog, eY16, domainGlobal, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show Layout.sym_Caml_state < 2 ^ 64 by decide)] using this
      youngOutsideHeader := by
        rw [eY16, eslot]
        simp only [headerLog, OutLRange, BitVec.toNat_ofNat, and_true]
        simp only [Layout.off_young_ptr, Layout.domainStateBytes] at *
        omega }
  have input' : AllocationInput L.runtimeOk P s pl cp sp high ra [.ptr l 0] (.double bits)
      ((Y - 16#64).toNat + 8) (allocationLog D Y bits) c := by
    rw [ea, elog, ← accu]; exact input
  have h : Int64FloatInput L.runtimeOk P s pl cp sp high ra l a' bits D Y Lm c :=
    { input' with
      accu, argumentPlace := argPlaced, argumentObject := object
      argumentBound := by omega
      argumentRead := RamReadAt.window ⟨by omega, by omega, Or.inr (by omega)⟩
      nursery := fast }
  have S := int64_float_contract h (by rw [elog]; exact runtime)
  rw [ea, elog] at S
  rw [accu]
  exact S

/-- The model's `caml_int64_float_of_bits`: a boxed int64 argument, a fresh double. -/
theorem int64_float_semantics {s : St} {v : Val} {heap : Heap} {world : World}
    (sem : primF1Impl "caml_int64_float_of_bits" [s.accu] s.heap s.world = .ok v heap world) :
    ∃ l bits, s.accu = .ptr l 0 ∧ s.heap.get? l = some (.int64 bits) ∧
      v = .ptr (s.heap.alloc (.double bits)).2 0 ∧ heap = (s.heap.alloc (.double bits)).1 ∧ world = s.world := by
  match hx : s.accu with
  | .ptr l 0 =>
    rw [hx] at sem
    cases ho : s.heap.get? l with
    | none => simp [primF1Impl, ho] at sem
    | some o =>
      cases o with
      | int64 bits =>
        simp only [primF1Impl, ho] at sem
        obtain ⟨rfl, rfl, rfl⟩ := sem
        exact ⟨l, bits, rfl, ho, rfl, rfl, rfl⟩
      | _ => simp [primF1Impl, ho] at sem
  | .ptr _ (_ + 1) => rw [hx] at sem; simp [primF1Impl] at sem
  | .int _ | .code _ | .atom _ | .raw _ => rw [hx] at sem; simp [primF1Impl] at sem

/-- **`caml_int64_float_of_bits` at every `C_CALL` site.** -/
theorem prim_caml_int64_float_of_bits_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (allocFrame : AllocFrame L) :
    PrimReturnsAt L P op ra k "caml_int64_float_of_bits" := by
  intro s c0 pl cp sp high table entry value env index v heap world _reach ready sem words
  have nil : s.stack.take k = [] := by
    cases e : s.stack.take k with
    | nil => rfl
    | cons _ _ => rw [e] at sem; simp [primF1Impl] at sem
  rw [nil] at sem ⊢
  have model := sem
  obtain ⟨l, bits, accu, object, rfl, rfl, rfl⟩ := int64_float_semantics sem
  have hentry : entry = Layout.sym_caml_int64_float_of_bits :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_int64_float_of_bits)
  subst hentry
  have places : ∀ young : BitVec 64, allocPlaces "caml_int64_float_of_bits" s young =
      [((s.heap.alloc (.double bits)).2, (young - 16#64).toNat + 8)] := by
    intro young; simp [allocPlaces, accu, object]
  have head := ready.allocPlaced _ (by rw [places]; exact List.mem_singleton_self _)
  refine ⟨BitVec.ofNat 64 ((BitVec.ofNat 64 (runtimeFields c0).youngPtr - 16#64).toNat + 8),
    ⟨by decide, model, fun c setup placedAt => ?_⟩⟩
  have here := placedAt _ (by rw [places]; exact List.mem_singleton_self _)
  have same := Option.some.inj (here.symm.trans head)
  dsimp only at same
  rw [← same]
  exact int64_float_entry allocFrame accu object words ready.stackFits setup here

end OCaml.Vm.Sim
