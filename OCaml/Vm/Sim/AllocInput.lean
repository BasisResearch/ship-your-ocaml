import OCaml.Vm.Sim.PlacePut
import OCaml.Vm.Gc.NurseryGeometry
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Sim.ClosureLayout
import OCaml.Vm.Sim.NurseryInput
import OCaml.Vm.Sim.MakeblockInput
import OCaml.Vm.Sim.ApplyRows

/-!
# Allocation logs at the loop head

An allocating arm's log is the young-pointer store (`grabReserveLog`) followed
by stores into the reserved nursery block. The store sits inside the
`Caml_state` record, which the stack geometry keeps apart from everything the
payload observes; the block lies in the free nursery (`NurseryGeometry`).
Certificates of the two parts combine (`PayloadOutside.append`, …).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-! ## Certificates of an appended log -/

theorem objectOutside_append {l1 l2 : List WEntry} {a : Nat} {o : Obj}
    (h1 : ObjectOutside l1 a o) (h2 : ObjectOutside l2 a o) : ObjectOutside (l1 ++ l2) a o :=
  ⟨outLRange_append h1.header h2.header, outLRange_append h1.payload h2.payload⟩

theorem _root_.OCaml.Vm.Primitives.PayloadOutside.append {l1 l2 : List WEntry} {P : Prog} {s : St}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp : Nat}
    (h1 : PayloadOutside l1 P s c pl cp sp) (h2 : PayloadOutside l2 P s c pl cp sp) :
    PayloadOutside (l1 ++ l2) P s c pl cp sp :=
  ⟨outLRange_append h1.domain h2.domain, outLRange_append h1.stackHigh h2.stackHigh,
   outLRange_append h1.trapsp h2.trapsp, outLRange_append h1.codeBase h2.codeBase,
   outLRange_append h1.atomBase h2.atomBase, outLRange_append h1.globals h2.globals,
   fun i w hw => outLRange_append (h1.code i w hw) (h2.code i w hw),
   fun i v hv => outLRange_append (h1.stack i v hv) (h2.stack i v hv),
   fun l a o live placed object => objectOutside_append (h1.heap l a o live placed object)
     (h2.heap l a o live placed object),
   fun id ch a hch hcp => outLRange_append (h1.channels id ch a hch hcp) (h2.channels id ch a hch hcp)⟩

theorem _root_.OCaml.Vm.Primitives.ImageOutside.append {l1 l2 : List WEntry}
    (h1 : ImageOutside l1) (h2 : ImageOutside l2) : ImageOutside (l1 ++ l2) :=
  ⟨outLRange_append h1.text h2.text, outLRange_append h1.rodata h2.rodata⟩

theorem _root_.OCaml.Vm.Primitives.BindingsOutside.append {l1 l2 : List WEntry} {P : Prog} {c : Config}
    (h1 : BindingsOutside l1 P c) (h2 : BindingsOutside l2 P c) : BindingsOutside (l1 ++ l2) P c :=
  ⟨outLRange_append h1.contents h2.contents,
   fun i name hi => outLRange_append (h1.entries i name hi) (h2.entries i name hi)⟩

/-! ## The young-pointer store -/

/-- The young-pointer store misses a range apart from its word. -/
theorem grab_out {domain a x n : Nat}
    (h : x + n ≤ domain + Layout.off_young_ptr ∨ domain + Layout.off_young_ptr + 8 ≤ x) :
    OutLRange (grabReserveLog domain a) x n := ⟨h, trivial⟩

/-- A range apart from the whole `Caml_state` record misses its young-pointer word. -/
theorem young_apart {c : Config} {x n : Nat} {v : BitVec 64}
    (apart : OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
      (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] x n) :
    OutLRange [((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr, 8, v)] x n := by
  obtain ⟨h, -⟩ := apart
  have : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  exact ⟨by dsimp only at h ⊢; omega, trivial⟩

/-- **The young-pointer store misses the represented payload.** -/
theorem StackGeometry.young_payload {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high a : Nat} (g : StackGeometry P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (space : high - Layout.stackBytes ≤ sp) :
    PayloadOutside (grabReserveLog (word c Layout.sym_Caml_state).toNat a) P s c pl cp sp := by
  have hs := stack.1
  have hl := g.domainLow
  have hd := g.domain.1
  simp only [stackWindow] at hd
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have static : ∀ x, x + 8 ≤ Layout.sym_bss_end →
      OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a) x 8 := fun x hx =>
    grab_out (by simp only [Layout.off_young_ptr]; omega)
  have field : ∀ off, off + 8 ≤ Layout.off_young_ptr ∨ Layout.off_young_ptr + 8 ≤ off →
      OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a)
        ((word c Layout.sym_Caml_state).toNat + off) 8 := fun off h =>
    grab_out (by omega)
  refine ⟨static _ (by decide), field _ (by decide), field _ (by decide), static _ (by decide),
    static _ (by decide), static _ (by decide), ?_, ?_, ?_, ?_⟩
  · intro i w hw
    obtain ⟨hc, -⟩ := g.domainCode
    have bound : i < P.code.size := (Array.getElem?_eq_some_iff.mp hw).1
    have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
    dsimp only at hc
    exact grab_out (by omega)
  · intro i v hv
    have bound : i < s.stack.length := (List.getElem?_eq_some_iff.1 hv).1
    have : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
    exact grab_out (by omega)
  · intro l b o _ placed object
    have apart := g.domainHeap l b o placed object
    exact ⟨young_apart (Gc.outW_sub apart (by omega) (by omega)), young_apart (Gc.outW_sub apart (by omega) (by omega))⟩
  · exact fun id ch b hch hcp => young_apart (g.domainChannels id ch b hch hcp)

/-- The young-pointer store misses the executable image. -/
theorem StackGeometry.young_image {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high a : Nat} (g : StackGeometry P s c pl cp high) :
    ImageOutside (grabReserveLog (word c Layout.sym_Caml_state).toNat a) := by
  have hl := g.domainLow
  have t : Image.textBase + Image.textSize ≤ Layout.sym_bss_end := by decide
  have r : Image.rodataBase + Image.rodataSize ≤ Layout.sym_bss_end := by decide
  exact ⟨grab_out (by omega), grab_out (by omega)⟩

/-- The young-pointer store misses the primitive bindings. -/
theorem StackGeometry.young_bindings {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high a : Nat} (g : StackGeometry P s c pl cp high) :
    BindingsOutside (grabReserveLog (word c Layout.sym_Caml_state).toNat a) P c := by
  have hl := g.domainLow
  have t : Layout.sym_caml_prim_table + Layout.off_prim_contents + 8 ≤ Layout.sym_bss_end := by decide
  exact ⟨grab_out (by omega), fun i name hi => young_apart (g.domainPrims i name hi)⟩

/-! ## The reserved block -/

/-- The free nursery holds the reserved block `[a - 8, a + 8 * count)`. -/
theorem block_in_free {c : Config} {a count : Nat} {log : List WEntry}
    (young : (runtimeFields c).youngPtr = a + 8 * count) (capacity : (runtimeFields c).youngLimit ≤ a - 8)
    (inside : LogInW [⟨a - 8, a + 8 * count⟩] log) : LogInW [Gc.nurseryFree c] log :=
  logInW_widen inside fun w hw => by
    simp only [List.mem_singleton] at hw
    subst hw
    simp only [Gc.nurseryFree]
    omega

/-- A reserved object misses every placed object. -/
theorem _root_.OCaml.Vm.Gc.NurseryGeometry.allocationOutside {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high a count : Nat} {o : Obj} (g : Gc.NurseryGeometry P s c pl cp high)
    (young : (runtimeFields c).youngPtr = a + 8 * count) (capacity : (runtimeFields c).youngLimit ≤ a - 8)
    (room : 8 ≤ a) (size : o.wosize ≤ count) : AllocationOutside P s pl a o := by
  intro l b old _ placed object
  have apart := Gc.apart_of_inside (g.heap l b old placed object) capacity
    (y := a - 8) (k := 8 * o.wosize + 8) (by omega)
  omega

/-- **The reservation of `count` words below `young_ptr`**: the nursery's
scalar observations at the loop head. -/
structure Reservation (L : OCaml.Layout) (s : St) (c : Config) (count : Nat) : Prop where
  room : Gc.G1Room L.budget s c
  fits : s.heap.words + (count + 1) ≤ L.budget.heapWords

theorem Reservation.capacity {L : OCaml.Layout} {s : St} {c : Config} {count : Nat}
    (r : Reservation L s c count) :
    (runtimeFields c).youngLimit + 8 * (count + 1) ≤ (runtimeFields c).youngPtr := by
  have := r.room.nursery
  have := r.fits
  omega

theorem logInW_append' {ws : List W} {l1 l2 : List WEntry} (h1 : LogInW ws l1) (h2 : LogInW ws l2) :
    LogInW ws (l1 ++ l2) := by
  induction l1 with
  | nil => exact h2
  | cons e l ih => exact ⟨h1.1, ih h1.2⟩

/-- A block log lies in its reserved block. -/
theorem blockLog_in {a tag : Nat} {words : List (BitVec 64)} (room : 8 ≤ a) (nonempty : 0 < words.length) :
    LogInW [⟨a - 8, a + 8 * words.length⟩] (blockLog a tag words) :=
  ⟨Or.inl ⟨Nat.le_refl _, by dsimp only; omega⟩, logInW_widen (value_log_in a words) fun w hw => by
    simp only [List.mem_singleton] at hw
    subst hw
    dsimp only
    omega⟩

theorem makeblockWords_length {c : Config} {sp count : Nat} {accu : BitVec 64} (positive : 0 < count) :
    (makeblockWords c sp count accu).length = count := by
  simp [makeblockWords, stackWords]
  omega

theorem makeblockObject_wosize {s : St} {count tag : Nat} (positive : 0 < count)
    (bound : count - 1 ≤ s.stack.length) : (makeblockObject s count tag).wosize = count := by
  simp [makeblockObject, Obj.wosize]
  omega

/-- **MAKEBLOCK's input at the loop head**, the fresh location placed at
`young_ptr - 8 * count`. -/
theorem MakeblockInput.of_input {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high count tag : Nat} {accu : BitVec 64}
    (h : ArmInput L P s op c pl cp sp high)
    (placed : pl.φ (s.heap.alloc (makeblockObject s count tag)).2 =
      some ((runtimeFields c).youngPtr - 8 * count))
    (reserve : Reservation L s c count)
    (positive : 0 < count) (bound : count - 1 ≤ s.stack.length) (small : count < 2^31) (tagBound : tag < 256)
    (value : valWord pl s.accu = some accu) (space : 8 * s.stack.length ≤ Layout.stackBytes) :
    MakeblockInput P s c pl cp sp high count tag ((runtimeFields c).youngPtr - 8 * count)
      (word c Layout.sym_Caml_state).toNat (runtimeFields c).youngLimit accu := by
  have g := h.geometry.nursery
  have capacityAll := reserve.capacity
  have aligned := g.aligned
  have top := g.top
  have statics := g.statics
  simp only [Gc.nurseryFree] at statics
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have hr : 0x80000000 ≤ Layout.sym_tohost := by decide
  have hs := h.stack.1
  have spSpace := stack_space h.stack space
  have young : (runtimeFields c).youngPtr = ((runtimeFields c).youngPtr - 8 * count) + 8 * count := by omega
  generalize ha : (runtimeFields c).youngPtr - 8 * count = a at placed young ⊢
  have capacity : (runtimeFields c).youngLimit ≤ a - 8 := by omega
  have room : 8 ≤ a := by omega
  have size := makeblockObject_wosize (tag := tag) positive bound
  have wordsLen := makeblockWords_length (c := c) (sp := sp) (accu := accu) positive
  have blockInside : LogInW [⟨a - 8, a + 8 * count⟩] (blockLog a tag (makeblockWords c sp count accu)) := by
    simpa only [wordsLen] using blockLog_in (tag := tag) (words := makeblockWords c sp count accu) room
      (by omega)
  have free := block_in_free young capacity blockInside
  have domFree := g.domain
  have apartDomain : a + 8 * count ≤ (word c Layout.sym_Caml_state).toNat ∨ ((word c Layout.sym_Caml_state).toNat) + Layout.domainStateBytes ≤ a - 8 := by
    have := Gc.apart_of_inside domFree capacity (y := a - 8) (k := 8 * count + 8) (by omega)
    omega
  have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  have hl : Layout.off_young_limit + 8 ≤ Layout.domainStateBytes := by decide
  -- the block part misses the domain record's words
  have blockMiss : ∀ off, off + 8 ≤ Layout.domainStateBytes →
      OutLRange (blockLog a tag (makeblockWords c sp count accu)) ((word c Layout.sym_Caml_state).toNat + off) 8 := fun off hoff =>
    outLRange_of_windows blockInside ⟨by dsimp only; omega, trivial⟩
  have domainArena := h.geometry.domainArena
  have arenaEnd := g.arena
  have youngWord : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr)).toNat = a + 8 * count := by
    rw [← young]; rfl
  have limitWord : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit)).toNat = (runtimeFields c).youngLimit := rfl
  refine
    { positive, bound, small := by omega, tagBound, room, placed
      separate := g.allocationOutside young capacity room (by omega)
      payload := (h.geometry.young_payload h.stack spSpace).append
        (g.toWindowSeparated.payload h.stack spSpace free)
      image := h.geometry.young_image.append (g.toWindowSeparated.image free)
      bindings := h.geometry.young_bindings.append (g.toWindowSeparated.bindings free)
      reserve := ?_
      arena := ?_
      domainValue := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      youngValue := by rw [← youngWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      limitValue := by rw [← limitWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      youngWrite := g.young_write
      limitRead := g.limit_read
      headerWrite := g.header_write young capacity room
      fieldWrites := fun i hi => ⟨by omega, by omega, by simp only [tohostAddr, ← mailbox_layout] at *; omega,
        by omega⟩
      reads := fun i hi => h.geometry.read h.stack spSpace (by omega)
      capacity
      headerYoungOutside := ⟨by dsimp only; omega, trivial⟩ }
  · refine ⟨by rw [size]; exact young, by rw [size]; exact Nat.le_refl _, room, by omega, capacity, fun c' memory => ?_⟩
    have pay := (h.geometry.young_payload (a := a) h.stack spSpace).append
      (g.toWindowSeparated.payload h.stack spSpace free)
    have keep : ∀ x, OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a ++ blockLog a tag (makeblockWords c sp count accu)) x 8 →
        word c' x = word c x := fun x hx => by
      change bytesT c'.σ.mem x 8 = bytesT c.σ.mem x 8
      rw [memory, makeblockLog, bytesT_writeLog_out _ hx]
    have domainKeep := keep _ pay.domain
    have youngNew : word c' ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr) = BitVec.ofNat 64 (a - 8) := by
      change bytesT c'.σ.mem _ 8 = _
      rw [memory, makeblockLog]
      exact Gc.word_writeLog_at _ _ 0 _ _ (by simp [grabReserveLog])
        (by simpa [grabReserveLog] using blockMiss _ hy)
    have limitOut : OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a) ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit) 8 :=
      grab_out (by simp only [Layout.off_young_limit, Layout.off_young_ptr]; omega)
    have limitKeep := keep _ (outLRange_append limitOut (blockMiss _ hl))
    refine ⟨?_, ?_⟩
    · simp only [runtimeFields, domainWord, domainKeep, youngNew, BitVec.toNat_ofNat]
      omega
    · simp only [runtimeFields, domainWord, domainKeep, limitKeep]
  · exact logInW_append' ⟨Or.inl ⟨by simp only [arenaWindow]; omega, by simp only [arenaWindow]; omega⟩, trivial⟩
      (logInW_widen blockInside fun w hw => by
        simp only [List.mem_singleton] at hw; subst hw; simp only [arenaWindow]; omega)

/-! ## The reserved block at a loop head -/

/-- **A block of `n` words (header excluded) reserved below `young_ptr`**: the
scalar facts every allocating arm consumes. -/
structure ReservedBlock (c : Config) (a n : Nat) : Prop where
  young : (runtimeFields c).youngPtr = a + 8 * n
  capacity : (runtimeFields c).youngLimit ≤ a - 8
  room : 8 ≤ a
  aligned : a % 8 = 0
  top : a + 8 * n ≤ 0x100000000
  statics : Layout.sym_bss_end ≤ a - 8

/-- The reserved block below `young_ptr` at a loop head. -/
theorem ReservedBlock.of_reservation {L : OCaml.Layout} {P : Prog} {s : St} {c : Config} {pl : Place}
    {cp : ChanPlace} {high n : Nat} (g : Gc.NurseryGeometry P s c pl cp high) (reserve : Reservation L s c n) :
    ReservedBlock c ((runtimeFields c).youngPtr - 8 * n) n := by
  have capacityAll := reserve.capacity
  have aligned := g.aligned
  have top := g.top
  have statics := g.statics
  simp only [Gc.nurseryFree] at statics
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Every aligned word of a reserved block is writable RAM. -/
theorem ReservedBlock.write {c : Config} {a n x : Nat} (b : ReservedBlock c a n)
    (low : a - 8 ≤ x) (high : x + 8 ≤ a + 8 * n) (aligned : x % 8 = 0) : RamWriteAt x 8 := by
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have hr : 0x80000000 ≤ Layout.sym_tohost := by decide
  have := b.statics
  have := b.top
  exact ⟨by omega, by omega, by simp only [tohostAddr, ← mailbox_layout] at *; omega, by omega⟩

/-- A log inside the reserved block lies in the free nursery. -/
theorem ReservedBlock.free {c : Config} {a n : Nat} {log : List WEntry} (b : ReservedBlock c a n)
    (inside : LogInW [⟨a - 8, a + 8 * n⟩] log) : LogInW [Gc.nurseryFree c] log :=
  block_in_free b.young b.capacity inside

/-- The reserved block misses the `Caml_state` record. -/
theorem ReservedBlock.domainApart {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high a n : Nat} (b : ReservedBlock c a n) (g : Gc.NurseryGeometry P s c pl cp high) :
    a + 8 * n ≤ (word c Layout.sym_Caml_state).toNat ∨
      (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes ≤ a - 8 := by
  have := Gc.apart_of_inside g.domain b.capacity (y := a - 8) (k := 8 * n + 8)
    (by have := b.young; have := b.room; omega)
  have := b.room
  omega

/-- The reserved block misses the VM stack allocation. -/
theorem ReservedBlock.stackApart {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high a n : Nat} (b : ReservedBlock c a n) (g : Gc.NurseryGeometry P s c pl cp high) :
    a + 8 * n ≤ high - Layout.stackBytes ∨ high ≤ a - 8 := by
  have apart := Gc.apart_of_inside g.stack b.capacity (y := a - 8) (k := 8 * n + 8)
    (by have := b.young; have := b.room; omega)
  have := b.room
  omega

/-- **The scalar nursery input of a reservation.** -/
theorem NurseryInput.of_block {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high a n : Nat} (b : ReservedBlock c a n) (g : Gc.NurseryGeometry P s c pl cp high)
    (sg : StackGeometry P s c pl cp high) (small : n < 2^31) :
    NurseryInput n a (word c Layout.sym_Caml_state).toNat (runtimeFields c).youngLimit c := by
  have young := b.young
  have youngWord : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr)).toNat =
      a + 8 * n := by rw [← young]; rfl
  have limitWord : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit)).toNat =
      (runtimeFields c).youngLimit := rfl
  exact ⟨small, b.room, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [← youngWord, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [← limitWord, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    g.young_write, g.limit_read, g.header_write young b.capacity b.room, b.capacity, sg.young_image⟩

end OCaml.Vm.Sim
