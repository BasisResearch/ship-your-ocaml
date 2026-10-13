import OCaml.Vm.Sim.AllocInput
import OCaml.Vm.Sim.LoopGeometry

/-!
# Chained nursery reservations

A primitive that allocates several objects (a string, then the tuple holding
it) reserves each below `young_ptr` in turn. `reserved c a` is the config `c`
after the young-pointer store of one reservation at `a`, and nothing else:
`LoopGeometry.reserve` moves the loop geometry there with the fresh object
placed. Chaining it gives the geometry of the heap with all the objects; the
real post-call config then agrees with the last virtual one on the words the
geometry reads (`LoopGeometry.transport`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- `c` after the young-pointer store of a reservation at `a`. -/
def reserved (c : Config) (a : Nat) : Config :=
  { c with σ := { c.σ with mem := writeLog c.σ.mem (grabReserveLog (word c Layout.sym_Caml_state).toNat a) } }

theorem reserved_word {c : Config} {a x : Nat}
    (out : OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a) x 8) :
    word (reserved c a) x = word c x := by
  change bytesT (writeLog c.σ.mem _) x 8 = bytesT c.σ.mem x 8
  rw [bytesT_writeLog_out _ out]

/-- The words a reservation misses: everything the geometry reads except the
young pointer. -/
structure GrabOutside (P : Prog) (s : St) (c : Config) (cp : ChanPlace) (a : Nat) : Prop where
  domain : OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a) Layout.sym_Caml_state 8
  contents : OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a)
    (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8
  chans : ∀ id ch b, s.world.chans[id]? = some ch → cp id = some b →
    OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a) b (chanOffBuff + ioBufferSize)
  head : OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a) Layout.sym_caml_all_opened_channels 8
  limit : OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a)
    ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit) 8

theorem GrabOutside.of_geometry {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {high : Nat}
    (g : StackGeometry P s c pl cp high) (a : Nat) : GrabOutside P s c cp a := by
  have hl := g.domainLow
  have static : ∀ x, x + 8 ≤ Layout.sym_bss_end →
      OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a) x 8 := fun x hx =>
    grab_out (by simp only [Layout.off_young_ptr]; omega)
  exact ⟨static _ (by decide), static _ (by decide),
    fun id ch b hch hcp => young_apart (g.domainChannels id ch b hch hcp), static _ (by decide),
    grab_out (by simp only [Layout.off_young_ptr, Layout.off_young_limit]; omega)⟩

/-- The reservation's scalar record, from the reserved block. -/
theorem NurseryReserve.grab {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {high a n : Nat}
    (b : ReservedBlock c a n) (g : StackGeometry P s c pl cp high) :
    NurseryReserve c (grabReserveLog (word c Layout.sym_Caml_state).toNat a) a n n := by
  have out := GrabOutside.of_geometry g a
  have room := b.room
  have top := b.top
  refine ⟨b.young, Nat.le_refl _, room, by have := b.aligned; omega, b.capacity, fun c' memory => ?_⟩
  have keep : ∀ x, OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a) x 8 → word c' x = word c x :=
    fun x hx => by
      change bytesT c'.σ.mem x 8 = bytesT c.σ.mem x 8
      rw [memory, bytesT_writeLog_out _ hx]
  have domainKeep := keep _ out.domain
  have youngNew : word c' ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr) = BitVec.ofNat 64 (a - 8) := by
    change bytesT c'.σ.mem _ 8 = _
    rw [memory]
    exact Gc.word_writeLog_at _ _ 0 _ _ (by simp [grabReserveLog]) trivial
  refine ⟨?_, ?_⟩
  · simp only [runtimeFields, domainWord, domainKeep, youngNew, BitVec.toNat_ofNat]
    omega
  · simp only [runtimeFields, domainWord, domainKeep, keep _ out.limit]

/-- **One reservation, on the virtual config**: the fresh object is placed at
the block below the young pointer, within the budget. -/
theorem _root_.OCaml.LoopGeometry.reserve {L : OCaml.Layout} {P : Prog} {s : St} {c : Config} {pl : Place}
    {cp : ChanPlace} {high : Nat} {o : Obj} (g : OCaml.LoopGeometry L P s c pl cp high)
    (fits : s.heap.words + (o.wosize + 1) ≤ L.budget.heapWords)
    (placed : pl.φ (s.heap.alloc o).2 = some ((runtimeFields c).youngPtr - 8 * o.wosize)) :
    OCaml.LoopGeometry L P { s with heap := (s.heap.alloc o).1 }
      (reserved c ((runtimeFields c).youngPtr - 8 * o.wosize)) pl cp high := by
  have b := ReservedBlock.of_reservation g.nursery (⟨g.room, fits⟩ : Reservation L s c o.wosize)
  have out := GrabOutside.of_geometry g.toStackGeometry ((runtimeFields c).youngPtr - 8 * o.wosize)
  exact g.alloc_log placed (NurseryReserve.grab b g.toStackGeometry) rfl rfl out.domain out.contents out.chans
    out.head rfl

/-- The virtual config's young pointer is the reservation's `a - 8`. -/
theorem reserved_young {c : Config} {a n : Nat} (b : ReservedBlock c a n)
    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {high : Nat} (g : StackGeometry P s c pl cp high) :
    (runtimeFields (reserved c a)).youngPtr = a - 8 ∧
      (runtimeFields (reserved c a)).youngLimit = (runtimeFields c).youngLimit :=
  (NurseryReserve.grab b g).after _ rfl

/-- The words a log misses read the same after it. -/
structure GeometryWordsKept (log : List WEntry) (s : St) (c : Config) (cp : ChanPlace) : Prop where
  domain : OutLRange log Layout.sym_Caml_state 8
  contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8
  head : OutLRange log Layout.sym_caml_all_opened_channels 8
  limit : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit) 8
  chans : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    OutLRange log a (chanOffBuff + ioBufferSize)

/-- **Two reservations, then the real config**: a string (or any object)
`o1`, then a block `o2` below it, placed at their nursery blocks; the config
`after` holds the log's effect on every word the geometry reads, and its
young pointer is below both objects. -/
theorem _root_.OCaml.LoopGeometry.reserve2 {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {high : Nat} {o1 o2 : Obj} {log : List WEntry}
    (g : OCaml.LoopGeometry L P s c pl cp high)
    (fits : s.heap.words + (o1.wosize + 1) + (o2.wosize + 1) ≤ L.budget.heapWords)
    (placed1 : pl.φ (s.heap.alloc o1).2 = some ((runtimeFields c).youngPtr - 8 * o1.wosize))
    (placed2 : pl.φ ((s.heap.alloc o1).1.alloc o2).2 =
      some ((runtimeFields c).youngPtr - 8 * (o1.wosize + 1) - 8 * o2.wosize))
    (kept : GeometryWordsKept log s c cp)
    (memory : ∀ x, OutLRange log x 8 → word after x = word c x)
    (young : (runtimeFields after).youngPtr =
      (runtimeFields c).youngPtr - 8 * (o1.wosize + 1) - 8 * (o2.wosize + 1)) :
    OCaml.LoopGeometry L P { s with heap := ((s.heap.alloc o1).1.alloc o2).1 } after pl cp high := by
  have b1 := ReservedBlock.of_reservation g.nursery (⟨g.room, by omega⟩ : Reservation L s c o1.wosize)
  have g1 := g.reserve (by omega) placed1
  obtain ⟨y1, l1⟩ := reserved_young b1 g.toStackGeometry
  have room1 := b1.room
  have g2 := g1.reserve (o := o2) (by simp only [Heap.words_alloc]; omega) (by
    rw [placed2, y1, Option.some.injEq]; omega)
  let c1 := reserved c ((runtimeFields c).youngPtr - 8 * o1.wosize)
  let c2 := reserved c1 ((runtimeFields c1).youngPtr - 8 * o2.wosize)
  have out1 := GrabOutside.of_geometry g.toStackGeometry ((runtimeFields c).youngPtr - 8 * o1.wosize)
  have out2 := GrabOutside.of_geometry g1.toStackGeometry ((runtimeFields c1).youngPtr - 8 * o2.wosize)
  have w1 : ∀ x, OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat
      ((runtimeFields c).youngPtr - 8 * o1.wosize)) x 8 → word c1 x = word c x := fun x h => reserved_word h
  have w2 : ∀ x, OutLRange (grabReserveLog (word c1 Layout.sym_Caml_state).toNat
      ((runtimeFields c1).youngPtr - 8 * o2.wosize)) x 8 → word c2 x = word c1 x := fun x h => reserved_word h
  have dom1 : word c1 Layout.sym_Caml_state = word c Layout.sym_Caml_state := w1 _ out1.domain
  have dom2 : word c2 Layout.sym_Caml_state = word c1 Layout.sym_Caml_state := w2 _ out2.domain
  have domA : word after Layout.sym_Caml_state = word c Layout.sym_Caml_state := memory _ kept.domain
  have b2 := ReservedBlock.of_reservation g1.nursery
    (⟨g1.room, by simp only [Heap.words_alloc]; omega⟩ : Reservation L _ c1 o2.wosize)
  obtain ⟨y2, l2⟩ := reserved_young b2 g1.toStackGeometry
  refine g2.transport (fun l o h => ⟨o, h, rfl⟩) rfl (domA.trans (dom2.trans dom1).symm)
    ((memory _ kept.contents).trans ((w2 _ out2.contents).trans (w1 _ out1.contents)).symm) ?_ ?_
    ((memory _ kept.head).trans ((w2 _ out2.head).trans (w1 _ out1.head)).symm) ?_ rfl
  · have lA : (runtimeFields after).youngLimit = (runtimeFields c).youngLimit := by
      simp only [runtimeFields, domainWord, domA, memory _ kept.limit]
    rw [lA, l2, l1]
  · rw [young, y2, y1]; omega
  · intro id ch a hc hp
    have k0 := links_of_channels kept.chans id ch a hc hp
    have k1 := links_of_channels out1.chans id ch a hc hp
    have k2 := links_of_channels out2.chans id ch a hc hp
    exact (memory _ k0).trans ((w2 _ k2).trans (w1 _ k1)).symm

end OCaml.Vm.Sim
