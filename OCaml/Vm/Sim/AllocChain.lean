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

end OCaml.Vm.Sim
