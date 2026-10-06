import OCaml.Refinement
import OCaml.Vm.Gc.G1RoomTransport
import OCaml.Vm.Sim.HeapWords

/-!
# Transports of the loop geometry

`OCaml.LoopGeometry` is the arm geometry plus the G1 nursery room. Its
transports mirror `ArmGeometry`'s (same names, so restore sites are
unchanged): the room survives every write log that misses the allocation
pointers (`Gc.G1Room.frame`) and allocation consumes it (`Gc.G1Room.reserve`).
-/

namespace OCaml
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Sim OCaml.Vm.Primitives

theorem LoopGeometry.same {L : Layout} {P : Prog} {s s' : St} {c c' : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} (g : LoopGeometry L P s c pl cp high)
    (heap : s'.heap = s.heap) (world : s'.world = s.world) (memory : c'.σ.mem = c.σ.mem) :
    LoopGeometry L P s' c' pl cp high :=
  ⟨g.toArmGeometry.same heap world memory, g.room.same memory (by rw [heap]; exact Nat.le_refl _)⟩

theorem LoopGeometry.state {L : Layout} {P : Prog} {s s' : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} (g : LoopGeometry L P s c pl cp high)
    (heap : s'.heap = s.heap) (world : s'.world = s.world) : LoopGeometry L P s' c pl cp high :=
  g.same heap world rfl

/-- **Transport across an arm's write log** missing the allocation pointers. -/
theorem LoopGeometry.frame_log {L : Layout} {P : Prog} {s s' : St} {c c' : Config} {pl : Place}
    {cp : ChanPlace} {high : Nat} {log : List WEntry} (g : LoopGeometry L P s c pl cp high)
    (heap : s'.heap = s.heap) (world : s'.world = s.world)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8)
    (young : YoungOutside log c)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : LoopGeometry L P s' c' pl cp high :=
  ⟨g.toArmGeometry.frame_log heap world domain contents young memory,
   g.room.frame young domain memory (by rw [heap]; exact Nat.le_refl _)⟩

theorem LoopGeometry.frame_vm {L : Layout} {P : Prog} {s s' : St} {c c' : Config} {pl : Place}
    {cp : ChanPlace} {high : Nat} {ws : List W} {log : List WEntry} (g : LoopGeometry L P s c pl cp high)
    (heap : s'.heap = s.heap) (world : s'.world = s.world)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8)
    (inside : LogInW ws log) (vm : ∀ w ∈ ws, VmWindow high (word c Layout.sym_Caml_state).toNat w)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : LoopGeometry L P s' c' pl cp high :=
  g.frame_log heap world domain contents (.of_windows g.toStackGeometry inside vm) memory

/-- Transport keeping the heap's words and the allocation pointers. -/
theorem LoopGeometry.transport {L : Layout} {P : Prog} {s s' : St} {c c' : Config} {pl : Place}
    {cp : ChanPlace} {high : Nat} (g : LoopGeometry L P s c pl cp high)
    (objects : ∀ l o', s'.heap.get? l = some o' → ∃ o, s.heap.get? l = some o ∧ o.wosize = o'.wosize)
    (chans : s'.world.chans = s.world.chans)
    (domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (prims : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents))
    (limit : (runtimeFields c').youngLimit = (runtimeFields c).youngLimit)
    (ptr : (runtimeFields c').youngPtr = (runtimeFields c).youngPtr)
    (words : s'.heap.words = s.heap.words) : LoopGeometry L P s' c' pl cp high :=
  ⟨g.toArmGeometry.transport objects chans domain prims limit ptr,
   ⟨by rw [limit, ptr, words]; exact g.room.nursery⟩⟩

/-- **Allocation consumes the room**: the reserved block holds exactly the
fresh object. No budget check is needed: past the budget the room is just the
reservation's capacity bound. -/
theorem LoopGeometry.alloc_log {L : Layout} {P : Prog} {s s' : St} {c c' : Config} {pl : Place}
    {cp : ChanPlace} {high a : Nat} {o : Obj} {log : List WEntry}
    (g : LoopGeometry L P s c pl cp high)
    (placed : pl.φ (s.heap.alloc o).2 = some a)
    (reserve : NurseryReserve c log a o.wosize o.wosize)
    (heap : s'.heap = (s.heap.alloc o).1) (world : s'.world = s.world)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : LoopGeometry L P s' c' pl cp high := by
  obtain ⟨ptr, limit⟩ := reserve.after c' memory
  have words : s'.heap.words = s.heap.words + (o.wosize + 1) := by rw [heap, Heap.words_alloc]
  have room := g.room.nursery
  have capacity := reserve.capacity
  have before := reserve.before
  have low := reserve.room
  exact ⟨g.toArmGeometry.alloc_log placed reserve heap world domain contents memory,
    ⟨by rw [limit, ptr, words]; omega⟩⟩

end OCaml
