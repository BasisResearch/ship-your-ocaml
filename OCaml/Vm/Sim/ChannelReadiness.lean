import OCaml.Vm.Repr.ChannelCounts
import OCaml.Vm.Primitives.Channel.OpenRepr
import OCaml.Vm.Primitives.OutChannelsList
import OCaml.Vm.Sim.CcallRows

/-! Per-call custom readiness from the successful successor, rather than a
budget for every `runtimeOk` configuration. Count representation and the
physical accounting laws remain explicit until their invariant producers
are supplied. -/

namespace OCaml.Vm.Sim
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives
set_option autoImplicit false

/-- A physical accounting result for intermediate execution summaries.
Complete VM boundaries use `CountedCcallReturnAt` instead. -/
structure CountedResult (Customs : Config → Nat → Prop) (Q : Config → Prop) (n : Nat) (c : Config) : Prop where
  post : Q c
  physical : Customs c n

/-- One returned placement witnesses both the ordinary result and every
counted channel observation on this execution. -/
structure CountedCcallReturnAt (Customs : Config → Nat → Prop) (ra : BitVec 64)
    (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (sp high : Nat) (domain frameSp result env : BitVec 64) (c : Config) : Prop
    extends CcallReturnAt ra L P s pl cp sp high domain frameSp result env c where
  counts : ChannelCustomsRepr Customs c cp s.world

structure CountedCcallReturn (Customs : Config → Nat → Prop) (ra : BitVec 64)
    (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (_cp : ChanPlace)
    (sp high : Nat) (domain frameSp result env : BitVec 64) (c : Config) : Prop where
  placed : ∃ cp', CountedCcallReturnAt Customs ra L P s pl cp' sp high domain frameSp result env c

/-- The C_CALL entry with physical custom accounting. The projection retains
the existing caller interface while invariant producers migrate. -/
structure CountedCcallSetupPost (Customs : Config → Nat → Prop) (ra : BitVec 64) (args : List Val)
    (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (sp high domain entry : Nat) (env : BitVec 64) (c : Config) : Prop
    extends CcallSetupPost ra args L P s pl cp sp high domain entry env c where
  counts : ChannelCustomsRepr Customs c cp s.world

/-- A primitive summary at counted C_CALL entries. The ordinary F1 rows still
need the invariant migration before they can consume this interface. -/
structure CountedCcallCallee (Customs : Config → Nat → Prop) (ra : BitVec 64) (args : List Val)
    (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (sp high domain entry : Nat) (env : BitVec 64) (name : String)
    (v : Val) (result : BitVec 64) (heap : Heap) (world : World) : Prop where
  fragment : name ∈ primsF1
  semantics : primF1Impl name args s.heap s.world = .ok v heap world
  summary : ∀ c, CountedCcallSetupPost Customs ra args L P s pl cp sp high domain entry env c →
    (∀ p ∈ allocPlaces name s (BitVec.ofNat 64 (runtimeFields c).youngPtr), pl.φ p.1 = some p.2) →
    FnSummary (BitVec.ofNat 64 entry) (fun x => x = c)
      (CountedCcallReturn Customs ra L P {s with pc := s.pc + 2, accu := v, heap := heap, world := world}
        pl cp sp high (BitVec.ofNat 64 domain) (BitVec.ofNat 64 (sp - 16)) result env)

/-- Returning primitive contract for the counted invariant, over the full
successful F1 domain. The original loop-entry counts are supplied explicitly;
its actual return retains complete counts at the returned placement. -/
def CountedPrimReturnsAtR (L : OCaml.Layout) (P : Prog) (Customs : Config → Nat → Prop)
    (op : Opcode) (ra : BitVec 64) (k : Nat) (name : String) : Prop :=
  ∀ s c pl cp sp high table entry value env index v heap world, Reach P s →
    CcallReady op L P s c pl cp sp high (domainAt c) table entry value env index name →
    ChannelCustomsRepr Customs c cp s.world →
    primF1Impl name (s.accu :: s.stack.take k) s.heap s.world = .ok v heap world →
    heap.words ≤ L.budget.heapWords → CcallSucc P heap world →
    ∃ result, CountedCcallCallee Customs ra (s.accu :: s.stack.take k) L P s pl cp sp high
      (domainAt c) entry env name v result heap world

/-- `Fits` applies to the actual successful C_CALL successor's custom count. -/
theorem CcallSucc.customs_bound {P : Prog} {B : OCaml.Budget} {heap : Heap} {world : World}
    (fits : OCaml.Fits B P) (succ : CcallSucc P heap world) : world.customs ≤ B.customs := by
  obtain ⟨s', reach, _, worldEq⟩ := succ
  rw [← worldEq]
  exact (fits s' reach).customs

/-- Opening either input or output allocates exactly one custom block. -/
theorem openChan_customs {h h' : Heap} {w w' : World} {fd : Int} {out : Bool} {v : Val}
    (ok : openChan h w fd out = .ok v h' w') : w'.customs = w.customs + 1 := by
  obtain ⟨_, _, off, rfl⟩ := openChan_ok ok
  simp [World.customs]

/-- The listing charges one custom allocation for each listed channel;
the accompanying cons cells consume nursery words, but no custom budget. -/
theorem listRefs_customs (w : World) :
    (listRefs w).customs = w.customs + (outChannelIds w).length := by
  have count (cs : List Chan) :
      ((cs.map fun ch => if ch.listed then { ch with refs := ch.refs + 1 } else ch).map Chan.refs).sum =
        (cs.map Chan.refs).sum + (cs.filter Chan.listed).length := by
    induction cs with
    | nil => rfl
    | cons ch cs ih =>
      cases eq : ch.listed <;> simp only [List.map_cons, eq, Bool.false_eq_true, ite_false,
        ite_true, List.sum_cons, List.filter_cons, List.length_cons] at * <;> omega
  let atId : Nat → Chan := fun id => w.chans[id]?.getD ⟨0, false, [], [], 0, 0, 0⟩
  have all : (List.range w.chans.length).map atId = w.chans := map_range_getD _ _
  have length : (outChannelIds w).length = (w.chans.filter Chan.listed).length := by
    rw [← all, List.filter_map, List.length_map]
    unfold outChannelIds
    rw [List.length_reverse]
    congr 1
    apply List.filter_congr
    intro id hid
    have lt : id < w.chans.length := by simpa using hid
    simp only [Function.comp_def, atId, List.getElem?_eq_getElem lt, Option.map_some,
      Option.getD_some, Chan.listed]
  rw [length]
  exact count w.chans

/-- Shared successful-call readiness bridge. The machine invariant supplies
the physical count witness; the caller supplies the successor's exact charge. -/
theorem channel_call_ready {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {c : Config} {cp : ChanPlace} {w w' : World} {k : Nat}
    (accounting : Gc.CustomMemCall.Accounting Ready state Customs)
    (counts : ChannelCustomsRepr Customs c cp w)
    (charge : w'.customs = w.customs + k) (bound : w'.customs ≤ Gc.quietBound) : Ready k c :=
  counts.boundary.ready accounting (by omega)

/-- One quiet allocation at a successful reachable opening. -/
theorem open_call_ready {P : Prog} {B : OCaml.Budget} {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {c : Config} {cp : ChanPlace} {s : St}
    {heap : Heap} {world : World} {v : Val} {fd : Int} {out : Bool}
    (accounting : Gc.CustomMemCall.Accounting Ready state Customs)
    (counts : ChannelCustomsRepr Customs c cp s.world)
    (fits : OCaml.Fits B P) (budget : B.customs ≤ Gc.quietBound)
    (succ : CcallSucc P heap world) (ok : openChan s.heap s.world fd out = .ok v heap world) :
    Ready 1 c :=
  channel_call_ready accounting counts (openChan_customs ok)
    (Nat.le_trans (succ.customs_bound fits) budget)

/-- The full out-list batch is quiet at its successful reachable C_CALL. -/
theorem out_list_call_ready {P : Prog} {B : OCaml.Budget} {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {c : Config} {cp : ChanPlace} {s : St} {heap : Heap}
    (accounting : Gc.CustomMemCall.Accounting Ready state Customs)
    (counts : ChannelCustomsRepr Customs c cp s.world)
    (fits : OCaml.Fits B P) (budget : B.customs ≤ Gc.quietBound)
    (succ : CcallSucc P heap (listRefs s.world)) : Ready (outChannelIds s.world).length c :=
  channel_call_ready accounting counts (listRefs_customs s.world)
    (Nat.le_trans (succ.customs_bound fits) budget)

end OCaml.Vm.Sim
