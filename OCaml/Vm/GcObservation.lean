import OCaml.Vm.Repr

/-! Concrete correspondence for quick_stat observations. This is a named
input obligation for the collector/runtime simulation, not a consequence
of the host trace used by the executable compiler differential. -/
namespace OCaml.Vm
open OCaml.Bytecode Vsa.Machine

/-- Counter snapshot at the C primitive entry, before its allocations.
The stack-usage hook is null in the supported bare-metal configuration. -/
structure GcSnapshotAt (c : Config) (s : GcSnapshot) : Prop where
  valid : s.valid = true
  noHook : word c Layout.sym_caml_stack_usage_hook = 0
  nurseryOrder : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr)).toNat ≤
    (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_young_alloc_end)).toNat
  allocatedNonnegative : 0 ≤ (word c Layout.sym_caml_allocated_words).toInt
  stackOrder : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp)).toNat ≤
    (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).toNat
  minor : s.minorWords = floatBits
    (floatFromBits (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stat_minor_words)) +
     (((word c ((word c Layout.sym_Caml_state).toNat + Layout.off_young_alloc_end)).toNat -
       (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr)).toNat) / 8).toUInt64.toFloat)
  promoted : s.promotedWords = word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stat_promoted_words)
  major : s.majorWords = floatBits
    (floatFromBits (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stat_major_words)) +
     (word c Layout.sym_caml_allocated_words).toNat.toUInt64.toFloat)
  minorCollections : s.minorCollections = (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stat_minor_collections)).toInt
  majorCollections : s.majorCollections = (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stat_major_collections)).toInt
  heapWords : s.heapWords = (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stat_heap_wsz)).toInt
  heapChunks : s.heapChunks = (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stat_heap_chunks)).toInt
  compactions : s.compactions = (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stat_compactions)).toInt
  topHeapWords : s.topHeapWords = (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stat_top_heap_wsz)).toInt
  stackSize : s.stackSize =
    (((word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).toNat -
      (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp)).toNat) / 8 : Nat)
  forcedMajor : s.forcedMajorCollections = (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stat_forced_major_collections)).toInt

/-- Supply at each quick_stat C entry from the concrete collector state.
Current WorldRepr alone does not establish this additional observation. -/
structure GcObservationInput (c : Config) (w : World) : Prop where
  available : w.gcSnapshots ≠ []
  agrees : ∀ snapshot rest, w.gcSnapshots = snapshot :: rest → GcSnapshotAt c snapshot

end OCaml.Vm
