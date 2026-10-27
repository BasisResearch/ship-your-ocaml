import OCaml.Vm.Boot.WhileMinRuntimeReads

/-! Collector invariants for the memory candidate certified by the store log.
The memory premise is separate from the outstanding Sail execution certificate. -/
namespace OCaml.Vm.Boot.WhileMinRuntime
open Vsa.Machine Vsa.Sim.Boot WhileMinLog

variable {c : Config} {initial : Vsa.MemRepr.Mem}

/-- Startup has disabled the optional stat-allocation pool. -/
theorem poolZero (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem initial log)) :
    Vsa.Sim.LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8) := by
  have rd (i : Nat) (h : byte c (Layout.sym_pool + i) = 0#8) :
      (c.σ.mem[Layout.sym_pool + i]?).getD 0 = 0#8 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have bit := congrArg (fun v : BitVec 8 => v.getLsbD k) h
    rw [byte, Vsa.Sim.getLsbD_bytesT _ 1 _ k hk] at bit
    simpa only [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, Nat.add_zero] using bit
  exact ⟨rd 0 (read_pool_0 memory), rd 1 (read_pool_1 memory), rd 2 (read_pool_2 memory),
    rd 3 (read_pool_3 memory), rd 4 (read_pool_4 memory), rd 5 (read_pool_5 memory),
    rd 6 (read_pool_6 memory), rd 7 (read_pool_7 memory)⟩

/-- The observed scalar projection equals reads from the certified memory. -/
theorem fields (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem initial log)) :
    runtimeFields c = WhileMinObservation.observed := by
  have dom : (word c Layout.sym_Caml_state).toNat = domain :=
    congrArg BitVec.toNat (read_domain memory)
  unfold runtimeFields domainWord
  rw [dom, read_young_start memory, read_young_end memory,
    read_young_alloc_start memory, read_young_alloc_end memory,
    read_young_ptr memory, read_young_limit memory, read_pending memory]
  rfl

/-- The best-fit free lists have the measured singleton shape. -/
theorem freeList (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem initial log)) : BestFitSingleton c := by
  refine ⟨freeBlock, ?_⟩
  exact {
    nonnull := by decide +kernel
    aligned := by decide +kernel
    large := by decide +kernel
    fits := by decide +kernel
    small := small_lists memory
    bitmap := read_bf_small_map memory
    root := congrArg BitVec.toNat (read_bf_large_tree memory)
    least := congrArg BitVec.toNat (read_bf_large_least memory)
    header := congrArg BitVec.toNat (read_header memory)
    node := read_isnode memory
    left := read_left memory
    right := read_right memory
    prev := congrArg BitVec.toNat (read_prev memory)
    next := congrArg BitVec.toNat (read_next memory)
    total := congrArg BitVec.toNat (read_caml_fl_cur_wsz memory)
  }

/-- Concrete collector invariant for any configuration with the certified
observed memory. A startup execution proof must supply this memory premise. -/
theorem runtimeOk (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem initial log)) :
    RuntimeOk BestFitSingleton c where
  bounds := by rw [fields memory]; exact WhileMinObservation.bounds
  noPending := by rw [fields memory]; exact WhileMinObservation.noPending
  freeListShape := freeList memory

/-- Densification preserves the concrete startup collector invariant. -/
theorem runtimeOk_fillZero (memory : c.σ.mem = observedMem initial log) :
    RuntimeOk BestFitSingleton (Vsa.Densify.fillZero c) := by
  apply runtimeOk (initial := initial)
  exact (Vsa.Densify.memEqv_fillZeroMem c.σ.mem).symm.trans
    (by rw [memory]; exact Vsa.Densify.MemEqv.refl _)

end OCaml.Vm.Boot.WhileMinRuntime
