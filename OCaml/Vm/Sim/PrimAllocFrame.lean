import OCaml.Vm.Sim.MakeblockRows
import OCaml.Vm.Sim.F1NativeWindow
import OCaml.Vm.Gc.F1Observation

/-!
# The runtime invariant across a native allocating primitive

A primitive with a native frame that allocates in the nursery (the
`caml_copy_string` family: `caml_sys_get_config`, `caml_sys_get_argv`,
`caml_sys_executable_name`) writes four kinds of words:
* inside the free nursery (headers, fields, copied bytes);
* above the allocator arena (its native frames);
* the domain's `young_ptr` (each reservation);
* the domain's `local_roots` (`CAMLparam`/`CAMLreturn`).
`PrimAllocFrame L` says such a log keeps the layout's runtime invariant when
the final young pointer stays within the nursery. The F1 instance is a6-gc's
`Gc.f1_allocation`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Boot

/-- One store of a native allocating primitive, at the loop-head config `c`. -/
def PrimAllocEntry (c : Config) (e : WEntry) : Prop :=
  ((runtimeFields c).youngLimit ≤ e.1 ∧ e.1 + e.2.1 ≤ (runtimeFields c).youngPtr) ∨
    Vsa.Sim.DlHeap.heapEnd ≤ e.1 ∨
    ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr ≤ e.1 ∧
      e.1 + e.2.1 ≤ (word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr + 8) ∨
    ((word c Layout.sym_Caml_state).toNat + Layout.off_local_roots ≤ e.1 ∧
      e.1 + e.2.1 ≤ (word c Layout.sym_Caml_state).toNat + Layout.off_local_roots + 8)

/-- **A native allocating primitive keeps the runtime invariant** (named
obligation; F1: `f1_primAllocFrame`): every store is a `PrimAllocEntry` and
the final young pointer lies between the old limit and the old pointer. -/
structure PrimAllocFrame (L : OCaml.Layout) : Prop where
  allocW : ∀ (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace) (high : Nat) (log : List WEntry),
    L.runtimeOk c → Gc.NurseryGeometry P s c pl cp high → (∀ e ∈ log, PrimAllocEntry c e) →
    (∀ after : Config, after.σ.mem = writeLog c.σ.mem log →
      (runtimeFields c).youngLimit ≤
          (word after ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr)).toNat ∧
        (word after ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr)).toNat ≤
          (runtimeFields c).youngPtr ∧
        (word after ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr)).toNat % 8 = 0) →
    ObservationRuntime L.runtimeOk c (fun x => ((writeLog c.σ.mem log)[x]?).getD 0)

/-- A domain field outside the kept dynamic words and the remembered-set words. -/
theorem domain_field_safe {off : Nat}
    (kept : ∀ v ∈ Gc.dynamicKept, Gc.Apart ⟨Gc.f1Domain + off, Gc.f1Domain + off + 8⟩ v)
    (fits : off + 8 ≤ Layout.domainStateBytes) (table : Gc.TableFree (Gc.f1Domain + off) (Gc.f1Domain + off + 8)) :
    (∀ v ∈ Gc.keptFootprint, Gc.Apart ⟨Gc.f1Domain + off, Gc.f1Domain + off + 8⟩ v) ∧
      Gc.F1HeapSafe ⟨Gc.f1Domain + off, Gc.f1Domain + off + 8⟩ :=
  ⟨Gc.kept_apart (Or.inl (by simp only [Gc.f1Domain, WhileMinRuntime.domain, Layout.sym_bss_end]; omega)) kept,
    Gc.heapSafe_domain (Nat.le_add_right _ _) (by omega) table⟩

theorem young_field_safe :
    (∀ v ∈ Gc.keptFootprint, Gc.Apart ⟨Gc.f1Domain + Layout.off_young_ptr, Gc.f1Domain + Layout.off_young_ptr + 8⟩ v) ∧
      Gc.F1HeapSafe ⟨Gc.f1Domain + Layout.off_young_ptr, Gc.f1Domain + Layout.off_young_ptr + 8⟩ := by
  refine domain_field_safe ?_ (by decide) (Or.inl (by simp only [Layout.off_young_ptr, Layout.off_minor_heap_wsz]; omega))
  intro v hv
  simp only [Gc.dynamicKept, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Gc.Apart] <;>
    simp only [Gc.f1Domain, WhileMinRuntime.domain, WhileMinRuntime.freeBlock,
      Layout.off_young_ptr, Layout.off_stack_high, Layout.off_stack_threshold,
      Layout.off_trap_barrier, Layout.off_backtrace_active, Layout.off_minor_heap_wsz, Layout.off_stat_heap_wsz, Layout.off_custom_table] <;> omega

theorem roots_field_safe :
    (∀ v ∈ Gc.keptFootprint, Gc.Apart ⟨Gc.f1Domain + Layout.off_local_roots, Gc.f1Domain + Layout.off_local_roots + 8⟩ v) ∧
      Gc.F1HeapSafe ⟨Gc.f1Domain + Layout.off_local_roots, Gc.f1Domain + Layout.off_local_roots + 8⟩ := by
  refine domain_field_safe ?_ (by decide)
    (by simp only [Gc.TableFree, Layout.off_local_roots, Layout.off_minor_heap_wsz, Layout.off_ref_table]; omega)
  intro v hv
  simp only [Gc.dynamicKept, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Gc.Apart] <;>
    simp only [Gc.f1Domain, WhileMinRuntime.domain, WhileMinRuntime.freeBlock,
      Layout.off_young_ptr, Layout.off_local_roots, Layout.off_stack_high,
      Layout.off_stack_threshold, Layout.off_trap_barrier, Layout.off_backtrace_active, Layout.off_minor_heap_wsz, Layout.off_stat_heap_wsz, Layout.off_custom_table] <;> omega

/-- A store inside the `young_ptr` word is apart from the kept footprint and heap-safe. -/
theorem young_sub_safe {lo hi : Nat} (h1 : Gc.f1Domain + Layout.off_young_ptr ≤ lo)
    (h2 : hi ≤ Gc.f1Domain + Layout.off_young_ptr + 8) :
    (∀ v ∈ Gc.keptFootprint, Gc.Apart ⟨lo, hi⟩ v) ∧ Gc.F1HeapSafe ⟨lo, hi⟩ := by
  refine ⟨fun v hv => ?_, ?_⟩
  · have := young_field_safe.1 v hv
    simp only [Gc.Apart] at this ⊢
    omega
  · simp only [Layout.off_young_ptr] at h1 h2
    exact Gc.heapSafe_domain (by generalize Gc.f1Domain = D at *; omega)
      (by simp only [Layout.domainStateBytes]; generalize Gc.f1Domain = D at *; omega)
      (Or.inl (by simp only [Layout.off_minor_heap_wsz]; generalize Gc.f1Domain = D at *; omega))

/-- A store inside the `local_roots` word is apart from the kept footprint and heap-safe. -/
theorem roots_sub_safe {lo hi : Nat} (h1 : Gc.f1Domain + Layout.off_local_roots ≤ lo)
    (h2 : hi ≤ Gc.f1Domain + Layout.off_local_roots + 8) :
    (∀ v ∈ Gc.keptFootprint, Gc.Apart ⟨lo, hi⟩ v) ∧ Gc.F1HeapSafe ⟨lo, hi⟩ := by
  refine ⟨fun v hv => ?_, ?_⟩
  · have := roots_field_safe.1 v hv
    simp only [Gc.Apart] at this ⊢
    omega
  · simp only [Layout.off_local_roots] at h1 h2
    exact Gc.heapSafe_domain (by generalize Gc.f1Domain = D at *; omega)
      (by simp only [Layout.domainStateBytes]; generalize Gc.f1Domain = D at *; omega)
      (Or.inr (Or.inr (by simp only [Layout.off_ref_table]; generalize Gc.f1Domain = D at *; omega)))

/-- **`PrimAllocFrame` for the pinned F1 layout.** -/
theorem f1_primAllocFrame : PrimAllocFrame Gc.f1Layout := by
  refine ⟨fun P s c pl cp high log ok g entries young => Gc.f1_observation_of ?_⟩
  have dom := Gc.f1_domain ok
  have stat := g.statics
  have priv := g.belowPrivate
  have top := g.top
  have nlow := g.nurseryLow
  simp only [Gc.minorRegion] at nlow
  obtain ⟨domainApart, -⟩ := g.domain
  rw [dom] at domainApart
  simp only [Gc.nurseryFree, Gc.privateRegion, Layout.sym_bss_end, Layout.domainStateBytes, Gc.f1Domain,
    WhileMinRuntime.domain] at stat priv domainApart
  apply Gc.f1_allocation
  · intro e he v hv
    rcases entries e he with hin | hin | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Gc.kept_apart (w := ⟨e.1, e.1 + e.2.1⟩) (Or.inl (by
        simp only [Gc.f1Domain, WhileMinRuntime.domain, Layout.sym_bss_end] at *; omega)) ?_ v hv
      intro v hv
      simp only [Gc.dynamicKept, List.mem_cons, List.not_mem_nil, or_false] at hv
      simp only [Gc.f1Domain, WhileMinRuntime.domain] at *
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Gc.Apart] <;>
        (try simp only [WhileMinRuntime.freeBlock,
          Layout.off_young_ptr, Layout.off_stack_high, Layout.off_stack_threshold, Layout.off_trap_barrier,
          Layout.off_backtrace_active, Layout.off_minor_heap_wsz, Layout.off_stat_heap_wsz, Layout.off_custom_table]) <;> omega
    · exact (native_safe (hi := e.1 + e.2.1) hin).1 v (List.mem_cons_of_mem _ hv)
    · rw [dom] at h1 h2
      exact (young_sub_safe h1 h2).1 v hv
    · rw [dom] at h1 h2
      exact (roots_sub_safe h1 h2).1 v hv
  · intro e he
    rcases entries e he with hin | hin | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have nl := g.nurseryLow
      have nh := g.nurseryHigh
      exact Gc.heapSafe_minor (by omega) (by omega)
    · exact Gc.heapSafe_native hin
    · rw [dom] at h1 h2
      exact (young_sub_safe h1 h2).2
    · rw [dom] at h1 h2
      exact (roots_sub_safe h1 h2).2
  · intro after memory
    have := young after memory
    rw [dom] at this
    exact this

end OCaml.Vm.Sim
