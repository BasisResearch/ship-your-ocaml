import OCaml.Vm.Boot.Startup.CustomFirst
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim VsaIris.Inst OCaml.Vm.Primitives

/-- The native initializer's four completed registrations, before caller restoration. -/
structure CustomNodes (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra s0 head : BitVec 64) (before after : Config) where
  H1 : List (Nat × Nat)
  H2 : List (Nat × Nat)
  H3 : List (Nat × Nat)
  first : Config
  second : Config
  third : Config
  int32 : CustomFirstRegistered H (capacity + 96) sp ra s0 head before first
  nativeint : CustomNextRegistered H1 (capacity + 64) .nativeint (nativeStack sp 16)
    (vsaReg int32.registration.allocated 10) first second
  int64 : CustomNextRegistered H2 (capacity + 32) .int64 (nativeStack sp 16)
    (vsaReg nativeint.registration.allocated 10) second third
  bigarray : CustomNextRegistered H3 capacity .bigarray (nativeStack sp 16)
    (vsaReg int64.registration.allocated 10) third after
  heap1 : H1 = ((vsaReg int32.registration.allocated 10).toNat, 16) :: H
  heap2 : H2 = ((vsaReg nativeint.registration.allocated 10).toNat, 16) :: H1
  heap3 : H3 = ((vsaReg int64.registration.allocated 10).toNat, 16) :: H2

theorem CustomNodes.member {H capacity sp ra s0 head before after e}
    (w : CustomNodes H capacity sp ra s0 head before after) (member : e ∈ H) :
    e ∈ ((vsaReg w.bigarray.registration.allocated 10).toNat, 16) :: w.H3 := by
  apply List.mem_cons_of_mem
  rw [w.heap3]
  apply List.mem_cons_of_mem
  rw [w.heap2]
  apply List.mem_cons_of_mem
  rw [w.heap1]
  exact List.mem_cons_of_mem _ member

/-- All four actual custom-operation requests and publications, consuming
exactly four 32-byte allocator charges and reaching the restoring epilogue. -/
theorem custom_nodes (c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra s0 head : BitVec 64) (ready : RuntimeReady H (capacity + 128) sp ra c)
    (frame : NativeFrame sp 560) (saved0 : gprGet c.σ 8 = some s0)
    (headWord : bytesT c.σ.mem Layout.sym_custom_ops_table 8 = head) :
    FnSummary 0x80024a2c#64 (fun d => d = c)
      (fun after => Nonempty (CustomNodes H capacity sp ra s0 head c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  obtain ⟨first, run1, ⟨w1⟩⟩ := (custom_first c H (capacity + 96) sp ra s0 head ready frame saved0 headWord).run c ⟨pc, rfl⟩
  obtain ⟨second, run2, ⟨w2⟩⟩ := (custom_next first _ (capacity + 64) .nativeint _ _ _
    w1.registration.ready nested w1.registration.table_reg w1.registration.head_word).run
    first ⟨w1.registration.publication.pc, rfl⟩
  obtain ⟨third, run3, ⟨w3⟩⟩ := (custom_next second _ (capacity + 32) .int64 _ _ _
    w2.registration.ready nested w2.registration.table_reg w2.registration.head_word).run
    second ⟨w2.registration.publication.pc, rfl⟩
  obtain ⟨after, run4, ⟨w4⟩⟩ := (custom_next third _ capacity .bigarray _ _ _
    w3.registration.ready nested w3.registration.table_reg w3.registration.head_word).run
    third ⟨w3.registration.publication.pc, rfl⟩
  exact ⟨after, run1.trans (run2.trans (run3.trans run4)), ⟨_, _, _, first, second, third, w1, w2, w3, w4, rfl, rfl, rfl⟩⟩
end OCaml.Vm.Boot.Startup
