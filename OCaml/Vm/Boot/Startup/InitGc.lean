import OCaml.Vm.Boot.Startup.InitGcSteps
import OCaml.Vm.Boot.Startup.GcMessageReady
import OCaml.Vm.Boot.Startup.PageTable
import OCaml.Vm.Gc.ReadyCalls

/-! caml_init_gc, composed with its callees, at the default parameters. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  OCaml.Vm.Gc LeanRV64DExecutable

/-- The ref tables' facts that do not mention the page table. -/
structure RefTablesPre (H : List (Nat × Nat)) (m : Std.ExtHashMap Nat (BitVec 8)) (t1 t2 t3 : BitVec 64) : Prop where
  ptr1 : bytesT m (domainField 104) 8 = t1
  ptr2 : bytesT m (domainField 112) 8 = t2
  ptr3 : bytesT m (domainField 120) 8 = t3
  spot1 : RefTableSpot t1
  spot2 : RefTableSpot t2
  spot3 : RefTableSpot t3
  empty1 : bytesT m t1.toNat 8 = 0#64
  empty2 : bytesT m t2.toNat 8 = 0#64
  empty3 : bytesT m t3.toNat 8 = 0#64
  apart12 : t1.toNat + 56 ≤ t2.toNat ∨ t2.toNat + 56 ≤ t1.toNat
  apart23 : t2.toNat + 56 ≤ t3.toNat ∨ t3.toNat + 56 ≤ t2.toNat
  domain1 : t1.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t1.toNat
  apart13 : t1.toNat + 56 ≤ t3.toNat ∨ t3.toNat + 56 ≤ t1.toNat
  domain2 : t2.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t2.toNat
  domain3 : t3.toNat + 56 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ t3.toNat
  owned1 : (t1.toNat, 56) ∈ H
  owned2 : (t2.toNat, 56) ∈ H
  owned3 : (t3.toNat, 56) ∈ H

/-- A fresh page table's slots are apart from the ref tables. -/
theorem RefTablesPre.at {H : List (Nat × Nat)} {m : Std.ExtHashMap Nat (BitVec 8)} {t1 t2 t3 ent : BitVec 64}
    (R : RefTablesPre H m t1 t2 t3) (fresh : FreshBlock vsaLayoutP H ent.toNat 16384) :
    RefTablesAt ((ent.toNat, 16384) :: H) ent m t1 t2 t3 := by
  have apart (t : BitVec 64) (owned : (t.toNat, 56) ∈ H) : t.toNat + 56 ≤ ent.toNat ∨ ent.toNat + 16384 ≤ t.toNat := by
    have a := fresh.2.2.2 _ owned
    rcases Nat.lt_or_ge t.toNat ent.toNat with h | h
    · rcases Nat.lt_or_ge (t.toNat + 55) ent.toNat with h' | h'
      · exact Or.inl (by omega)
      · exact absurd (show InExt (t.toNat, 56) ent.toNat by unfold InExt; dsimp only; omega)
          (a ent.toNat (by unfold InExt; dsimp only; omega))
    · rcases Nat.lt_or_ge t.toNat (ent.toNat + 16384) with h' | h'
      · exact absurd (show InExt (t.toNat, 56) t.toNat by unfold InExt; dsimp only; omega)
          (a t.toNat (by unfold InExt; dsimp only; omega))
      · exact Or.inr h'
  exact ⟨R.ptr1, R.ptr2, R.ptr3, R.spot1, R.spot2, R.spot3, R.empty1, R.empty2, R.empty3, R.apart12, R.apart23,
    R.domain1, R.apart13, R.domain2, R.domain3, apart _ R.owned1, apart _ R.owned2, apart _ R.owned3,
    List.mem_cons_of_mem _ R.owned1, List.mem_cons_of_mem _ R.owned2, List.mem_cons_of_mem _ R.owned3⟩

end OCaml.Vm.Boot.Startup
