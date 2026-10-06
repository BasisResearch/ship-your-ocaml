import OCaml.Vm.Boot.Startup.StrdupMeasure
import OCaml.Vm.Boot.Startup.StrchrMiss
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-! The memory-neutral string leaves (`strlen`, `strchr(s, '/')`) from a ready
native caller: the call's result and readiness at its return. -/

structure StrlenReturned (H : List (Nat × Nat)) (capacity : Nat) (sp ra : BitVec 64) (len : Nat)
    (before after : Config) : Prop where
  post : StrlenCallPost startupLive ra len before after
  ready : RuntimeReady H capacity sp ra after

theorem strlen_ready (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (sp ra name : BitVec 64) (len : Nat)
    (ready : RuntimeReady H capacity sp ra c) (string : CBytes c.σ.mem name.toNat len)
    (argument : gprGet c.σ 10 = some name) :
    FnSummary 0x80042970#64 (fun d => d = c) (StrlenReturned H capacity sp ra len c) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have readOnly : ROHolds (vsaModel startupLive) c roR
      (snpText ++ dataOf c.σ.mem (List.range' name.toNat (len + 1))) := by
    refine ⟨ready.readOnly.1, ?_⟩
    intro p hp
    rcases List.mem_append.1 hp with snp | data
    · change (c.σ.mem[p.1]?).getD 0 = p.2
      rw [snp_text_loaded ready.image p snp]; rfl
    · obtain ⟨a, _, rfl⟩ := List.mem_map.1 data
      rfl
  obtain ⟨after, run, measured⟩ := (strlen_call c snp_text_live string.read ready.platform ready.image
    startup_image_live readOnly (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact argument)
    ready.raReg ready.aligned).run c ⟨pc, rfl⟩
  exact ⟨after, run, measured, ready.of_same_memory measured.toLeafInput measured.libraryGood measured.memory
    (measured.registers 3 (by decide) (by decide) (by decide))
    ((measured.registers 2 (by decide) (by decide) (by decide)).trans ready.stack)⟩

structure StrchrReturned (H : List (Nat × Nat)) (capacity : Nat) (sp ra : BitVec 64) (before after : Config) :
    Prop where
  done : StrchrMissDone ra before after
  ready : RuntimeReady H capacity sp ra after

theorem strchr_ready (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (sp ra a : BitVec 64) (len : Nat)
    (ready : RuntimeReady H capacity sp ra c) (regs : GHolds c.σ [(11, 47#64), (10, a)])
    (string : SlashString c.σ.mem a len) (plan : StrchrPlan c.σ.mem a len) :
    FnSummary 0x80040704#64 (fun d => d = c) (StrchrReturned H capacity sp ra c) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have present : GprPresent c.σ := ⟨fun n lo hi => ready.platform.gpr n lo (by omega)⟩
  obtain ⟨after, run, done⟩ := (strchr_miss c a ra len ready.toLeafInput
    ⟨regs.1, regs.2.1, ready.raReg, trivial⟩ present string plan).run c ⟨pc, rfl⟩
  have good : VsaOk startupLive after := by
    refine ⟨done.good, done.tick, fun n lo hi => done.present.get n lo (by omega), fun a ha => ?_, ?_⟩
    · rw [done.memory]; exact ready.platform.live a ha
    · rw [done.frame.regs _ (by decide) (by decide)]; exact ready.platform.htifIdle
  have gpFrame : gpr after 3 = gpr c 3 := done.frame.regs .x3 (by decide) (by decide)
  have spFrame : gprGet after.σ 2 = gprGet c.σ 2 := done.frame.regs .x2 (by decide) (by decide)
  exact ⟨after, run, done, ready.of_same_memory done.toLeafInput good
    (by rw [done.memory]; exact Vsa.Densify.MemEqv.refl _) gpFrame (spFrame.trans ready.stack)⟩
end OCaml.Vm.Boot.Startup
