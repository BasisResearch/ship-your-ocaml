import OCaml.Vm.Primitives.DoubleAllocation
import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Primitives.Boundary

namespace OCaml.Vm.Primitives.DoubleAllocation
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- The allocator's nursery fast path, including separation of metadata reads
from its header write. The collector case is deliberately not assumed here. -/
structure FastInput (ra bits domain young limit : BitVec 64) (c : Config) : Prop
    extends LeafInput ra c where
  bitsReg : gpr c 10 = some bits
  domainValue : word c domainGlobal.toNat = domain
  youngValue : word c (youngSlot domain).toNat = young
  limitValue : word c (limitSlot domain).toNat = limit
  youngWrite : WriteWindow (youngSlot domain) 8
  limitRead : ReadWindow (limitSlot domain) 8
  headerWrite : WriteWindow (young - 16#64) 8
  dataWrite : WriteWindow (young - 16#64 + 8#64) 8
  room : guardB .BLTU (young - 16#64) limit = false
  reserveImage : ImageOutside (reserveLog domain young)
  initializeImage : ImageOutside (initializeLog (young - 16#64) (young - 16#64) bits)
  globalOutsideReserve : OutLRange (reserveLog domain young) domainGlobal.toNat 8
  globalOutsideHeader : OutLRange (headerLog (young - 16#64)) domainGlobal.toNat 8
  youngOutsideHeader : OutLRange (headerLog (young - 16#64)) (youngSlot domain).toNat 8

def allocationLog (domain young bits : BitVec 64) : List WEntry :=
  reserveLog domain young ++ initializeLog (young - 16#64) (young - 16#64) bits

def doubleWrites : List Nat := [10, 13, 14, 15, 16, 17]

theorem domain_read : ReadWindow domainGlobal 8 := by constructor <;> decide

/-- Both generated nursery blocks compose to an exact allocation write log. -/
theorem copy_double_fast (c : Config) (ra bits domain young limit : BitVec 64)
    (h : FastInput ra bits domain young limit c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_copy_double) (fun d => d = c)
      (WritePost doubleWrites (allocationLog domain young bits) c ra (young - 16#64 + 8#64)) := by
  let bd := read8 c.σ.mem domainGlobal.toNat
  let byoung := read8 c.σ.mem (youngSlot domain).toNat
  let blimit := read8 c.σ.mem (limitSlot domain).toNat
  have vd : bytesVal .ld bd = domain := (read8_value _ _).trans h.domainValue
  have vy : bytesVal .ld byoung = young := (read8_value _ _).trans h.youngValue
  have vl : bytesVal .ld blimit = limit := (read8_value _ _).trans h.limitValue
  have facts := reserve_facts c ra bits bd byoung blimit (loaded h.image) domain_read
    (by rw [vd]; exact h.youngWrite.read) (by rw [vd]; exact h.limitRead)
    (by rw [vd]; exact h.youngWrite) (read8_pins _ _)
    (by rw [vd]; exact read8_pins _ _) (by rw [vd]; exact read8_pins _ _)
  have S := reserve_summary c ra bits bd byoung blimit h.toLeafInput
    ⟨h.raReg, h.bitsReg, True.intro⟩ facts
    (by rw [vd, vy]; exact h.reserveImage) (by rw [vy, vl]; exact h.room)
  simp only [reserve_regs, vd, vy, vl] at S
  apply summary_bind S (fun _ p => p.pc)
  intro d p
  have leaf : LeafInput ra d :=
    ⟨p.good, p.image, p.minstret, gholds_lookup _ p.regs rfl, h.aligned, p.tick⟩
  have regs : GHolds d.σ [(1, ra), (15, young - 16#64), (16, domainGlobal), (17, bits)] :=
    holds_project p.regs (by simp [lookupG])
  let m := writeLog d.σ.mem (headerLog (young - 16#64))
  let bd' := read8 m domainGlobal.toNat
  let byoung' := read8 m (youngSlot domain).toNat
  have vd' : bytesVal .ld bd' = domain := by
    rw [read8_value, bytesT_writeLog_out _ h.globalOutsideHeader, p.memory,
      bytesT_writeLog_out _ h.globalOutsideReserve]
    exact h.domainValue
  have vy' : bytesVal .ld byoung' = young - 16#64 := by
    rw [read8_value, bytesT_writeLog_out _ h.youngOutsideHeader, p.memory]
    exact word_writeLog _ _ _
  have facts' := initialize_facts d ra (young - 16#64) bits bd' byoung' (loaded p.image)
    h.headerWrite domain_read (by rw [vd']; exact h.youngWrite.read)
    (by rw [vy']; exact h.dataWrite) (read8_pins _ _)
    (by rw [vd']; exact read8_pins _ _)
  have T := initialize_summary d ra (young - 16#64) bits bd' byoung' leaf regs facts'
    (by rw [vy']; exact h.initializeImage)
  simp only [initialize_regs, vd', vy'] at T
  apply T.weaken (fun _ he => he)
  intro after post
  have effect := p.toEffectPost.trans post.toEffectPost
  rw [p.memory, ← writeLog_append] at effect
  exact effect.widen (by decide)

end OCaml.Vm.Primitives.DoubleAllocation
