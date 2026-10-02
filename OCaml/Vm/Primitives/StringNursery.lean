import OCaml.Vm.Primitives.StringFast
import OCaml.Vm.Primitives.LibraryEffects

namespace OCaml.Vm.Primitives.StringAllocation
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- ABI values at the constructor's three generated boundaries. -/
def entryRegisters (ra sp length : BitVec 64) : Nat → BitVec 64
  | 1 => ra | 2 => sp | 10 => length | _ => 0

def preparedRegisters (ra sp length : BitVec 64) : Nat → BitVec 64
  | 1 => ra | 2 => sp - 48#64 | 10 => stringWords length
  | 14 => length | 15 => stringSpan length | _ => 0

def reservedRegisters (ra sp length header : BitVec 64) : Nat → BitVec 64
  | 1 => ra | 2 => sp - 48#64 | 10 => stringWords length | 13 => header
  | 14 => length | 15 => stringSpan length | 16 => DoubleAllocation.domainGlobal | _ => 0

def nurseryHeader (young length : BitVec 64) : BitVec 64 := young - 8#64 - stringSpan length

def constructorLog (ra sp length domain young : BitVec 64) : List WEntry :=
  savedRaLog sp ra ++ reservationLog domain young (stringSpan length) ++
    initializationLog (reservedRegisters ra sp length (nurseryHeader young length)) (nurseryHeader young length)

/-- Finite readback conditions over the constructor's first-order write log.
These describe only memory, never an execution. Stack/nursery/metadata
separation and the write-log frame lemmas supply them at call sites. -/
structure NurseryReadback (ra sp length domain young limit : BitVec 64) (c : Config) : Prop where
  domainValue : bytesT (writeLog c.σ.mem (savedRaLog sp ra)) DoubleAllocation.domainGlobal.toNat 8 = domain
  youngValue : bytesT (writeLog c.σ.mem (savedRaLog sp ra)) (DoubleAllocation.youngSlot domain).toNat 8 = young
  limitValue : bytesT (writeLog c.σ.mem (savedRaLog sp ra)) (DoubleAllocation.limitSlot domain).toNat 8 = limit
  domainAfterHeader : bytesT (writeLog c.σ.mem
    (savedRaLog sp ra ++ reservationLog domain young (stringSpan length) ++
      [((nurseryHeader young length).toNat, 8, (stringWords length <<< 10) + 252#64)]))
    DoubleAllocation.domainGlobal.toNat 8 = domain
  youngAfterHeader : bytesT (writeLog c.σ.mem
    (savedRaLog sp ra ++ reservationLog domain young (stringSpan length) ++
      [((nurseryHeader young length).toNat, 8, (stringWords length <<< 10) + 252#64)]))
    (DoubleAllocation.youngSlot domain).toNat 8 = nurseryHeader young length
  savedRaValue : bytesT (writeLog c.σ.mem (constructorLog ra sp length domain young)) (sp - 8#64).toNat 8 = ra

/-- Nursery geometry and input registers for a G1 string allocation. -/
structure NurseryInput (ra sp length domain young limit : BitVec 64) (c : Config) : Prop
    extends LeafInput ra c, NurseryReadback ra sp length domain young limit c where
  stackReg : gpr c 2 = some sp
  lengthReg : gpr c 10 = some length
  stackWrite : WriteWindow (sp - 8#64) 8
  youngWrite : WriteWindow (DoubleAllocation.youngSlot domain) 8
  limitRead : ReadWindow (DoubleAllocation.limitSlot domain) 8
  headerWrite : WriteWindow (nurseryHeader young length) 8
  lastWrite : WriteWindow (nurseryHeader young length + 8#64 + stringSpan length - 8#64) 8
  paddingWrite : WriteWindow (nurseryHeader young length + 8#64 + (stringSpan length - 1#64)) 1
  small : guardB .BLTU 256#64 (stringWords length) = false
  room : guardB .BLTU (nurseryHeader young length) limit = false
  stackImage : ImageOutside (savedRaLog sp ra)
  reserveImage : ImageOutside (reservationLog domain young (stringSpan length))
  initializeImage : ImageOutside
    (initializationLog (reservedRegisters ra sp length (nurseryHeader young length)) (nurseryHeader young length))

/-- Exact constructor effects together with preservation of library entry
well-formedness for any live-byte set supplied by the caller. -/
structure NurseryPost (ra sp length domain young : BitVec 64)
    (before after : Config) : Prop extends
    WriteRegistersPost [1, 2, 10, 11, 12, 13, 14, 15, 16, 17]
      (constructorLog ra sp length domain young) before ra
      (nurseryHeader young length + 8#64) [(2, sp)] after where
  libraryGood : ∀ live, VsaIris.Inst.VsaOk live before → VsaIris.Inst.VsaOk live after

/-- The successful nursery path is one machine function summary, with an
exact allocation log and restoration of the native stack pointer. -/
theorem alloc_string_nursery (c : Config) (ra sp length domain young limit : BitVec 64)
    (h : NurseryInput ra sp length domain young limit c) :
    FnSummary 0x8000c174#64 (fun d => d = c)
      (NurseryPost ra sp length domain young c) := by
  let R0 := entryRegisters ra sp length
  let R1 := preparedRegisters ra sp length
  let R2 := reservedRegisters ra sp length (nurseryHeader young length)
  have regs0 : GHolds c.σ (prepare_input R0) := ⟨h.raReg, h.stackReg, h.lengthReg, True.intro⟩
  have S := prepare_fast c R0 h.toLeafInput regs0 h.stackWrite h.stackImage h.small
  apply summary_bind S (fun _ p => p.pc)
  intro mid p
  have leaf : LeafInput ra mid :=
    ⟨p.good, p.image, p.minstret, gholds_lookup _ p.regs (by simp [prepare_regs, R0, entryRegisters, lookupG]),
      h.aligned, p.tick⟩
  have regs1 : GHolds mid.σ (reserve_input R1) :=
    holds_project p.regs (by simp [reserve_input, R1, preparedRegisters, prepare_regs, R0, entryRegisters, lookupG])
  let bd := read8 mid.σ.mem DoubleAllocation.domainGlobal.toNat
  let byoung := read8 mid.σ.mem (DoubleAllocation.youngSlot domain).toNat
  let blimit := read8 mid.σ.mem (DoubleAllocation.limitSlot domain).toNat
  have vd : bytesVal .ld bd = domain := by rw [read8_value, p.memory]; exact h.domainValue
  have vy : bytesVal .ld byoung = young := by rw [read8_value, p.memory]; exact h.youngValue
  have vl : bytesVal .ld blimit = limit := by rw [read8_value, p.memory]; exact h.limitValue
  have access := reserve_access mid R1 bd byoung blimit
    (by rw [vd]; exact h.youngWrite) (by rw [vd]; exact h.limitRead)
    (read8_pins _ _) (by rw [vd]; exact read8_pins _ _) (by rw [vd]; exact read8_pins _ _)
  have T := reserve_fast mid R1 bd byoung blimit leaf regs1 access
    (by rw [vd, vy]; exact h.reserveImage) (by rw [vy, vl]; exact h.room)
  simp only [vd, vy, vl] at T
  apply summary_bind T (fun _ q => q.pc)
  intro reserved q
  have memory : reserved.σ.mem = writeLog c.σ.mem
      (savedRaLog sp ra ++ reservationLog domain young (stringSpan length)) := by
    rw [q.memory, p.memory, ← writeLog_append]
    rfl
  have leaf' : LeafInput ra reserved :=
    ⟨q.good, q.image, q.minstret,
      gholds_lookup _ q.regs (by simp [reserve_regs, R1, preparedRegisters, lookupG]), h.aligned, q.tick⟩
  have regs2 : GHolds reserved.σ (initialize_input R2) :=
    holds_project q.regs (by simp [initialize_input, R2, reservedRegisters, reserve_regs,
      R1, preparedRegisters, lookupG, nurseryHeader, vy])
  let mHeader := writeLog reserved.σ.mem
    [((nurseryHeader young length).toNat, 8, (stringWords length <<< 10) + 252#64)]
  let bd' := read8 mHeader DoubleAllocation.domainGlobal.toNat
  let byoung' := read8 mHeader (DoubleAllocation.youngSlot domain).toNat
  have vd' : bytesVal .ld bd' = domain := by
    rw [read8_value]
    change bytesT mHeader _ 8 = domain
    dsimp only [mHeader]
    rw [memory, ← writeLog_append]
    exact h.domainAfterHeader
  have vy' : bytesVal .ld byoung' = nurseryHeader young length := by
    rw [read8_value]
    change bytesT mHeader _ 8 = nurseryHeader young length
    dsimp only [mHeader]
    rw [memory, ← writeLog_append]
    exact h.youngAfterHeader
  let mFinal := writeLog reserved.σ.mem (initializationLog R2 (nurseryHeader young length))
  let bra := read8 mFinal (sp - 8#64).toNat
  have vra : bytesVal .ld bra = ra := by
    rw [read8_value]
    change bytesT mFinal _ 8 = ra
    dsimp only [mFinal]
    rw [memory, ← writeLog_append]
    exact h.savedRaValue
  have access' := initialize_access reserved R2 bd' byoung' bra h.headerWrite
    DoubleAllocation.domain_read (by rw [vd']; exact h.youngWrite.read)
    (by rw [vy']; exact h.lastWrite) (by rw [vy']; exact h.paddingWrite)
    (by change ReadWindow (sp - 48#64 + 40#64) 8; rw [prepare_save_address]; exact h.stackWrite.read)
    (read8_pins _ _) (by rw [vd']; exact read8_pins _ _)
    (by rw [vy']; change LPins8 mFinal (sp - 48#64 + 40#64).toNat bra
        rw [prepare_save_address]; exact read8_pins _ _)
  have U := initialize_fast reserved R2 bd' byoung' bra leaf' regs2 access'
    (by rw [vy']; exact h.initializeImage) vra
  simp only [vy'] at U
  apply U.weaken (fun _ he => he)
  intro after finish
  have effect := (p.toEffectPost.trans q.toEffectPost).trans finish.toEffectPost
  rw [memory, ← writeLog_append] at effect
  have framed := effect.widen (writes' := [1, 2, 10, 11, 12, 13, 14, 15, 16, 17]) (by decide)
  have preserved : ∀ live, VsaIris.Inst.VsaOk live c → VsaIris.Inst.VsaOk live after := by
    intro live good
    have good1 := p.vsaOk good (by decide) (by simp [prepare_regs, keysG])
    have good2 := q.vsaOk good1 (by decide) (by simp [reserve_regs, keysG])
    exact finish.vsaOk good2 (by decide) (by simp [initialize_regs, keysG])
  refine ⟨⟨framed, ?_⟩, preserved⟩
  have spValue := gholds_lookup _ finish.regs (n := 2) rfl
  change gpr after 2 = some sp ∧ True
  constructor
  · have restore : sp - 48#64 + 48#64 = sp := by bv_omega
    change gprGet after.σ 2 = some sp
    simpa only [initialize_regs, R2, reservedRegisters, restore] using spValue
  · trivial

end OCaml.Vm.Primitives.StringAllocation
