import OCaml.Vm.Primitives.StringNursery

namespace OCaml.Vm.Primitives.StringAllocation
open Vsa.Machine Vsa.Sim

/-- Nursery metadata observed before entering the constructor. -/
structure NurseryMetadata (domain young limit : BitVec 64) (c : Config) : Prop where
  domainValue : word c DoubleAllocation.domainGlobal.toNat = domain
  youngValue : word c (DoubleAllocation.youngSlot domain).toNat = young
  limitValue : word c (DoubleAllocation.limitSlot domain).toNat = limit

/-- A caller's preceding writes avoid the three nursery metadata words. -/
structure MetadataOutside (log : List WEntry) (domain : BitVec 64) : Prop where
  domainSlot : OutLRange log DoubleAllocation.domainGlobal.toNat 8
  young : OutLRange log (DoubleAllocation.youngSlot domain).toNat 8
  limit : OutLRange log (DoubleAllocation.limitSlot domain).toNat 8

/-- Transport entry metadata across a library observation and caller stores. -/
theorem NurseryMetadata.frame_observedLog {domain young limit c after log}
    (h : NurseryMetadata domain young limit c) (outside : MetadataOutside log domain)
    (memory : Vsa.Densify.MemEqv after.σ.mem (writeLog c.σ.mem log)) :
    NurseryMetadata domain young limit after := by
  have wordFrame : ∀ a, OutLRange log a 8 → word after a = word c a := by
    intro a out
    exact (Vsa.Sim.Boot.bytesT_memEqv memory a 8).trans (bytesT_writeLog_out _ out)
  exact ⟨(wordFrame _ outside.domainSlot).trans h.domainValue,
    (wordFrame _ outside.young).trans h.youngValue,
    (wordFrame _ outside.limit).trans h.limitValue⟩

/-- Disjoint stack, nursery and metadata cells supply every intermediate
readback required by the generated string constructor. -/
structure NurserySeparation (ra sp length domain young : BitVec 64) : Prop where
  stackDomain : OutLRange (savedRaLog sp ra) DoubleAllocation.domainGlobal.toNat 8
  stackYoung : OutLRange (savedRaLog sp ra) (DoubleAllocation.youngSlot domain).toNat 8
  stackLimit : OutLRange (savedRaLog sp ra) (DoubleAllocation.limitSlot domain).toNat 8
  reserveDomain : OutLRange (reservationLog domain young (stringSpan length)) DoubleAllocation.domainGlobal.toNat 8
  headerDomain : OutLRange
    [((nurseryHeader young length).toNat, 8, (stringWords length <<< 10) + 252#64)]
    DoubleAllocation.domainGlobal.toNat 8
  headerYoung : OutLRange
    [((nurseryHeader young length).toNat, 8, (stringWords length <<< 10) + 252#64)]
    (DoubleAllocation.youngSlot domain).toNat 8
  savedRa : OutLRange (reservationLog domain young (stringSpan length) ++
    initializationLog (reservedRegisters ra sp length (nurseryHeader young length)) (nurseryHeader young length))
    (sp - 8#64).toNat 8

/-- Discharge all post-store reads from ordinary entry metadata and separation;
no execution or intermediate machine state is assumed. -/
theorem nursery_readback {ra sp length domain young limit c}
    (metadata : NurseryMetadata domain young limit c)
    (separate : NurserySeparation ra sp length domain young) :
    NurseryReadback ra sp length domain young limit c := by
  constructor
  · rw [bytesT_writeLog_out _ separate.stackDomain]
    exact metadata.domainValue
  · rw [bytesT_writeLog_out _ separate.stackYoung]
    exact metadata.youngValue
  · rw [bytesT_writeLog_out _ separate.stackLimit]
    exact metadata.limitValue
  · rw [writeLog_append, bytesT_writeLog_out _ separate.headerDomain,
      writeLog_append, bytesT_writeLog_out _ separate.reserveDomain,
      bytesT_writeLog_out _ separate.stackDomain]
    exact metadata.domainValue
  · rw [writeLog_append, bytesT_writeLog_out _ separate.headerYoung, writeLog_append]
    exact word_writeLog _ _ _
  · rw [constructorLog, List.append_assoc, writeLog_append,
      bytesT_writeLog_out _ separate.savedRa]
    exact savedRa_value c sp ra

end OCaml.Vm.Primitives.StringAllocation
