import OCaml.Vm.Primitives.SmallFast
import OCaml.Vm.Primitives.LibraryEffects

namespace OCaml.Vm.Primitives.SmallAllocation
open Vsa.Machine Vsa.Sim

def entryRegisters (ra size tag : BitVec 64) : Nat → BitVec 64
  | 1 => ra | 10 => size | 11 => tag | _ => 0

def reservedRegisters (ra size tag header : BitVec 64) : Nat → BitVec 64
  | 1 => ra | 10 => size | 11 => tag | 14 => header | 17 => DoubleAllocation.domainGlobal | _ => 0

def nurseryHeader (young size : BitVec 64) : BitVec 64 := young - 8#64 - (size <<< 3)

def constructorLog (ra size tag domain young : BitVec 64) : List WEntry :=
  StringAllocation.reservationLog domain young (size <<< 3) ++
    initializationLog (reservedRegisters ra size tag (nurseryHeader young size))

/-- Caller-supplied nursery space and static scalar memory observations for
G1 block allocation. The post-header observations follow from separation. -/
structure NurseryMemory (ra size tag domain young limit : BitVec 64) (c : Config) : Prop
    where
  domainValue : word c DoubleAllocation.domainGlobal.toNat = domain
  youngValue : word c (DoubleAllocation.youngSlot domain).toNat = young
  limitValue : word c (DoubleAllocation.limitSlot domain).toNat = limit
  youngWrite : WriteWindow (DoubleAllocation.youngSlot domain) 8
  limitRead : ReadWindow (DoubleAllocation.limitSlot domain) 8
  headerWrite : WriteWindow (nurseryHeader young size) 8
  room : guardB .BLTU (nurseryHeader young size) limit = false
  reserveImage : ImageOutside (StringAllocation.reservationLog domain young (size <<< 3))
  initializeImage : ImageOutside (initializationLog (reservedRegisters ra size tag (nurseryHeader young size)))
  domainAfterHeader : bytesT (writeLog c.σ.mem (constructorLog ra size tag domain young))
    DoubleAllocation.domainGlobal.toNat 8 = domain
  youngAfterHeader : bytesT (writeLog c.σ.mem (constructorLog ra size tag domain young))
    (DoubleAllocation.youngSlot domain).toNat 8 = nurseryHeader young size

/-- Dynamic entry facts are established by the generated call boundary. -/
structure NurseryInput (ra size tag domain young limit : BitVec 64) (c : Config) : Prop
    extends LeafInput ra c, NurseryMemory ra size tag domain young limit c where
  sizeReg : gpr c 10 = some size
  tagReg : gpr c 11 = some tag

structure NurseryPost (ra size tag domain young : BitVec 64) (before after : Config) : Prop extends
    WriteRegistersPost [6, 10, 12, 13, 14, 15, 16, 17]
      (constructorLog ra size tag domain young) before ra (nurseryHeader young size + 8#64)
      [(1, ra)] after where
  libraryGood : ∀ live, VsaIris.Inst.VsaOk live before → VsaIris.Inst.VsaOk live after

theorem alloc_small_nursery (c : Config) (ra size tag domain young limit : BitVec 64)
    (h : NurseryInput ra size tag domain young limit c) :
    FnSummary 0x8000c0b8#64 (fun d => d = c)
      (NurseryPost ra size tag domain young c) := by
  let R0 := entryRegisters ra size tag
  let R1 := reservedRegisters ra size tag (nurseryHeader young size)
  let bd := read8 c.σ.mem DoubleAllocation.domainGlobal.toNat
  let byoung := read8 c.σ.mem (DoubleAllocation.youngSlot domain).toNat
  let blimit := read8 c.σ.mem (DoubleAllocation.limitSlot domain).toNat
  have vd : bytesVal .ld bd = domain := (read8_value _ _).trans h.domainValue
  have vy : bytesVal .ld byoung = young := (read8_value _ _).trans h.youngValue
  have vl : bytesVal .ld blimit = limit := (read8_value _ _).trans h.limitValue
  have regs : GHolds c.σ (reserve_input R0) := ⟨h.raReg, h.sizeReg, h.tagReg, True.intro⟩
  have access := reserve_access c R0 bd byoung blimit
    (by rw [vd]; exact h.youngWrite) (by rw [vd]; exact h.limitRead)
    (read8_pins _ _) (by rw [vd]; exact read8_pins _ _) (by rw [vd]; exact read8_pins _ _)
  have S := reserve_fast c R0 bd byoung blimit h.toLeafInput regs access
    (by rw [vd, vy]; exact h.reserveImage) (by rw [vy, vl]; exact h.room)
  simp only [vd, vy, vl] at S
  apply summary_bind S (fun _ p => p.pc)
  intro reserved p
  have leaf : LeafInput ra reserved :=
    ⟨p.good, p.image, p.minstret,
      gholds_lookup _ p.regs (by simp [reserve_regs, R0, entryRegisters, lookupG]), h.aligned, p.tick⟩
  have regs' : GHolds reserved.σ (initialize_input R1) :=
    holds_project p.regs (by simp [initialize_input, R1, reservedRegisters, reserve_regs,
      R0, entryRegisters, lookupG, nurseryHeader, vy])
  let mHeader := writeLog reserved.σ.mem (initializationLog R1)
  let bd' := read8 mHeader DoubleAllocation.domainGlobal.toNat
  let byoung' := read8 mHeader (DoubleAllocation.youngSlot domain).toNat
  have memory : mHeader = writeLog c.σ.mem (constructorLog ra size tag domain young) := by
    dsimp only [mHeader]
    rw [p.memory, ← writeLog_append]
    rfl
  have vd' : bytesVal .ld bd' = domain := by
    rw [read8_value]
    change bytesT mHeader _ 8 = domain
    rw [memory]
    exact h.domainAfterHeader
  have vy' : bytesVal .ld byoung' = nurseryHeader young size := by
    rw [read8_value]
    change bytesT mHeader _ 8 = nurseryHeader young size
    rw [memory]
    exact h.youngAfterHeader
  have access' := initialize_access reserved R1 bd' byoung' h.headerWrite
    DoubleAllocation.domain_read (by rw [vd']; exact h.youngWrite.read)
    (read8_pins _ _) (by rw [vd']; exact read8_pins _ _)
  have T := initialize_fast reserved R1 bd' byoung' leaf regs' access' h.initializeImage
  simp only [vy'] at T
  apply T.weaken (fun _ eq => eq)
  intro after finish
  have effect := p.toEffectPost.trans finish.toEffectPost
  change EffectPost _ mHeader c ra _ after at effect
  rw [memory] at effect
  refine ⟨⟨effect.widen (by decide), ?_⟩, ?_⟩
  · exact ⟨gholds_lookup _ finish.regs (by simp [initialize_regs, R1, reservedRegisters, lookupG]), True.intro⟩
  · intro live good
    have good' := p.vsaOk good (by decide) (by simp [reserve_regs, keysG])
    exact finish.vsaOk good' (by decide) (by simp [initialize_regs, keysG])

end OCaml.Vm.Primitives.SmallAllocation
