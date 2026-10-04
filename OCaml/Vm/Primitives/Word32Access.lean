import OCaml.Vm.Primitives.Write

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- Four total bytes for a scalar word load. -/
def read4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : List (BitVec 8) :=
  [(mem[a]?).getD 0,(mem[a+1]?).getD 0,(mem[a+2]?).getD 0,(mem[a+3]?).getD 0]

theorem read4_pins (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    LPins4 mem a (read4 mem a) := by simp [LPins4,read4]

/-- A signed 32-bit load has the same RAM/HTIF requirements as other scalar loads. -/
theorem ReadWindow.lw {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs}
    {a : MInstr} {x : BitVec 64} {bs : List (BitVec 8)} (h : ReadWindow x 4)
    (kind : a.kind = .lw) (address : eaddrM a L = x) (pins : LPins4 m x.toNat bs) :
    MemFacts m L bs a := by
  simp only [MemFacts,kind,address]
  refine ⟨⟨h.lower,h.upper,?_⟩,pins⟩
  simpa only [tohostAddr,LibraryLayout.tohostAddr,Layout.sym_tohost] using h.htif

/-- An aligned 32-bit store stays in RAM above the HTIF registers. -/
theorem WriteWindow.sw {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs}
    {a : MInstr} {x : BitVec 64} {bs : List (BitVec 8)} (h : WriteWindow x 4)
    (kind : a.kind = .sw) (address : eaddrM a L = x) : MemFacts m L bs a := by
  simp only [MemFacts,kind,address]
  refine ⟨h.lower,h.upper,?_,h.aligned⟩
  simpa only [tohostAddr,LibraryLayout.tohostAddr,Layout.sym_tohost] using h.htif

/-- Separated writes preserve a complete four-byte scalar load certificate. -/
theorem lpins4_writeLog {mem : Std.ExtHashMap Nat (BitVec 8)} {a : Nat}
    {bytes : List (BitVec 8)} {log : List WEntry}
    (pins : LPins4 mem a bytes) (outside : OutLRange log a 4) :
    LPins4 (writeLog mem log) a bytes := by
  have same (i : Nat) (bound : i < 4) :
      ((writeLog mem log)[a + i]?).getD 0 = (mem[a + i]?).getD 0 := by
    rw [writeLog_out _ _ _ (outL_of_range outside (by omega) (by omega))]
  simp only [LPins4] at pins ⊢
  simpa only [show ((writeLog mem log)[a]?).getD 0 = (mem[a]?).getD 0 from by
    simpa using same 0 (by decide),same 1 (by decide),same 2 (by decide),same 3 (by decide)] using pins

/-- A signed word load observes exactly the four-byte total word. -/
theorem read4_value (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    bytesVal .lw (read4 mem a) = Functions.sign_extend (m := 64) (bytesT mem a 4) := by
  rw [bytesT_four_eq]
  simp [bytesVal,read4,bytesT4]

/-- Read back one actual 32-bit store, including its truncation to low bits. -/
theorem word32_writeLog (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (value : BitVec 64) :
    bytesT (writeLog mem [(a,4,value)]) a 4 = value.setWidth 32 := by
  rw [bytesT_four_eq]
  change bytesT4 (writeMap4 mem a (swData value)) a = _
  simp [bytesT4,writeMap4,Std.ExtHashMap.getElem?_insert,Std.ExtHashMap.getElem_insert,swData]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  simp only [BitVec.extractLsb'_eq_self,Sail.BitVec.extractLsb,BitVec.extractLsb]
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb]
  simp

/-- Truncating a signed LW result recovers the original four-byte word. -/
theorem truncate_signed_word (value : BitVec 32) :
    (Functions.sign_extend (m := 64) value).setWidth 32 = value := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k bound
  simp [Functions.sign_extend,Sail.BitVec.signExtend,BitVec.getLsbD_setWidth,
    BitVec.getLsbD_signExtend,bound]
  omega

end OCaml.Vm.Primitives
