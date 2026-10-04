import OCaml.Vm.Gc.Generated.AllocAccount
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Gc.CodeFrame

namespace OCaml.Vm.Gc.AllocAccount
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def headerLog (R : Nat → BitVec 64) : List WEntry := [((R 10).toNat,8,R 11)]
def initialized (R : Nat → BitVec 64) (c : Config) := writeLog c.σ.mem (headerLog R)
def state (R : Nat → BitVec 64) (c : Config) := bytesT (initialized R c) Layout.sym_Caml_state 8
def thresholdAddr (R : Nat → BitVec 64) (c : Config) := state R c + BitVec.ofNat 64 Layout.off_minor_heap_wsz

def loads (R : Nat → BitVec 64) (c : Config) :=
  [read8 (initialized R c) Layout.sym_caml_allocated_words,
   read8 (initialized R c) Layout.sym_Caml_state,
   read8 (initialized R c) (thresholdAddr R c).toNat]
def counted (R : Nat → BitVec 64) (c : Config) :=
  bytesT (initialized R c) Layout.sym_caml_allocated_words 8 + 1#64 + R 8

theorem counter_window : WriteWindow (BitVec.ofNat 64 Layout.sym_caml_allocated_words) 8 := by
  constructor <;> decide

theorem state_window : ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 := by
  constructor <;> decide

theorem access (R : Nat → BitVec 64) (c : Config)
    (write : WriteWindow (R 10) 8) (read : ReadWindow (thresholdAddr R c) 8) :
    AccessPlan c.σ.mem (regs R) (loads R c) block.body := by
  simp only [block,caml_alloc_shr_for_minor_gcXb7ccFSeg,List.getD_cons_zero,AccessPlan]
  chain_facts True.intro
  · apply write.sd rfl ?_
    simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,Functions.sign_extend,Sail.BitVec.signExtend]
  · apply counter_window.read.ld rfl ?_ ?_
    · simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,eraseG,stepGM,wvalM,imm20Of,
        Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_caml_allocated_words]
    · simpa [loads,stepLdsM,writeLog,Layout.sym_caml_allocated_words,Layout.sym_Caml_state,initialized,headerLog,stepMemM,wentryM,eaddrM,widthOfM,regs,srcVal,lookupG,
        mkLine,decodeM,Functions.sign_extend,Sail.BitVec.signExtend] using
        (read8_pins (initialized R c) Layout.sym_caml_allocated_words)
  · apply state_window.ld rfl ?_ ?_
    · simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,eraseG,stepGM,wvalM,imm20Of,
        Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_Caml_state]
    · simpa [loads,stepLdsM,writeLog,Layout.sym_caml_allocated_words,Layout.sym_Caml_state,initialized,headerLog,stepMemM,wentryM,eaddrM,widthOfM,regs,srcVal,lookupG,
        mkLine,decodeM,Functions.sign_extend,Sail.BitVec.signExtend] using
        (read8_pins (initialized R c) Layout.sym_Caml_state)
  · apply read.ld rfl ?_ ?_
    · simp [eaddrM,mkLine,decodeM,regs,loads,thresholdAddr,state,srcVal,lookupG,eraseG,stepGM,stepLdsM,wvalM,
        Functions.sign_extend,Sail.BitVec.signExtend,Layout.off_minor_heap_wsz,read8_value]
    · simpa [loads,stepLdsM,writeLog,Layout.sym_caml_allocated_words,Layout.sym_Caml_state,initialized,headerLog,stepMemM,wentryM,eaddrM,widthOfM,regs,srcVal,lookupG,
        mkLine,decodeM,Functions.sign_extend,Sail.BitVec.signExtend] using
        (read8_pins (initialized R c) (thresholdAddr R c).toNat)
  · apply counter_window.sd rfl ?_
    simp [eaddrM,mkLine,decodeM,regs,srcVal,lookupG,eraseG,stepGM,wvalM,imm20Of,
      Functions.sign_extend,Sail.BitVec.signExtend,Layout.sym_caml_allocated_words]

end OCaml.Vm.Gc.AllocAccount
