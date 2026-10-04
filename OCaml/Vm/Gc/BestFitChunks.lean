import OCaml.Vm.Gc.BestFitAccess
import OCaml.Vm.Gc.ChainCompose

namespace OCaml.Vm.Gc.BestFitSmall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Shared read-only size check and nonnull list-head lookup. -/
theorem entry_access (mem : Std.ExtHashMap Nat (BitVec 8)) (ra size : BitVec 64)
    (b : List (BitVec 8)) (lds : List (List (BitVec 8)))
    (window : ReadWindow (slot size) 8) (pins : LPins8 mem (slot size).toNat b)
    (small : size.toNat ≤ Layout.bf_small_count) (nonnull : bytesVal .ld b ≠ 0) :
    ChainAccess mem (regs ra size) (b::lds) entryBlocks := by
  apply ChainAccess.cons ⟨size_access _ _ _ _,size_control _ _ _ small⟩
  rw [size_log,size_regs,size_loads]
  exact ChainAccess.cons ⟨list_access _ _ _ _ _ window pins,list_control _ _ _ _ nonnull⟩ ChainAccess.nil

/-- Shared nonempty-tail pop, accounting and native-return suffix. The
counter load pins are taken after the pop store, so either merge-cursor
branch can supply them by memory separation. -/
theorem pop_return_access (mem : Std.ExtHashMap Nat (BitVec 8))
    (ra size head cursor : BitVec 64) (bn bt : List (BitVec 8))
    (read : ReadWindow head 8) (write : WriteWindow (slot size) 8)
    (nextPins : LPins8 mem head.toNat bn)
    (counterPins : LPins8 (writeLog mem [((slot size).toNat,8,bytesVal .ld bn)])
      Layout.sym_caml_fl_cur_wsz bt)
    (nonnull : bytesVal .ld bn ≠ 0) (aligned : ra.toNat % 4 = 0) :
    ChainAccess mem (merged ra size head cursor) [bn,bt] popReturnBlocks := by
  apply ChainAccess.cons ⟨pop_access _ _ _ _ _ _ _ read write nextPins,
    pop_control _ _ _ _ _ _ nonnull⟩
  rw [pop_log,pop_regs,pop_loads]
  exact ChainAccess.cons ⟨return_access _ _ _ _ _ _ _ counterPins,
    return_control _ _ _ _ _ _ aligned⟩ ChainAccess.nil

end OCaml.Vm.Gc.BestFitSmall
