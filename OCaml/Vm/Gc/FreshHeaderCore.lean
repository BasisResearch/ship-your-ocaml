import OCaml.Vm.Gc.FreshAllocated
import OCaml.Vm.Gc.FreshQueueCore

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives

/-- Original header size and tag after either allocator's exact wrapper log. -/
theorem header_of_wrapper_effect {R hp log size tag before after}
    (memory : after.σ.mem = writeLog (oldifySnapshot R before).σ.mem
      (AllocWrapperCore.effect (allocatorRegs R before) hp log (oldifySnapshot R before)))
    (windows : AllocEntry.Windows (allocatorRegs R before))
    (tagOutside : OutLRange log
      (AllocEntry.frameSp (allocatorRegs R before) + BitVec.ofNat 64 AllocEntry.tagOffset).toNat 8)
    (source : HeaderOk (word before (R 10 - 8#64).toNat) size tag)
    (separate : hp.toNat + 8 ≤ Layout.sym_caml_allocated_words ∨ Layout.sym_caml_allocated_words + 8 ≤ hp.toNat) :
    HeaderOk (word after hp.toNat) size tag := by
  have sizeBound : (allocatorRegs R before 10).toNat < 2^54 := by
    have bound := allocator_size R before
    change (allocatorRegs R before 10).toNat ≤ 18014398509481983 at bound
    omega
  have sizeEq : (allocatorRegs R before 10).toNat = size := by
    change (sizeWord (word before (R 10 - 8#64).toNat)).toNat = size
    exact (sizeWord_nat _).trans source.2
  have tagEq : (allocatorRegs R before 11).toNat = tag := by
    change (tagWord (word before (R 10 - 8#64).toNat)).toNat = tag
    exact (tagWord_nat _).trans source.1
  have tagBound : (allocatorRegs R before 11).toNat < 256 := by
    rw [tagEq]
    have h := source.1
    have bound := Nat.mod_lt (word before (R 10 - 8#64).toNat).toNat (by decide : 0 < 256)
    omega
  have header := AllocWrapperCore.header_of_effect memory windows tagOutside sizeBound separate tagBound
  simpa only [sizeEq,tagEq] using header

/-- A later finite write log preserves a typed header outside its footprint. -/
theorem header_of_suffix {before after : Config} {log : List WEntry} {a size tag : Nat}
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (header : HeaderOk (word before a) size tag) (outside : OutLRange log a 8) :
    HeaderOk (word after a) size tag := by
  have same : word after a = word before a := by
    rw [word,memory,bytesT_writeLog_out _ outside]
    rfl
  rw [same]
  exact header

/-- Queue writes preserve a typed header outside their finite footprint. -/
theorem QueueResult.header {R target log qs pl before after size tag} {hp : BitVec 64}
    (post : QueueResult R target log qs pl before after)
    (header : HeaderOk (word (queueSnapshot R log before) hp.toNat) size tag)
    (outside : OutLRange (queueEffect R target log qs before) hp.toNat 8) :
    HeaderOk (word after hp.toNat) size tag := by
  apply header_of_suffix ?_ header outside
  simp only [queueSnapshot,post.memory,writeLog_append]

end OCaml.Vm.Gc.Fresh
