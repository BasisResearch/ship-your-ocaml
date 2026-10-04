import OCaml.Vm.Gc.FreshAllocated
import OCaml.Vm.Gc.FreshQueueCore

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives

/-- Typed size/tag agreement for any wrapper allocation whose argument
registers came from the source header. Entry and tail allocations share this
proof; the wrapper may choose different color bits for the new header. -/
theorem header_of_typed_wrapper {R hp log hd size tag before after}
    (memory : after.σ.mem = writeLog before.σ.mem (AllocWrapperCore.effect R hp log before))
    (windows : AllocEntry.Windows R)
    (tagOutside : OutLRange log (AllocEntry.frameSp R + BitVec.ofNat 64 AllocEntry.tagOffset).toNat 8)
    (source : HeaderOk hd size tag)
    (arguments : R 10 = sizeWord hd ∧ R 11 = tagWord hd)
    (separate : hp.toNat + 8 ≤ Layout.sym_caml_allocated_words ∨ Layout.sym_caml_allocated_words + 8 ≤ hp.toNat) :
    HeaderOk (word after hp.toNat) size tag := by
  have sizeBound : (R 10).toNat < 2^54 := by
    rw [arguments.1,sizeWord_nat]
    have bound := hd.isLt
    omega
  have tagBound : (R 11).toNat < 256 := by
    rw [arguments.2,tagWord_nat]
    exact Nat.mod_lt _ (by decide)
  have sizeEq : (R 10).toNat = size := by
    rw [arguments.1,sizeWord_nat]
    exact source.2
  have tagEq : (R 11).toNat = tag := by
    rw [arguments.2,tagWord_nat]
    exact source.1
  have header := AllocWrapperCore.header_of_effect memory windows tagOutside sizeBound separate tagBound
  simpa only [sizeEq,tagEq] using header

/-- Original first-entry interface, delegated to the shared typed-wrapper
law without changing its native-prologue or footprint premises. -/
theorem header_of_wrapper_effect {R hp log size tag before after}
    (memory : after.σ.mem = writeLog (oldifySnapshot R before).σ.mem
      (AllocWrapperCore.effect (allocatorRegs R before) hp log (oldifySnapshot R before)))
    (windows : AllocEntry.Windows (allocatorRegs R before))
    (tagOutside : OutLRange log
      (AllocEntry.frameSp (allocatorRegs R before) + BitVec.ofNat 64 AllocEntry.tagOffset).toNat 8)
    (source : HeaderOk (word before (R 10 - 8#64).toNat) size tag)
    (separate : hp.toNat + 8 ≤ Layout.sym_caml_allocated_words ∨ Layout.sym_caml_allocated_words + 8 ≤ hp.toNat) :
    HeaderOk (word after hp.toNat) size tag :=
  header_of_typed_wrapper memory windows tagOutside source ⟨rfl,rfl⟩ separate

/-- A bounded payload has the same header address in word and natural
arithmetic. The allocator's RAM window supplies the lower bound. -/
theorem header_address_of_lower {payload : BitVec 64} (lower : Layout.header_bytes ≤ payload.toNat) :
    (payload - BitVec.ofNat 64 Layout.header_bytes).toNat = payload.toNat - Layout.header_bytes := by
  have bound : (8#64) ≤ payload := lower
  simpa only [Layout.header_bytes,show (8#64).toNat = 8 from rfl] using BitVec.toNat_sub_of_le bound

/-- A bounded allocated header gives the natural header address of its
payload without modular wraparound. -/
theorem header_address_of_upper {hp : BitVec 64} (upper : hp.toNat + Layout.header_bytes < 2^64) :
    hp.toNat = (hp + BitVec.ofNat 64 Layout.header_bytes).toNat - Layout.header_bytes := by
  change hp.toNat + 8 < 2^64 at upper
  change hp.toNat = (hp + 8#64).toNat - 8
  simp only [BitVec.toNat_add,show (8#64).toNat = 8 from rfl,Nat.mod_eq_of_lt upper]
  omega

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
