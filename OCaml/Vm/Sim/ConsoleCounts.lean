import OCaml.Vm.Repr.ChannelCounts
import OCaml.Vm.Sim.PrimConsoleReturns

/-! Reference observations of the actual successful console semantics. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A successful OS write changes no channel records. -/
theorem writeFd_refs_same {w w' : World} {fd : Int} {bs : List UInt8}
    (ok : writeFd w fd bs = some w') : ChannelRefsSame w w' := by
  unfold writeFd at ok
  split at ok
  · cases ok
  · simp only [Option.bind_eq_bind] at ok
    cases call : osCall w.os (.write fd.toNat bs bs.length) with
    | none => rw [call] at ok; cases ok
    | some result =>
      rw [call, Option.bind_some] at ok
      split at ok
      · cases ok; exact .of_chans rfl
      · cases ok

/-- Successful flush retains the length and each refcount, including the
closed-channel no-op. Buffers, offsets and the OS may change. -/
theorem flushChan_refs_same {w w' : World} {id : Nat}
    (ok : flushChan w id = some w') : ChannelRefsSame w w' := by
  unfold flushChan at ok
  cases at_ : w.chans[id]? with
  | none => simp [at_] at ok
  | some ch =>
    simp only [at_, Option.bind_eq_bind, Option.bind_some] at ok
    split at ok
    · cases ok; exact .of_chans rfl
    · split at ok
      · cases ok
      · split at ok
        · cases ok
        · cases wr : writeFd w ch.fd ch.buf with
          | none => rw [wr] at ok; cases ok
          | some mid =>
            rw [wr, Option.bind_some] at ok
            cases ok
            have same := writeFd_refs_same wr
            exact (writeFd_refs_same wr).set_after at_ _ rfl

/-- The two actual put-character branches retain each reference count. -/
theorem putChar_refs_same {w w' : World} {id : Nat} {b : UInt8}
    (ok : putChar w id b = some w') : ChannelRefsSame w w' := by
  obtain ⟨ch, at_, _, _, branch⟩ := putChar_cases ok
  cases branch with
  | room _ => exact .set at_ rfl
  | full _ _ wr =>
    exact (writeFd_refs_same wr).set_after at_ _ rfl

/-- Every successful block-output iteration preserves length and per-id
refs; the recursion follows putBlock's fuel, including empty slices. -/
theorem putBlock_refs_same {w w' : World} {id fuel : Nat} {bs : List UInt8}
    (ok : putBlock w id bs fuel = some w') : ChannelRefsSame w w' := by
  induction fuel generalizing w bs with
  | zero =>
    cases bs with
    | nil => cases ok; exact .of_chans rfl
    | cons b bs => simp [putBlock] at ok
  | succ fuel ih =>
    cases bs with
    | nil => cases ok; exact .of_chans rfl
    | cons b bs =>
      rw [putBlock] at ok
      · cases at_ : w.chans[id]? with
        | none => simp [at_] at ok
        | some ch =>
          simp only [at_, Option.bind_eq_bind, Option.bind_some] at ok
          split at ok
          · cases ok
          · split at ok
            · cases ok; exact .set at_ rfl
            · split at ok
              · cases ok
              · cases wr : writeFd w ch.fd (ch.buf ++ (b :: bs).take (ioBufferSize - ch.buf.length)) with
                | none => rw [wr] at ok; cases ok
                | some mid =>
                  rw [wr, Option.bind_some] at ok
                  have tail := ih ok
                  exact ((writeFd_refs_same wr).set_after at_
                    {ch with buf := [], offset := ch.offset +
                      (ch.buf ++ (b :: bs).take (ioBufferSize - ch.buf.length)).length} rfl).trans tail
      · intro h; cases h

/-- The real unary flush return carries the reference observations. -/
theorem flush_primitive_refs_same {args : List Val} {h h' : Heap} {w w' : World} {v : Val}
    (sem : primF1Impl "caml_ml_flush" args h w = .ok v h' w') : ChannelRefsSame w w' := by
  rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [primF1Impl] at sem
  · obtain ⟨id, _, ok, _, _⟩ := flush_semantics sem
    exact flushChan_refs_same ok
  · simp [primF1Impl] at sem

/-- The real binary character-output return carries the same observations. -/
theorem output_char_primitive_refs_same {args : List Val} {h h' : Heap} {w w' : World} {v : Val}
    (sem : primF1Impl "caml_ml_output_char" args h w = .ok v h' w') : ChannelRefsSame w w' := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [primF1Impl] at sem
  · simp [primF1Impl] at sem
  · obtain ⟨id, n, _, _, ok, _, _⟩ := output_char_semantics sem
    exact putChar_refs_same ok
  · simp [primF1Impl] at sem

/-- Both real four-argument output returns, including every slice guard. -/
theorem output_primitive_refs_same {name : String} {args : List Val}
    {h h' : Heap} {w w' : World} {v : Val}
    (nameOk : name = "caml_ml_output" ∨ name = "caml_ml_output_bytes")
    (sem : primF1Impl name args h w = .ok v h' w') : ChannelRefsSame w w' := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨o, _ | ⟨n, _ | ⟨extra, rest⟩⟩⟩⟩⟩
  all_goals first
    | solve | rcases nameOk with rfl | rfl <;> simp [primF1Impl] at sem
    | obtain ⟨id, ch, oi, ni, bs, _, _, _, _, _, _, _, ok, _, _⟩ := output_semantics nameOk sem
      exact putBlock_refs_same ok

/-- Among all real implementation patterns, only the two output primitives
can successfully return four arguments. -/
theorem primF1Impl_four_name {name : String} {args : List Val} {h h' : Heap}
    {w w' : World} {v : Val} (len : args.length = 4)
    (sem : primF1Impl name args h w = .ok v h' w') :
    name = "caml_ml_output" ∨ name = "caml_ml_output_bytes" := by
  unfold primF1Impl at sem
  split at sem <;> simp_all

end OCaml.Vm.Sim
