import OCaml.Vm.Gc.ForwardingPrefix
import OCaml.Vm.Gc.SingleFieldForwardedReturn

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The three stores already resolve a self-pointer at the tail boundary. -/
theorem self_forwardedValue {q root c} (window : WriteWindow q.source 8)
    (self : child q root c = q.source) : forwardedValue q root c = q.target := by
  have view := forwarding_prefix (q := q) (root := root) (before := c)
    (after := forwardedSnapshot q root c) (pl := ⟨fun _ => none,0,0⟩) rfl
    (by have lower := window.lower; omega)
  simpa only [Reloc.Eqv.rawW,forwardedValue,self] using view.2

/-- A copied single-field self-cycle returns with its field pointing to the
copy, rather than to the old nursery address captured in the register. -/
theorem ForwardedReturned.self_value {q root sp before after}
    (post : ForwardedReturned q root sp before after) (window : WriteWindow q.source 8)
    (self : child q root before = q.source) : word after q.target.toNat = q.target :=
  post.value.trans (self_forwardedValue window self)

/-- Self-cycle execution, deriving the zero-header and forwarding word from
the actual parent prefix. Only access and native-bank separation are supplied. -/
theorem return_self {q root sp domain c} (input : Input q root c)
    (stack : gprGet c.σ 2 = some sp) (constants : GHolds c.σ Fresh.loopConstants)
    (even : ChildClassify.even (child q root c) = true)
    (range : YoungConditions q root domain c) (self : child q root c = q.source)
    (destination : WriteWindow q.target 8)
    (windows : ∀ off ∈ OldifyReturn.offsets, ReadWindow (sp + BitVec.ofNat 64 off) 8)
    (prefixOutside : ∀ off ∈ OldifyReturn.offsets,
      OutLRange (Enqueue.prefixLog q.source q.target root) (sp + BitVec.ofNat 64 off).toNat 8)
    (destinationOutside : ∀ off ∈ OldifyReturn.offsets,
      OutLRange [(q.target.toNat,8,q.target)] (sp + BitVec.ofNat 64 off).toNat 8)
    (aligned : (OldifyReturn.returnWord sp c).toNat % 4 = 0) :
    FnSummary pc (fun d => d = c)
      (fun after => ForwardedReturned q root sp c after ∧ word after q.target.toNat = q.target) := by
  have memory : (forwardedSnapshot q root c).σ.mem =
      writeLog c.σ.mem (Enqueue.prefixLog q.source q.target root) := rfl
  have view := forwarding_prefix (q := q) (pl := ⟨fun _ => none,0,0⟩) memory
    (by have lower := input.windows.source.lower; omega)
  have same := OldifyReturn.SavedSame.of_writeLog memory prefixOutside
  have resolved := self_forwardedValue input.windows.source self
  have conditions : ForwardedReturnConditions q root sp c :=
    { header := by simpa only [Reloc.Eqv.rawW,self] using view.1
      headerRead := by simpa only [self] using input.windows.header.read
      pointerRead := by simpa only [self] using input.windows.source.read
      rootWrite := destination
      windows := windows
      outside := by change ∀ off ∈ OldifyReturn.offsets,
                      OutLRange [(q.target.toNat,8,forwardedValue q root c)] (sp + BitVec.ofNat 64 off).toNat 8
                    simpa only [resolved] using destinationOutside
      aligned := by simpa only [same.returnWord] using aligned
      prefixOutside := prefixOutside }
  apply (return_young_forwarded input stack constants even range conditions).weaken (fun _ h => h)
  intro after returned
  exact ⟨returned,returned.self_value input.windows.source self⟩

end OCaml.Vm.Gc.SingleField
