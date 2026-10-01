import OCaml.Vm.Primitives.StringWrapper
import OCaml.Vm.Primitives.StringEqualityContract

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable
open StringWrapper

abbrev WrapperEntry (c : Config) (ra sp x y : BitVec 64) :=
  WriteRegistersPost [2, 1] (savedRaLog sp ra) c call.target x
    [(1, call.link), (2, sp - 16#64), (10, x), (11, y)]

/-- The generated save block and full JAL bridge establish the callee interface. -/
theorem wrapper_enter (c : Config) (ra sp x y : BitVec 64) (h : LeafInput ra c)
    (hs : gpr c 2 = some sp) (hx : gpr c 10 = some x) (hy : gpr c 11 = some y)
    (window : WriteWindow (sp - 8#64) 8) (outside : ImageOutside (savedRaLog sp ra)) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_string_notequal) (fun d => d = c)
      (WrapperEntry c ra sp x y) := by
  apply summary_bind (save_summary c ra sp x y h hs hx hy window outside) (fun _ p => p.pc)
  intro d p
  have regs : GHolds d.σ [(2, sp - 16#64), (10, x), (11, y)] :=
    holds_project p.regs (by simp [lookupG])
  have S := call_registers_summary call_shape call_decode d (call_pins p.image)
    p.good p.image p.tick p.minstret _ regs (by change KeysOK [2, 10, 11]; decide)
    (by change ∀ n ∈ [2, 10, 11], n ≠ 1; decide) rfl
  apply S.weaken (fun _ h => h)
  intro after post
  have effect := p.toEffectPost.trans post.toEffectPost
  rw [p.memory] at effect
  exact ⟨effect, post.regs⟩

abbrev WrapperReturn (c : Config) (ra sp value : BitVec 64) :=
  WriteRegistersPost ([2, 1] ++ StringScan.scanWrites) (savedRaLog sp ra) c call.link value
    [(1, call.link), (2, sp - 16#64), (10, value)]

/-- Equality runs on the copied canonical strings while retaining the native
stack pointer and the link installed by JAL. -/
theorem wrapper_equal (c : Config) (ra sp : BitVec 64) (a b : Nat) (xs ys : List UInt8)
    (left : PaddedString c a xs) (right : PaddedString c b ys)
    (leftOutside : ObjectOutside (savedRaLog sp ra) a (.bytes xs))
    (rightOutside : ObjectOutside (savedRaLog sp ra) b (.bytes ys))
    (ga : StringGeometry a xs.length) (gb : StringGeometry b ys.length) :
    FnSummary call.target (WrapperEntry c ra sp (BitVec.ofNat 64 a) (BitVec.ofNat 64 b))
      (WrapperReturn c ra sp (tag64 (stringEqualityResult xs ys))) := by
  constructor
  intro d hd
  obtain ⟨pc, pre⟩ := hd
  have regs := pre.regs
  have leaf : LeafInput call.link d :=
    ⟨pre.good, pre.image, pre.minstret, gholds_lookup _ regs rfl, by decide, pre.tick⟩
  have l := left.frame_log leftOutside pre.memory
  have r := right.frame_log rightOutside pre.memory
  have S := StringScan.string_equal_machine d call.link a b xs.length ys.length leaf
    (gholds_lookup _ regs rfl) (gholds_lookup _ regs rfl) ga gb l.headerSize r.headerSize
  rw [string_comparison_value l r] at S
  have packed := S.weaken (fun _ h => h) (Post' := WrapperReturn c ra sp (tag64 (stringEqualityResult xs ys))) (by
    intro after post
    have effect := pre.toEffectPost.trans post
    rw [pre.memory] at effect
    refine ⟨effect, ?_⟩
    exact ⟨(post.frame _ (by decide) (by decide)).trans (gholds_lookup (n := 1) _ regs rfl),
      (post.frame _ (by decide) (by decide)).trans (gholds_lookup (n := 2) _ regs rfl), post.result, True.intro⟩)
  exact packed.run d ⟨by rw [← call_target]; exact pc, rfl⟩

def wrapperWrites : List Nat := [1, 2, 10, 11, 13, 14, 15]

/-- The generated suffix reloads the original return address and restores sp. -/
theorem wrapper_leave (c : Config) (ra sp value : BitVec 64)
    (window : WriteWindow (sp - 8#64) 8) (aligned : ra.toNat % 4 = 0) :
    Vsa.Logic.Triple (WrapperReturn c ra sp value)
      (WriteRegistersPost wrapperWrites (savedRaLog sp ra) c ra (4#64 - value)
        [(2, sp), (10, 4#64 - value), (15, 4#64), (1, ra)]) := by
  intro d pre
  have leaf : LeafInput call.link d :=
    ⟨pre.good, pre.image, pre.minstret, gholds_lookup _ pre.regs rfl, by decide, pre.tick⟩
  have saved : word d (sp - 8#64).toNat = ra := by
    change bytesT d.σ.mem _ 8 = ra
    rw [pre.memory]
    exact savedRa_value c sp ra
  have S := restore_summary d call.link ra sp value leaf
    (gholds_lookup _ pre.regs rfl) (gholds_lookup _ pre.regs rfl) window.read saved aligned
  have packed := S.weaken (fun _ h => h)
    (Post' := WriteRegistersPost wrapperWrites (savedRaLog sp ra) c ra (4#64 - value)
      [(2, sp), (10, 4#64 - value), (15, 4#64), (1, ra)]) (by
    intro after post
    have effect := pre.toEffectPost.trans post.toEffectPost
    rw [pre.memory] at effect
    exact ⟨effect.widen (by decide), post.regs⟩)
  exact packed.run d ⟨pre.pc, rfl⟩

/-- The complete native wrapper is a prefix/callee/suffix call splice. -/
theorem string_notequal_machine (c : Config) (ra sp : BitVec 64) (a b : Nat) (xs ys : List UInt8)
    (h : LeafInput ra c) (hs : gpr c 2 = some sp)
    (hx : gpr c 10 = some (BitVec.ofNat 64 a)) (hy : gpr c 11 = some (BitVec.ofNat 64 b))
    (window : WriteWindow (sp - 8#64) 8) (imageOutside : ImageOutside (savedRaLog sp ra))
    (left : PaddedString c a xs) (right : PaddedString c b ys)
    (leftOutside : ObjectOutside (savedRaLog sp ra) a (.bytes xs))
    (rightOutside : ObjectOutside (savedRaLog sp ra) b (.bytes ys))
    (ga : StringGeometry a xs.length) (gb : StringGeometry b ys.length) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_string_notequal) (fun d => d = c)
      (WriteRegistersPost wrapperWrites (savedRaLog sp ra) c ra
        (4#64 - tag64 (stringEqualityResult xs ys))
        [(2, sp), (10, 4#64 - tag64 (stringEqualityResult xs ys)), (15, 4#64), (1, ra)]) :=
  ⟨FnSummary.callSplice (wrapper_enter c ra sp _ _ h hs hx hy window imageOutside).run
    (wrapper_equal c ra sp a b xs ys left right leftOutside rightOutside ga gb)
    (wrapper_leave c ra sp _ window h.aligned) (fun _ p => ⟨p.pc, p⟩) (fun _ p => p)⟩

end OCaml.Vm.Primitives
