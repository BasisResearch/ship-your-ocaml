import OCaml.Vm.Boot.Startup.BssReads
import OCaml.Vm.Primitives.Leaf
import Vsa.Sim.Boot.Bytes
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.Boot OCaml.Vm.Primitives

/-- Main also frames every byte before both of its stores. -/
theorem mainWrites_before (ra : BitVec 64) (env : List (BitVec 8)) (a : Nat)
    (lo : a < Layout.sym_environ) (hi : a < Layout.sym_stack_top - 8) :
    OutL (mainWrites ra env) a := ⟨Or.inl hi, Or.inl lo, True.intro⟩

theorem CrtCamlMainPost.memory_below {initial c : Config} (post : CrtCamlMainPost initial c)
    (a : Nat) (below : a < Layout.sym_bss_start)
    (outside : OutL (mainWrites 0x8000003c#64
      (read8 initial.σ.mem Layout.sym_embedded_env)) a) :
    c.σ.mem[a]? = initial.σ.mem[a]? := by
  rw [post.memory, writeLog_out _ _ _ outside, clearWords_below _ _ _ _ below]

theorem CrtCamlMainPost.bytes_below {initial c : Config} (post : CrtCamlMainPost initial c)
    (a w : Nat) (below : a + w ≤ Layout.sym_bss_start)
    (outside : ∀ i < w, OutL (mainWrites 0x8000003c#64
      (read8 initial.σ.mem Layout.sym_embedded_env)) (a + i)) :
    bytesT c.σ.mem a w = bytesT initial.σ.mem a w :=
  bytesT_local_eq a w (fun i hi => post.memory_below _ (by omega) (outside i hi))

/-- The actual startup effects preserve both immutable runtime sections. -/
theorem CrtCamlMainPost.image {initial c : Config} (post : CrtCamlMainPost initial c)
    (image : ExecutableImage initial) : ExecutableImage c := by
  constructor
  · apply image.text.transport
    intro a lo hi
    have bounds : Image.textBase + Image.textSize ≤ Layout.sym_bss_start ∧
        Image.textBase + Image.textSize ≤ Layout.sym_environ ∧
        Image.textBase + Image.textSize ≤ Layout.sym_stack_top - 8 := by decide
    exact post.memory_below a (by omega) (mainWrites_before _ _ a (by omega) (by omega))
  · apply image.rodata.transport
    intro a lo hi
    have bounds : Image.rodataBase + Image.rodataSize ≤ Layout.sym_bss_start ∧
        Image.rodataBase + Image.rodataSize ≤ Layout.sym_environ ∧
        Image.rodataBase + Image.rodataSize ≤ Layout.sym_stack_top - 8 := by decide
    exact post.memory_below a (by omega) (mainWrites_before _ _ a (by omega) (by omega))

theorem CrtCamlMainPost.leaf {initial c : Config} (post : CrtCamlMainPost initial c)
    (image : ExecutableImage initial) : LeafInput 0x80001df0#64 c :=
  ⟨post.good, post.image image, post.good.minstret, post.linkReg, by decide, post.tick⟩
end OCaml.Vm.Boot.Startup
