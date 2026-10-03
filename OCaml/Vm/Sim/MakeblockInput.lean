import OCaml.Vm.Sim.MakeblockRestore
import OCaml.Vm.Sim.MakeblockArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Natural-address nursery facts for fixed or variable block constructors.
Payload separation covers operand and source-stack reads after every prefix. -/
structure MakeblockInput (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high count tag a domain limit : Nat) (accu : BitVec 64) : Prop
    extends MakeblockWriteOk P s c pl cp sp high count tag a domain accu where
  domainValue : word c Layout.sym_Caml_state = BitVec.ofNat 64 domain
  youngValue : word c (domain + Layout.off_young_ptr) = BitVec.ofNat 64 (a + 8 * count)
  limitValue : word c (domain + Layout.off_young_limit) = BitVec.ofNat 64 limit
  youngWrite : RamWriteAt (domain + Layout.off_young_ptr) 8
  limitRead : RamReadAt (domain + Layout.off_young_limit) 8
  headerWrite : RamWriteAt (a - 8) 8
  fieldWrites : ∀ i, i < count → RamWriteAt (a + 8 * i) 8
  reads : ∀ i, i < count - 1 → RamReadAt (sp + 8 * i) 8
  capacity : limit ≤ a - 8
  headerYoungOutside : OutLRange [(a - 8, 8, blockHeader count tag)] (domain + Layout.off_young_ptr) 8

/-- Stack separation can be selected by a bounded index rather than a named value. -/
theorem payload_stack_outside {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {log : List WEntry} {sp i : Nat} (outside : PayloadOutside log P s c pl cp sp) (bound : i < s.stack.length) :
    OutLRange log (sp + 8 * i) 8 :=
  outside.stack i s.stack[i] (List.getElem?_eq_getElem bound)

end OCaml.Vm.Sim
