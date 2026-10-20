import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Primitives.Read
import Vsa.Sim.WriteLogNF

/-! Bytes across a composed native run: every byte satisfying the accumulated
`keep` condition is unchanged. The memory counterpart of `GprsSame`: one
`MemSame` per step (a call's `kept`/`caller` field, a block's write log),
composed with `trans`, read with `word`. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Bytes satisfying `keep` agree between `before` and `after`. -/
structure MemSame (before after : Config) (keep : Nat → Prop) : Prop where
  same : ∀ x, keep x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem MemSame.of_eq {c d : Config} (h : d.σ.mem = c.σ.mem) : MemSame c d fun _ => True :=
  ⟨fun _ _ => by rw [h]⟩

/-- A block's write log: bytes outside it are unchanged. -/
theorem MemSame.of_log {c d : Config} {log : List WEntry} (h : d.σ.mem = writeLog c.σ.mem log) :
    MemSame c d (OutL log) :=
  ⟨fun x out => by rw [h, writeLog_out _ _ _ out]⟩

theorem MemSame.trans {c d e : Config} {P Q : Nat → Prop} (first : MemSame c d P) (second : MemSame d e Q) :
    MemSame c e fun x => P x ∧ Q x :=
  ⟨fun x h => (second.same x h.2).trans (first.same x h.1)⟩

theorem MemSame.mono {c d : Config} {P Q : Nat → Prop} (k : MemSame c d P) (h : ∀ x, Q x → P x) : MemSame c d Q :=
  ⟨fun x q => k.same x (h x q)⟩

/-- A word whose bytes are all kept. -/
theorem MemSame.word {c d : Config} {keep : Nat → Prop} (k : MemSame c d keep) {a : Nat}
    (h : ∀ i, i < 8 → keep (a + i)) : bytesT d.σ.mem a 8 = bytesT c.σ.mem a 8 :=
  word_observed _ fun i hi => k.same _ (h i hi)

end OCaml.Vm.Boot.Startup
