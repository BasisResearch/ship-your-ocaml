import OCaml.Vm.Primitives.Named.Umoddi3
import OCaml.Vm.Sim.Udivdi3
import OCaml.Vm.Primitives.LibraryEffects

/-!
# `__umoddi3` as a call summary

libgcc's `__umoddi3(n, d)` saves `ra` in `t0`, calls `__udivdi3` (which
leaves the remainder in `a1`), moves it to `a0` and returns through `t0`.
The two generated blocks (`--ocaml-named`) and the proved division core
(`udivdi3_summary`) compose here. `ra` is clobbered (it holds the internal
link), so the post frames the integer registers outside
`[1, 5, 10, 11, 12, 13]`.
-/

namespace OCaml.Vm.Primitives.Named.Umoddi3
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Sim

/-- The registers `__umoddi3` may change. -/
def umodWrites : List Nat := [1, 5, 10, 11, 12, 13]

/-- **`__umoddi3` returned**: `a0 = n % d` at the caller's return address,
memory and output kept, the other integer registers kept. -/
structure UmodPost (before : Config) (ra value : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  pc : pcOf after = some ra
  result : gpr after 10 = some value
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ umodWrites → gprGet after.σ n = gprGet before.σ n
  htifIdle : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes

/-- A noise-and-writes register frame keeps every unwritten integer register. -/
theorem gpr_of_frame {before after : MState} {W : List Nat} (keys : KeysOK W)
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) → (∀ n ∈ W, (gprReg n == r) = false) →
      after.regs.get? r = before.regs.get? r)
    (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (out : n ∉ W) : gprGet after n = gprGet before n := by
  apply gprGet_of_frame n lower upper (VsaIris.Inst.gpr_avoids_noise n (by omega) lower) ?_ frame
  intro m hm
  have bounds := keys m hm
  exact gprReg_beq_false m (by omega) n (by omega) bounds.1 lower (fun e => out (e ▸ hm))

/-- **`__umoddi3(x, y)`** from a leaf call with a nonzero divisor. -/
theorem umoddi3_summary {c : Config} {x y ra : BitVec 64} (input : Udivdi3Input x y ra c) :
    FnSummary 0x800372e8#64 (fun d => d = c) (UmodPost c ra (x % y)) := by
  let R : Nat → BitVec 64 := fun k => (gprGet c.σ k).getD 0
  have r1 : R 1 = ra := by simp only [R, input.raReg]; rfl
  have r10 : R 10 = x := by simp only [R]; rw [show gprGet c.σ 10 = some x from input.left]; rfl
  have r11 : R 11 = y := by simp only [R]; rw [show gprGet c.σ 11 = some y from input.right]; rfl
  have regs : GHolds c.σ (save_input R) := by
    simp only [save_input, GHolds, r1, r10, r11]
    exact ⟨input.raReg, input.left, input.right, trivial⟩
  have leaf : LeafInput (R 1) c := by rw [r1]; exact input.toLeafInput
  apply summary_bind (save_fast c R leaf regs) (fun _ p => p.pc)
  intro c1 p1
  have args : GHolds c1.σ [(5, ra), (10, x), (11, y)] := by
    apply holds_project p1.regs
    simp [save_regs, r1, r10, r11, lookupG]
  have J := call_registers_summary save_call_shape save_call_decode c1 (save_call_pins p1.image)
    p1.good p1.image p1.tick p1.minstret _ args (by change KeysOK [5, 10, 11]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl
  apply summary_bind J (fun _ q => by rw [save_call_target] at q; exact q.pc)
  intro c2 p2
  have div : Udivdi3Input x y 0x800372f0#64 c2 :=
    { good := p2.good, image := p2.image, minstret := p2.minstret
      raReg := gholds_lookup _ p2.regs rfl, aligned := by decide, tick := p2.tick
      left := gholds_lookup _ p2.regs rfl, right := gholds_lookup _ p2.regs rfl
      nonzero := input.nonzero }
  apply summary_bind (udivdi3_summary div) (fun _ q => q.pc)
  intro c3 p3
  have t0 : gprGet c3.σ 5 = some ra :=
    (p3.frame Register.x5 (by decide)).trans (gholds_lookup (n := 5) _ p2.regs rfl)
  let R3 : Nat → BitVec 64 := fun k => if k = 5 then ra else x % y
  have regs3 : GHolds c3.σ (back_input R3) := by
    simp only [back_input, GHolds, R3]
    exact ⟨t0, p3.remainderReg, trivial⟩
  have B := back_summary c3 0x800372f0#64 R3 [] p3.toLeafInput regs3
    (by simp only [AccessPlan, back_body]; chain_facts True.intro) (by
      have tgt : srcVal 5 (runGM back_body (back_input R3) []) = ra := by
        rw [back_eval]; simp [back_regs, srcVal, lookupG, R3]
      simp only [TermFactsO, TermFactsT, back_term]
      rw [tgt, ret_tgt ra input.aligned]
      exact input.aligned)
  apply B.weaken (fun _ h => h)
  intro c4 p4
  have log4 : (evalBlocks back_blocks (SegEvalState.init (back_input R3) [])).log = [] := rfl
  have regs4 : (evalBlocks back_blocks (SegEvalState.init (back_input R3) [])).regs = back_regs R3 [] :=
    back_eval R3 []
  have memory : c4.σ.mem = c.σ.mem := by
    rw [p4.memory, log4, p3.memory, p2.memory, p1.memory]; rfl
  have frame3 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [10, 11, 12, 13] → gprGet c3.σ n = gprGet c2.σ n :=
    gpr_of_frame (by decide) fun r hn hw =>
      p3.frame r ⟨hw 10 (by decide), hw 11 (by decide), hw 12 (by decide), hw 13 (by decide),
        hn _ (by decide), hn _ (by decide), hn _ (by decide), hn _ (by decide), hn _ (by decide),
        hn _ (by decide), hn _ (by decide)⟩
  have frame4 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [10] → gprGet c4.σ n = gprGet c3.σ n :=
    gpr_of_frame (by decide) fun r hn hw => p4.frame r hn hw
  have reg10 : gprGet c4.σ 10 = some (x % y) := by
    apply gholds_lookup _ (regs4 ▸ p4.regs); simp [back_regs, lookupG, R3]
  exact
    { good := p4.good
      image := ⟨by simpa only [memory] using input.image.text, by simpa only [memory] using input.image.rodata⟩
      minstret := p4.minstret
      tick := p4.tick
      pc := by
        have tgt : srcVal 5 (runGM back_body (back_input R3) []) = ra := by
          rw [back_eval]; simp [back_regs, srcVal, lookupG, R3]
        change c4.σ.regs.get? Register.PC = _
        rw [p4.pc]
        change some (tgtPCT back_term (runGM back_body (back_input R3) [])) = some ra
        simp only [tgtPCT, back_term]
        rw [tgt, ret_tgt ra input.aligned]
      result := reg10
      memory := memory
      output := by rw [p4.output, p3.output, p2.output, p1.output]
      frame := fun n lo hi out => by
        simp only [umodWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
        exact (frame4 n lo hi (by simp; omega)).trans ((frame3 n lo hi (by simp; omega)).trans
          ((p2.gpr_frame (by decide) n lo hi (by simp; omega)).trans (p1.gpr_frame (by decide) n lo hi (by simp; omega))))
      htifIdle := by
        rw [p4.frame _ (by decide) (by decide), p3.frame _ (by decide),
          p2.frame _ (by decide) (by decide), p1.frame _ (by decide) (by decide)] }

end OCaml.Vm.Primitives.Named.Umoddi3
