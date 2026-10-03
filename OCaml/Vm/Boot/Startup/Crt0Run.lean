import OCaml.Vm.Boot.Startup.GprPresence
import OCaml.Vm.Boot.Startup.ClearLoop

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

def bssWords : Nat := (Layout.sym_bss_end - Layout.sym_bss_start) / 8

theorem bss_region : ClearRegion Layout.sym_bss_start bssWords := by
  constructor <;> decide

theorem bss_end : Layout.sym_bss_start + 8 * bssWords = Layout.sym_bss_end := by decide

/-- The generated eight-instruction setup supplies the loop invariant. -/
theorem setup_clear {c d : Config} (h : CrtReady c)
    (post : BlockPost startX0000Seg 0x80000000#64 startX0000L [] c d) :
    ClearAt Layout.sym_bss_start bssWords 0 d d := by
  have hm : d.σ.mem = c.σ.mem := post.memory
  refine ⟨⟨post.good, ?_, post.tick⟩, Nat.zero_le _, post.pc, ?_, ?_, rfl, rfl, ?_⟩
  · rw [hm]; exact h.code
  · exact gholds_lookup _ post.regs (by rfl)
  · rw [bss_end]
    exact gholds_lookup _ post.regs (by rfl)
  · intro r _ _; rfl

/-- Argument-register setup immediately before crt0 calls main. -/
theorem args_input {c : Config} (h : CrtReady c) :
    BlockInput startX0030Seg 0x80000030#64 startX0030L [] c where
  good := h.good
  minstret := h.good.minstret
  regs := True.intro
  keys := by decide
  shape := by decide
  tick := h.tick
  facts := by chain_facts h.code with "Vsa.Sim.Code._start_at_"

structure CrtCallPost (initial c : Config) : Prop where
  gprs : GprPresent initial.σ → GprPresent c.σ
  ready : CrtReady c
  pc : PCAt 0x80000038#64 c
  memory : c.σ.mem = clearWords initial.σ.mem Layout.sym_bss_start bssWords
  stack : gprGet c.σ 2 = some (BitVec.ofNat 64 Layout.sym_stack_top)
  gp : gprGet c.σ 3 = some (BitVec.ofNat 64 Layout.sym_global_pointer)
  argc : gprGet c.σ 10 = some 0#64
  argv : gprGet c.σ 11 = some 0#64
  output : c.σ.sailOutput = initial.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [2, 3, 5, 6, 10, 11], (gprReg n == r) = false) →
    c.σ.regs.get? r = initial.σ.regs.get? r

/-- From `_start` to the `main` call site, for every embedded program.
The whole BSS loop uses one symbolic iteration and the total-correctness rule. -/
theorem crt0_to_call (initial : Config) (h : CrtReady initial) :
    FnSummary (BitVec.ofNat 64 Layout.sym_start) (fun c => c = initial)
      (CrtCallPost initial) := by
  constructor
  rintro c ⟨pc, rfl⟩
  obtain ⟨first, setup, a⟩ := (setup_summary c h).run c ⟨pc, rfl⟩
  obtain ⟨last, loop, b⟩ := clear_loop bss_region first first (setup_clear h a)
  have branch : guardB .BGEU (BitVec.ofNat 64 (Layout.sym_bss_start + 8 * bssWords))
      (BitVec.ofNat 64 (Layout.sym_bss_start + 8 * bssWords)) = true := by decide
  obtain ⟨exit, guard, g⟩ := (guard_summary last _ _ true b.ready b.cursor b.limit branch).run last ⟨b.pc, rfl⟩
  obtain ⟨d, args, p⟩ := (block_summary _ _ _ _ exit (args_input g.ready)).run exit ⟨g.pc, rfl⟩
  have ma : first.σ.mem = c.σ.mem := a.memory
  have mp : d.σ.mem = exit.σ.mem := p.memory
  have code : Code._startLoaded d.σ.mem := by rw [mp]; exact g.ready.code
  refine ⟨d, setup.trans (loop.trans (guard.trans args)),
    ⟨?_, ⟨p.good, code, p.tick⟩, p.pc, ?_, ?_, ?_, ?_, ?_,
      p.output.trans (g.output.trans (b.output.trans a.output)), ?_⟩⟩
  · intro beforePins
    have setupPins := BlockPost.gpr_present a beforePins (by decide) (by decide)
    have loopPins : GprPresent last.σ := by
      apply setupPins.of_frame (writes := [5]) (by decide)
      · intro n hn
        have eq : n = 5 := List.mem_singleton.mp hn
        subst n
        rw [b.cursor]; rfl
      · intro r noise outside
        apply b.frame r noise
        intro eq
        subst r
        have := outside 5 (by decide)
        contradiction
    have guardPins : GprPresent exit.σ := loopPins.of_frame (writes := [])
      (by decide) (by simp) (fun r noise _ => g.frame r noise)
    exact BlockPost.gpr_present p guardPins (by decide) (by decide)
  · rw [mp, g.memory, b.memory, ma]
  · have hr : gprGet first.σ 2 = some (BitVec.ofNat 64 Layout.sym_stack_top) :=
      gholds_lookup _ a.regs (by rfl)
    exact (p.frame .x2 (by decide) (by decide)).trans
      ((g.frame .x2 (by decide)).trans ((b.frame .x2 (by decide) (by decide)).trans hr))
  · have hr : gprGet first.σ 3 = some (BitVec.ofNat 64 Layout.sym_global_pointer) := gholds_lookup _ a.regs (by rfl)
    exact (p.frame .x3 (by decide) (by decide)).trans
      ((g.frame .x3 (by decide)).trans ((b.frame .x3 (by decide) (by decide)).trans hr))
  · exact gholds_lookup _ p.regs (by rfl)
  · exact gholds_lookup _ p.regs (by rfl)
  · intro r noise outside
    have x5 : r ≠ .x5 := by
      intro eq
      subst r
      have no := outside 5 (by decide)
      contradiction
    exact (p.frame_subset (writes := [2, 3, 5, 6, 10, 11]) (by decide) r noise outside).trans
      ((g.frame r noise).trans ((b.frame r noise x5).trans
        (a.frame_subset (writes := [2, 3, 5, 6, 10, 11]) (by decide) r noise outside)))

end OCaml.Vm.Boot.Startup
