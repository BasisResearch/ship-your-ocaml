import OCaml.Vm.Primitives.Uncaught.StdioReturned
import OCaml.Vm.Primitives.ExitPath.Context

/-!
# A function body's state between its prologue and epilogue

Inside a newlib stdio function (`_fclose_r`, `_fwalk_sglue`) the state at a
block boundary, relative to the state `b` after the prologue, is: the
exit-path invariant keeping the bytes of `keep` (`KeepCtx`), an aligned
`ra`, some registers pinned to values (`pins`, a `GHolds` list: `sp`, the
saved and loop registers), and some held as at `b` (`hold`). A generated
block (`Frame.step`), a direct call (`Frame.call`), a returned callee
(`Frame.returned`) and a `ret` leaf (`Frame.ret`) each preserve it.
-/

namespace OCaml.Vm.Primitives.Uncaught.StdioFrame
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives VsaIris.Inst
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of gpr_some gpr_some_of)
open OCaml.Vm.Primitives.ExitPath (KeepCtx ExitOk exitReads)
open OCaml.Vm.Primitives.Uncaught.StdioReturned

/-- Registers outside a list keep the list's values. -/
theorem gholds_keep {σ σ' : MState} :
    ∀ (L : GRegs), GHolds σ L → (∀ k ∈ keysG L, gprGet σ' k = gprGet σ k) → GHolds σ' L
  | [], _, _ => trivial
  | (k, _) :: L, ⟨h1, h2⟩, f =>
    ⟨(f k (by simp [keysG])).trans h1, gholds_keep L h2 fun k' hk => f k' (by simp [keysG, hk])⟩

/-- **A body's state** relative to `b`: the bytes of `keep` and the console as
at `b`, an aligned `ra`, the registers of `pins` at their values, those of
`hold` as at `b`. -/
structure Frame (b : Config) (keep : Nat → Prop) (pins : GRegs) (hold : Nat → Prop) (c : Config) : Prop where
  ctx : KeepCtx keep b c
  ra : ∃ r : BitVec 64, gprGet c.σ 1 = some r ∧ r.toNat % 4 = 0
  pinned : GHolds c.σ pins
  held : ∀ k, 1 ≤ k → k ≤ 31 → hold k → gprGet c.σ k = gprGet b.σ k
  gprs : GprsKept b c

/-- A log at or above `.rodata`'s end misses the image (as
`NamedRegister.imageOutside_of_rodata`, which sits in a heavier module). -/
theorem imageOutside_above {log : List WEntry} (above : ∀ e ∈ log, 0x80061fb0 ≤ e.1) : ImageOutside log := by
  have t : Image.textBase + Image.textSize ≤ 0x80061fb0 := by decide
  have r : Image.rodataBase + Image.rodataSize ≤ 0x80061fb0 := by decide
  have go (A n : Nat) (h : A + n ≤ 0x80061fb0) : OutLRange log A n := by
    induction log with
    | nil => trivial
    | cons e rest ih => exact ⟨.inl (Nat.le_trans h (above e (by simp))), ih fun e' he => above e' (by simp [he])⟩
  exact ⟨go _ _ t, go _ _ r⟩

namespace Frame
variable {b : Config} {keep : Nat → Prop} {pins : GRegs} {hold : Nat → Prop}

/-- The state right after the prologue. -/
theorem start {c : Config} (ok : ExitOk c) (image : ExecutableImage c)
    (minstret : ∃ v, c.σ.regs.get? Register.minstret = some v) (ra : ∃ r : BitVec 64, gprGet c.σ 1 = some r ∧ r.toNat % 4 = 0)
    (pinned : GHolds c.σ pins) : Frame c keep pins hold c :=
  ⟨KeepCtx.refl ok image minstret, ra, pinned, fun _ _ _ _ => rfl, GprsKept.refl _⟩

theorem pin {c : Config} (h : Frame b keep pins hold c) {n : Nat} {v : BitVec 64} (hn : lookupG n pins = some v) :
    gprGet c.σ n = some v :=
  gholds_lookup _ h.pinned hn

theorem leaf {c : Config} (h : Frame b keep pins hold c) : LeafInput (regsAt c 1) c := by
  obtain ⟨r, hr, al⟩ := h.ra
  rw [regsAt_of hr]; exact h.ctx.leaf hr al

theorem reg {c : Config} (h : Frame b keep pins hold c) (n : Nat) (hn : n ∈ exitReads) :
    gprGet c.σ n = some (regsAt c n) :=
  gpr_some (h.ctx.ok.present n hn)

/-- Fewer kept bytes. -/
theorem mono {keep' : Nat → Prop} {c : Config} (h : Frame b keep pins hold c) (sub : ∀ x, keep' x → keep x) :
    Frame b keep' pins hold c :=
  { h with ctx := h.ctx.mono sub }

/-- A generated block that writes no kept byte, neither `ra` nor a held
register, and leaves the pins `pins'`. -/
theorem stepTo {c d : Config} {writes : List Nat} {log : List WEntry} {pc value : BitVec 64} {regs pins' : GRegs}
    (h : Frame b keep pins hold c) (post : WriteRegistersPost writes log c pc value regs d)
    (out : ∀ x, keep x → OutL log x) (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs)
    (avoid : ∀ n ∈ writes, n ≠ 1 ∧ ¬hold n) (pinned : GHolds d.σ pins') : Frame b keep pins' hold d where
  ctx := h.ctx.step post out keys cover
  ra := by
    obtain ⟨r, hr, al⟩ := h.ra
    exact ⟨r, (post.toEffectPost.gpr_frame keys 1 (by decide) (by decide) fun m => (avoid 1 m).1 rfl).trans hr, al⟩
  pinned := pinned
  held k lo hi hk :=
    (post.toEffectPost.gpr_frame keys k lo hi fun m => (avoid k m).2 hk).trans (h.held k lo hi hk)
  gprs := h.gprs.trans post.kept

/-- A generated block that also leaves the pins alone. -/
theorem step {c d : Config} {writes : List Nat} {log : List WEntry} {pc value : BitVec 64} {regs : GRegs}
    (h : Frame b keep pins hold c) (post : WriteRegistersPost writes log c pc value regs d)
    (out : ∀ x, keep x → OutL log x) (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs)
    (avoid : ∀ n ∈ writes, n ≠ 1 ∧ ¬hold n) (pinsOk : ∀ n ∈ keysG pins, 1 ≤ n ∧ n ≤ 31 ∧ n ∉ writes) :
    Frame b keep pins hold d :=
  h.stepTo post out keys cover avoid (gholds_keep pins h.pinned fun k hk =>
    post.toEffectPost.gpr_frame keys k (pinsOk k hk).1 (pinsOk k hk).2.1 (pinsOk k hk).2.2)

/-- A direct call: only `ra` changes, to the aligned link. -/
theorem call {c d : Config} {target value link : BitVec 64} {regs : GRegs} (h : Frame b keep pins hold c)
    (post : RegistersPost [1] c.σ.mem c target value ((1, link) :: regs) d) (al : link.toNat % 4 = 0)
    (holdRa : ¬hold 1) (pinsOk : ∀ n ∈ keysG pins, 2 ≤ n ∧ n ≤ 31) : Frame b keep pins hold d where
  ctx := h.ctx.call post (by simp [keysG])
  ra := ⟨link, gholds_lookup _ post.regs (by simp [lookupG]), al⟩
  pinned := gholds_keep pins h.pinned fun k hk => post.toEffectPost.gpr_frame (by decide) k
    (by have := pinsOk k hk; omega) (pinsOk k hk).2 (by simp only [List.mem_singleton]; have := pinsOk k hk; omega)
  held k lo hi hk := (post.toEffectPost.gpr_frame (by decide) k lo hi (by
    simp only [List.mem_singleton]; rintro rfl; exact holdRa hk)).trans (h.held k lo hi hk)
  gprs := h.gprs.trans post.kept

/-- A returned callee that kept the bytes of `keep`, the pinned and the held registers. -/
theorem returned {c d : Config} {ra : BitVec 64} {K : Nat → Prop} (h : Frame b keep pins hold c)
    (r : Returned ra K c d) (al : ra.toNat % 4 = 0) (sub : ∀ x, keep x → K x)
    (pinsKept : ∀ n ∈ keysG pins, CalleeKept n) (holdKept : ∀ n, hold n → CalleeKept n) : Frame b keep pins hold d where
  ctx :=
    { ok := ⟨r.good, r.tick, r.htif.trans h.ctx.ok.htifIdle, fun n hn => by
        have bounds : 1 ≤ n ∧ n ≤ 31 := by simp [exitReads] at hn; omega
        exact r.gprs.present n bounds.1 bounds.2 (h.ctx.ok.present n hn)⟩
      image := r.image
      minstret := r.minstret
      output := r.output.trans h.ctx.output
      frame := fun x hx => (r.kept x (sub x hx)).trans (h.ctx.frame x hx) }
  ra := ⟨ra, r.raReg, al⟩
  pinned := gholds_keep pins h.pinned fun k hk => r.saved k (pinsKept k hk)
  held k lo hi hk := (r.saved k (holdKept k hk)).trans (h.held k lo hi hk)
  gprs := h.gprs.trans r.gprs

/-- A `ret` leaf (no writes) returns to `ra` in the same state. -/
theorem ret {c : Config} {t r : BitVec 64} {regs : GRegs} (h : Frame b keep pins hold c)
    (raReg : gprGet c.σ 1 = some r) (pinsOk : ∀ n ∈ keysG pins, 1 ≤ n ∧ n ≤ 31)
    (leaf : FnSummary t (fun d => d = c) (WriteRegistersPost [] [] c (regsAt c 1) (regsAt c 10) regs)) :
    FnSummary t (fun d => d = c) (fun d => Frame b keep pins hold d ∧ PCAt r d) :=
  leaf.weaken (fun _ e => e) fun _ p =>
    ⟨h.step p (fun _ _ => trivial) (by decide) (by simp) (by simp)
      (fun n hn => ⟨(pinsOk n hn).1, (pinsOk n hn).2, by simp⟩), by
      have := p.pc; rw [regsAt_of raReg] at this; exact this⟩

/-- A direct call whose callee returns to the link in the same state. -/
theorem callThen {c : Config} {call : CallInstr} (h : Frame b keep pins hold c) (shape : CallShape call)
    (decode : CallDecode call) (pins' : CallPins call c) (al : call.link.toNat % 4 = 0) (holdRa : ¬hold 1)
    (pinsOk : ∀ n ∈ keysG pins, 2 ≤ n ∧ n ≤ 31)
    (callee : ∀ d, Frame b keep pins hold d → gprGet d.σ 1 = some call.link →
      FnSummary call.target (fun e => e = d) (fun e => Frame b keep pins hold e ∧ PCAt call.link e)) :
    FnSummary call.pc (fun e => e = c) (fun e => Frame b keep pins hold e ∧ PCAt call.link e) := by
  apply summary_bind (call_registers_summary shape decode c pins' h.ctx.ok.good h.ctx.image h.ctx.ok.tick
    h.ctx.minstret [(10, regsAt c 10)] ⟨h.reg 10 (by decide), trivial⟩ (by change KeysOK [10]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl) (fun _ q => q.pc)
  intro d q
  exact callee d (h.call q al holdRa pinsOk) (gholds_lookup _ q.regs (by simp [lookupG]))

end Frame

/-- The `__retarget_lock_*_recursive` leaves (all `ret`). -/
theorem lockLeaf {b c : Config} {keep : Nat → Prop} {pins : GRegs} {hold : Nat → Prop} {r t : BitVec 64}
    (h : Frame b keep pins hold c) (raReg : gprGet c.σ 1 = some r) (pinsOk : ∀ n ∈ keysG pins, 1 ≤ n ∧ n ≤ 31)
    (leaf : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ [(1, R 1), (10, R 10)] →
      FnSummary t (fun d => d = c) (WriteRegistersPost [] [] c (R 1) (R 10) [(1, R 1), (10, R 10)])) :
    FnSummary t (fun d => d = c) (fun d => Frame b keep pins hold d ∧ PCAt r d) :=
  h.ret raReg pinsOk (leaf c (regsAt c) h.leaf ⟨h.reg 1 (by decide), h.reg 10 (by decide), trivial⟩)

/-- `__sfp_lock_acquire`/`__sfp_lock_release`: `a0` set to the global lock,
then a tail jump into the lock leaf. -/
theorem sfpTail {b c : Config} {keep : Nat → Prop} {pins : GRegs} {hold : Nat → Prop} {r e t v : BitVec 64}
    {regs : GRegs} (h : Frame b keep pins hold c) (raReg : gprGet c.σ 1 = some r)
    (pinsOk : ∀ n ∈ keysG pins, 1 ≤ n ∧ n ≤ 31 ∧ n ≠ 10) (hold10 : ¬hold 10)
    (enter : FnSummary e (fun d => d = c) (WriteRegistersPost [10] [] c t v regs)) (cover : 10 ∈ keysG regs)
    (leaf : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ [(1, R 1), (10, R 10)] →
      FnSummary t (fun d => d = c) (WriteRegistersPost [] [] c (R 1) (R 10) [(1, R 1), (10, R 10)])) :
    FnSummary e (fun d => d = c) (fun d => Frame b keep pins hold d ∧ PCAt r d) := by
  apply summary_bind enter (fun _ p => p.pc)
  intro d p
  exact lockLeaf (h.step p (fun _ _ => trivial) (by decide) (fun n hn => by simp at hn; subst hn; exact cover)
    (fun n hn => by simp at hn; subst hn; exact ⟨by decide, hold10⟩)
    (fun n hn => ⟨(pinsOk n hn).1, (pinsOk n hn).2.1, by simp; exact (pinsOk n hn).2.2⟩))
    ((p.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans raReg)
    (fun n hn => ⟨(pinsOk n hn).1, (pinsOk n hn).2.1⟩) leaf

end OCaml.Vm.Primitives.Uncaught.StdioFrame
