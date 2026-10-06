import OCaml.Vm.Boot.Startup.ResolveSteps
import OCaml.Vm.Boot.Startup.ResolveName
import OCaml.Vm.Boot.Startup.HeapFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! htif.c's first `resolve("ocamlrun", r)`: `fs_init`, then the path names no
file, so `R_NONE`. -/

/-- `resolve`'s entry registers: `r` is `_open`'s frame, then the path and the
callee-saved registers. -/
def resolveEntry (spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64) : GRegs :=
  [(2, nativeStack spo 80), (1, ra), (10, path), (11, nativeStack spo 80), (8, s0), (9, s1), (18, s2), (19, s3),
    (20, s4), (21, s5), (22, s6), (23, s7), (24, s8), (25, s9)]

/-- `resolve`'s own stack pointer. -/
def resolveStack (spo : BitVec 64) : BitVec 64 := nativeStack (nativeStack spo 80) 96

/-- `resolve` after `fs_init` returns to it. -/
structure ResolveInit (H : List (Nat × Nat)) (capacity : Nat)
    (spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64) (before after : Config) where
  node : BitVec 64
  pc : PCAt jal_80000594_call.link after
  regs : GHolds after.σ [(2, resolveStack spo), (19, nativeStack spo 80), (25, path), (20, s4), (8, s0), (9, s1),
    (18, s2), (21, s5), (22, s6), (23, s7), (24, s8)]
  high : ∀ n, 26 ≤ n → n ≤ 27 → gprGet after.σ n = gprGet before.σ n
  ready : RuntimeReady ((node.toNat, 5) :: H) capacity (resolveStack spo) jal_80000594_call.link after
  embed : EmbedImage after
  slot : FsSlotOne after.σ.mem node
  rest : ∀ j, 2 ≤ j → j < 64 → slotUsed after.σ.mem (Layout.sym_files + 56 * j) = 0#8
  saved : ∀ off value, (off, value) ∈ resolveSlots ra s3 s4 s9 →
    bytesT after.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 = value
  live : ∀ e ∈ H, ∀ x, InExt e x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  above : ∀ x, (nativeStack spo 80).toNat ≤ x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

/-- `resolve`'s entry through `fs_init`. -/
theorem resolve_init (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64)
    (ready : RuntimeReady H (capacity + charge) (nativeStack spo 80) ra c)
    (frame : NativeFrame spo (80 + (96 + (96 + (64 + allocHeadroom)))))
    (deep : embedLimit + (80 + (96 + (96 + (64 + allocHeadroom)))) ≤ spo.toNat)
    (image : EmbedImage c) (regs : GHolds c.σ (resolveEntry spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9))
    (notReady : read4 c.σ.mem Layout.sym_fs_ready = [0#8, 0#8, 0#8, 0#8])
    (clear : ∀ j, 1 ≤ j → j < 64 → slotUsed c.σ.mem (Layout.sym_files + 56 * j) = 0#8)
    (charged : vsaChg 5 charge) :
    FnSummary 0x8000056c#64 (fun d => d = c)
      (fun after => Nonempty (ResolveInit H capacity spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have outer : NativeFrame (nativeStack spo 80) (96 + (96 + (64 + allocHeadroom))) :=
    frame.nested (front := 80) (by decide)
  have frameR := outer.resize (small := 96) (by unfold allocHeadroom; omega) (by decide)
  have frameF : NativeFrame (resolveStack spo) (96 + (64 + allocHeadroom)) := outer.nested (front := 96) (by decide)
  have outerNat := (frame.resize (small := 80) (by unfold allocHeadroom; omega) (by decide)).stack_nat
  have rNat := frameR.stack_nat
  have lower := frame.lower
  have entry (n : Nat) (v : BitVec 64) (hv : lookupG n (resolveEntry spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) = some v) :
      gprGet c.σ n = some v := gholds_lookup _ regs hv
  -- the prologue
  obtain ⟨d1, run1, p1⟩ := (resolve_entry c (nativeStack spo 80) ra s3 s4 s9 path (nativeStack spo 80)
    ready.toLeafInput frameR (gholds_select regs _ fun n v member => by
      simp only [resolveInput, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rfl) notReady).run c ⟨pc, rfl⟩
  have ready1 := ready.stack_log p1 (by decide) (by simp only [resolveEntered, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) ready.aligned frameR
    (resolveLog_inside frameR)
  -- the call to fs_init
  have callRegs : GHolds d1.σ [(19, nativeStack spo 80), (25, path), (2, resolveStack spo), (15, 0#64), (20, s4),
      (10, path), (11, nativeStack spo 80)] :=
    gholds_select p1.regs _ fun n v member => by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rfl
  obtain ⟨d2, run2, p2⟩ := (call_registers_summary jal_80000594_call_shape jal_80000594_call_decode d1
    (jal_80000594_call_pins ready1.image) p1.good ready1.image p1.tick p1.minstret _ callRegs
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl).run d1 ⟨p1.pc, rfl⟩
  have p2' : WriteRegistersPost [1] [] d1 jal_80000594_call.target path
      ((1, jal_80000594_call.link) :: [(19, nativeStack spo 80), (25, path), (2, resolveStack spo), (15, 0#64),
        (20, s4), (10, path), (11, nativeStack spo 80)]) d2 := p2
  have ready2 := ready1.stack_log p2' (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p2'.regs rfl) (gholds_lookup (n := 1) _ p2'.regs rfl) (by decide) frameF
    (by simp only [LogInW])
  have mem2 : d2.σ.mem = writeLog c.σ.mem (resolveLog (nativeStack spo 80) ra s3 s4 s9) :=
    (p2'.memory.trans (show writeLog d1.σ.mem [] = d1.σ.mem from rfl)).trans p1.memory
  have keep2 (x : Nat) (out : x < nativeFrameBase (nativeStack spo 80) 96 ∨ (nativeStack spo 80).toNat ≤ x) :
      (d2.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [mem2, frameOn_writeLog _ _ _ (resolveLog_inside frameR) x ⟨out, trivial⟩]
  have keepG (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out1 : n ∉ [19, 25, 2, 15]) (out2 : n ∉ [1])
      (hv : lookupG n (resolveEntry spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) = some v) : gprGet d2.σ n = some v :=
    (p2'.toEffectPost.gpr_frame (by decide) n lo hi out2).trans
      ((p1.toEffectPost.gpr_frame (by decide) n lo hi out1).trans (entry n v hv))
  have base : nativeFrameBase (nativeStack spo 80) 96 = spo.toNat - 80 - 96 := by
    unfold nativeFrameBase; rw [outerNat]; unfold nativeFrameBase; rfl
  obtain ⟨d3, run3, ⟨F⟩⟩ := (fs_init d2 H capacity charge (resolveStack spo) jal_80000594_call.link s0 s1 s2
    (nativeStack spo 80) s4 s5 s6 s7 s8 path path ready2 frameF
    (by unfold resolveStack; rw [rNat, base]; omega)
    (image.frame (EmbedFrame.stack mem2 (resolveLog_inside frameR) (by rw [outerNat]; unfold nativeFrameBase; omega)))
    ((gholds_append _ _).2 ⟨⟨gholds_lookup (n := 2) _ p2'.regs rfl, gholds_lookup (n := 19) _ p2'.regs rfl,
        keepG 22 s6 (by decide) (by decide) (by decide) (by decide) rfl,
        keepG 23 s7 (by decide) (by decide) (by decide) (by decide) rfl,
        gholds_lookup (n := 1) _ p2'.regs rfl, keepG 8 s0 (by decide) (by decide) (by decide) (by decide) rfl,
        gholds_lookup (n := 10) _ p2'.regs rfl, trivial⟩,
      ⟨keepG 9 s1 (by decide) (by decide) (by decide) (by decide) rfl,
        keepG 18 s2 (by decide) (by decide) (by decide) (by decide) rfl,
        gholds_lookup (n := 20) _ p2'.regs rfl, keepG 21 s5 (by decide) (by decide) (by decide) (by decide) rfl,
        keepG 24 s8 (by decide) (by decide) (by decide) (by decide) rfl, gholds_lookup (n := 25) _ p2'.regs rfl,
        trivial⟩⟩)
    (fun j lo hi => by
      unfold slotUsed
      rw [keep2 _ (Or.inl (by rw [base]; unfold Layout.sym_files heapEnd at *; omega))]
      exact clear j lo hi) charged).run d2 ⟨p2'.pc, rfl⟩
  refine ⟨d3, run1.trans (run2.trans run3), ⟨{
    node := F.node
    pc := F.pc
    regs := gholds_select F.regs _ fun n v member => by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    high := fun n lo hi => (F.high n lo hi).trans
      ((p2'.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega)).trans
      (p1.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega)))
    ready := F.ready
    embed := F.embed
    slot := F.slot
    rest := F.rest
    saved := fun off value member => by
      have range : 8 ≤ off ∧ off + 8 ≤ 96 := by
        simp only [resolveSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
        omega
      rw [word_observed (m := d2.σ.mem) _ (fun i hi => F.above _ (by
        unfold resolveStack; rw [rNat]; omega)), mem2]
      exact frameR.word_log_read (by
        intro k v hk
        simp only [resolveSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
        omega) (by simp [resolveSlots]) _ member
    live := fun e he x inside => by
      have bounds := ready.heap.block_bounds (q := e.1) (n := e.2) he
      unfold InExt at inside
      rw [F.live e he x (by unfold InExt; omega), keep2 x (Or.inl (by rw [base]; unfold heapEnd at *; omega))]
    above := fun x high => by
      rw [F.above x (by
        unfold resolveStack; rw [rNat, base]; have h' := high; rw [outerNat] at h'; unfold nativeFrameBase at h'; omega),
        keep2 x (Or.inr high)] }⟩⟩
end OCaml.Vm.Boot.Startup
