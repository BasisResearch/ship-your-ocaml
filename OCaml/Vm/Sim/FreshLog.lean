import OCaml.Vm.Sim.AllocInput
import OCaml.Vm.Sim.VmLog

/-!
# Certificates for allocation logs that also write the VM stack

An allocating arm stores the young pointer, then initializes its block in the
free nursery; CLOSUREREC also pushes the function pointers into the VM stack
allocation, over the consumed captures. For any log whose windows are of
those three kinds (`FreshWindow`), `FreshLogOk.of_windows` derives every
separation fact the represented-state restoration needs from the arm
geometry, once: each target range is apart from the free nursery
(`NurseryGeometry`), from the VM stack allocation (`StackGeometry`) and from
the young-pointer word (the `Caml_state` record facts).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The young-pointer word of `Caml_state`. -/
def youngPtrW (c : Config) : W :=
  ⟨(word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr,
   (word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr + 8⟩

/-- An allocation write window: inside the free nursery, inside the VM stack
allocation, or the young-pointer word. -/
def FreshWindow (c : Config) (high : Nat) (w : W) : Prop :=
  ((runtimeFields c).youngLimit ≤ w.lo ∧ w.hi ≤ (runtimeFields c).youngPtr) ∨
    (high - Layout.stackBytes ≤ w.lo ∧ w.hi ≤ high) ∨ w = youngPtrW c

/-- Everything such a log leaves untouched. -/
structure FreshLogOk (log : List WEntry) (P : Prog) (s : St) (c : Config) (pl : Place)
    (cp : ChanPlace) : Prop where
  core : PayloadCoreOutside log P s c pl cp
  trap : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) 8
  heap : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o → ObjectOutside log a o
  image : ImageOutside log
  bindings : BindingsOutside log P c
  arena : LogInW [arenaWindow] log

/-- A range apart from the whole `Caml_state` record misses its young-pointer word. -/
theorem record_young {c : Config} {x n : Nat}
    (h : OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
      (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] x n) :
    OutWRange [youngPtrW c] x n := by
  have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  have h1 := h.1
  dsimp only at h1
  exact ⟨by simp only [youngPtrW]; omega, trivial⟩

/-- **One derivation for every allocation log.** -/
theorem FreshLogOk.of_windows {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} {ws : List W} {log : List WEntry} (g : ArmGeometry P s c pl cp high)
    (inside : LogInW ws log) (fresh : ∀ w ∈ ws, FreshWindow c high w) : FreshLogOk log P s c pl cp := by
  have n := g.nursery
  have hg := g.statics
  have hl := g.domainLow
  have hd := g.domain.1
  simp only [stackWindow] at hd
  have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  -- one target is apart from every window when it is apart from all three kinds
  have apart : ∀ x k, OutWRange [Gc.nurseryFree c] x k → OutWRange [stackWindow high] x k →
      OutWRange [youngPtrW c] x k → OutLRange log x k := by
    intro x k h1 h2 h3
    apply outLRange_of_windows inside
    apply outWRange_of_forall
    intro w hw
    have o1 := h1.1
    have o2 := h2.1
    have o3 := h3.1
    simp only [Gc.nurseryFree, stackWindow, youngPtrW] at o1 o2 o3
    rcases fresh w hw with ⟨lo, hi⟩ | ⟨lo, hi⟩ | rfl
    · omega
    · omega
    · simp only [youngPtrW]; omega
  have static : ∀ x k, x + k ≤ Layout.sym_bss_end → OutLRange log x k := fun x k hx =>
    apart x k (Gc.window_static n.statics hx) ⟨by simp only [stackWindow]; omega, trivial⟩
      ⟨by simp only [youngPtrW]; omega, trivial⟩
  -- a `Caml_state` field other than the young pointer
  have field : ∀ off, off + 8 ≤ Layout.domainStateBytes →
      (off + 8 ≤ Layout.off_young_ptr ∨ Layout.off_young_ptr + 8 ≤ off) →
      OutLRange log ((word c Layout.sym_Caml_state).toNat + off) 8 := fun off hoff hne =>
    apart _ 8 (Gc.outW_sub n.domain (by omega) (by omega))
      ⟨by simp only [stackWindow]; omega, trivial⟩ ⟨by simp only [youngPtrW]; omega, trivial⟩
  refine ⟨⟨static _ _ (by decide), field _ (by decide) (by decide), static _ _ (by decide),
      static _ _ (by decide), static _ _ (by decide), fun i w hw => ?_, fun id ch a hch hcp => ?_⟩,
    field _ (by decide) (by decide), fun l a o placed object => ?_,
    ⟨static _ _ (by decide), static _ _ (by decide)⟩,
    ⟨static _ _ (by decide), fun j name hj => ?_⟩, ?_⟩
  · have bound : i < P.code.size := by simpa using (Array.getElem?_eq_some_iff.mp hw).1
    have h2 := g.domainCode.1
    dsimp only at h2
    exact apart _ 4 (n.code i w hw) (g.code i w hw) ⟨by simp only [youngPtrW]; omega, trivial⟩
  · exact apart _ _ (n.channels id ch a hch hcp) (g.channels id ch a hch hcp)
      (record_young (g.domainChannels id ch a hch hcp))
  · have ho := n.heap l a o placed object
    have hs := g.heap l a o placed object
    have hr := record_young (g.domainHeap l a o placed object)
    exact ⟨apart _ 8 (Gc.outW_sub ho (by omega) (by omega)) (Gc.outW_sub hs (by omega) (by omega))
        (Gc.outW_sub hr (by omega) (by omega)),
      apart _ _ (Gc.outW_sub ho (by omega) (by omega)) (Gc.outW_sub hs (by omega) (by omega))
        (Gc.outW_sub hr (by omega) (by omega))⟩
  · exact apart _ 8 (n.primitives j name hj) (g.primitives j name hj) (record_young (g.domainPrims j name hj))
  · have ha := g.arena
    have hn := n.arena
    have hda := g.domainArena
    apply log_in_windows_of_mem
    intro e member
    apply insideW_arena _ (logInW_mem inside member)
    intro w hw
    rcases fresh w hw with ⟨-, hi⟩ | ⟨-, hi⟩ | rfl
    · omega
    · omega
    · simp only [youngPtrW]; omega

/-- The reservation's young-pointer store is a `FreshWindow` store. -/
theorem grabReserveLog_in (c : Config) (a : Nat) :
    LogInW [youngPtrW c] (grabReserveLog (word c Layout.sym_Caml_state).toNat a) :=
  ⟨Or.inl ⟨by simp only [youngPtrW]; omega, by simp only [youngPtrW]; omega⟩, trivial⟩

/-- A log in some windows lies in any list containing them. -/
theorem logInW_mono {ws ws' : List W} {log : List WEntry} (inside : LogInW ws log)
    (sub : ∀ w ∈ ws, w ∈ ws') : LogInW ws' log :=
  log_in_windows_of_mem fun e he => by
    have h := logInW_mem inside he
    clear inside he
    induction ws with
    | nil => exact False.elim h
    | cons w ws ih =>
      rcases h with here | tail
      · obtain ⟨l, r⟩ := here
        have mem := sub w (by simp)
        clear sub ih
        induction ws' with
        | nil => cases mem
        | cons w' ws' ih' =>
          rcases List.mem_cons.mp mem with rfl | mem
          · exact Or.inl ⟨l, r⟩
          · exact Or.inr (ih' mem)
      · exact ih (fun w' hw => sub w' (by simp [hw])) tail

/-- **The reservation summary of a log with a prefix**: the young pointer
moves to the header and the limit stays, when neither the prefix nor the
stores after the reservation touch `Caml_state`'s symbol or its two
allocation words. -/
theorem NurseryReserve.of_prefixed {c : Config} {a n : Nat} {pre log : List WEntry}
    (b : ReservedBlock c a n) (domainLow : Layout.sym_bss_end ≤ (word c Layout.sym_Caml_state).toNat)
    (preOut : ∀ x ∈ [Layout.sym_Caml_state, (word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr,
      (word c Layout.sym_Caml_state).toNat + Layout.off_young_limit], OutLRange pre x 8)
    (logOut : ∀ x ∈ [Layout.sym_Caml_state, (word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr,
      (word c Layout.sym_Caml_state).toNat + Layout.off_young_limit], OutLRange log x 8) :
    NurseryReserve c (pre ++ (grabReserveLog (word c Layout.sym_Caml_state).toNat a ++ log)) a n n := by
  have young := b.young
  have room := b.room
  refine ⟨young, Nat.le_refl _, room, by have := b.aligned; omega, b.capacity, fun c' memory => ?_⟩
  have hd : Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end := by decide
  have hy : Layout.off_young_ptr + 8 ≤ Layout.off_young_limit ∨ Layout.off_young_limit + 8 ≤ Layout.off_young_ptr := by decide
  let mem1 := writeLog c.σ.mem pre
  have dom1 : bytesT mem1 Layout.sym_Caml_state 8 = word c Layout.sym_Caml_state :=
    bytesT_writeLog_out _ (preOut _ (by simp))
  have whole : c'.σ.mem = writeLog mem1 (grabReserveLog (word c Layout.sym_Caml_state).toNat a ++ log) := by
    rw [memory, writeLog_append]
  have domainOut : OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a ++ log) Layout.sym_Caml_state 8 :=
    outLRange_append (grab_out (by omega)) (logOut _ (by simp))
  have dom' : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state := by
    change bytesT c'.σ.mem _ 8 = _
    rw [whole, bytesT_writeLog_out _ domainOut, dom1]
  have youngNew : word c' ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr) = BitVec.ofNat 64 (a - 8) := by
    change bytesT c'.σ.mem _ 8 = _
    rw [whole]
    exact Gc.word_writeLog_at _ _ 0 _ _ (by simp [grabReserveLog])
      (by simpa [grabReserveLog] using logOut _ (by simp))
  have limitKeep : word c' ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit) =
      word c ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit) := by
    change bytesT c'.σ.mem _ 8 = bytesT c.σ.mem _ 8
    rw [memory]
    exact bytesT_writeLog_out _ (outLRange_append (preOut _ (by simp))
      (outLRange_append (grab_out (by omega)) (logOut _ (by simp))))
  have top := b.top
  refine ⟨?_, ?_⟩
  · simp only [runtimeFields, domainWord, dom', youngNew, BitVec.toNat_ofNat]
    omega
  · simp only [runtimeFields, domainWord, dom', limitKeep]

end OCaml.Vm.Sim
