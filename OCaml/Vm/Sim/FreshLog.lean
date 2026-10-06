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
  /-- the stores miss the invocation's `external_raise` word -/
  external : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise) 8

/-- **One derivation for every allocation log.** -/
theorem FreshLogOk.of_windows {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} {ws : List W} {log : List WEntry} (g : ArmGeometry P s c pl cp high)
    (inside : LogInW ws log) (fresh : ∀ w ∈ ws, FreshWindow c high w) : FreshLogOk log P s c pl cp := by
  have n := g.nursery
  have lw : LogWindows log P s c pl cp high high [Layout.off_young_ptr] :=
    ⟨g.toStackGeometry, ⟨ws, inside, fun w hw => by
      rcases fresh w hw with ⟨lo, hi⟩ | ⟨lo, hi⟩ | rfl
      · exact .separated (n.toWindowSeparated.sub lo hi)
      · exact .belowStack lo hi
      · exact .field (List.mem_singleton_self _)⟩, Nat.le_refl _, by decide⟩
  refine ⟨lw.core (by decide), lw.domainField (by decide) (by decide),
    fun _ _ _ placed got => lw.objectOutside placed got, lw.image, lw.bindings, ?_,
    lw.domainField (by decide) (by decide)⟩
  · have ha := g.arena
    have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
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
