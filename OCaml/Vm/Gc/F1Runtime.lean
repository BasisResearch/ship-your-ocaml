import OCaml.Vm.Boot.WhileMinLoaded
import OCaml.Vm.Reloc
import OCaml.Vm.Primitives.Write
import OCaml.Vm.Primitives.Allocation
import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Sim.CheckSignals
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Gc.NurseryDefs
import OCaml.Vm.Primitives.ExitPath.Machine
import OCaml.Vm.Sim.NurseryInput

/-!
# The F1 runtime invariant, pinned at the cut

Under G1 no collection runs and nothing is allocated in the major heap after
the cut, so the best-fit free list, the `Caml_state` address and the VM stack
geometry keep their cut values. `F1Pins` fixes them; `f1Runtime := RuntimeOk
F1Pins` then reads only a fixed footprint (`f1Footprint`): `.bss`, the
`young_*` and stack fields of the domain record, and the free block.

* `f1_stable`: every window apart from the footprint is `WindowStable`.
  Corollaries: Caml_state fields outside the read ones (`f1_domainField`), the
  nursery (`f1_nursery`), the VM stack (`f1_stackWindow`).
* `f1_stackHigh`, `f1_threshold`, `f1_quiet`: the stack and signal facts the
  arms' `RuntimeFrame` takes.
* `f1_allocation`: `AllocationRuntime` for a log that only stores apart from
  the footprint, except `young_ptr`, which it lowers within the nursery.
* `whileMin_f1Pins`: the pins hold at the captured cut.
-/

namespace OCaml.Vm.Gc
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives Boot

/-- The cut's domain address, stack top and threshold. -/
def f1Domain : Nat := WhileMinRuntime.domain
def f1High : Nat := WhileMinEntry.high
def f1Threshold : Nat := f1High - Layout.stackBytes + Layout.stackThresholdBytes

/-- What G1 keeps fixed after the cut. -/
structure F1Pins (c : Config) : Prop where
  freeList : BestFitSingletonAt c WhileMinRuntime.freeBlock
  domain : word c Layout.sym_Caml_state = BitVec.ofNat 64 f1Domain
  stackHigh : word c (f1Domain + Layout.off_stack_high) = BitVec.ofNat 64 f1High
  threshold : word c (f1Domain + Layout.off_stack_threshold) = BitVec.ofNat 64 f1Threshold
  /-- the default exit path's four `.bss` globals (`caml_verb_gc`,
  `caml_cleanup_on_exit`, `__atexit`, `__stdio_exit_handler`) at their
  defaults: no F1 path writes them -/
  exit : ExitPath.ExitGlobals c
  /-- `caml_init_stack` puts `trap_barrier` one word above `stack_high`; G1 never moves it -/
  trapBarrier : word c (f1Domain + Layout.off_trap_barrier) = BitVec.ofNat 64 (f1High + 8)
  /-- no backtrace recording -/
  backtraceOff : word c (f1Domain + Layout.off_backtrace_active) = 0#64
  /-- no channel-mutex unlock hook (`caml_channel_mutex_unlock_exn`) -/
  channelUnlock : word c Layout.sym_caml_channel_mutex_unlock_exn = 0#64

/-- The F1 runtime invariant. -/
def f1Runtime : Config → Prop := RuntimeOk F1Pins

/-- The F1 layout. -/
def f1Layout : OCaml.Layout := runtimeLayout F1Pins g1Budget

/-- The memory `f1Runtime` reads, except the `young_ptr` word. -/
def keptFootprint : List W :=
  [⟨0, Layout.sym_caml_callback_depth⟩, ⟨Layout.sym_caml_callback_depth + 4, Layout.sym_bss_end⟩, ⟨f1Domain, f1Domain + Layout.off_young_ptr⟩,
   ⟨f1Domain + Layout.off_young_ptr + 8, f1Domain + 64⟩,
   ⟨f1Domain + Layout.off_stack_high, f1Domain + Layout.off_stack_threshold + 8⟩,
   ⟨f1Domain + Layout.off_trap_barrier, f1Domain + Layout.off_trap_barrier + 8⟩,
   ⟨f1Domain + Layout.off_backtrace_active, f1Domain + Layout.off_backtrace_active + 8⟩,
   ⟨WhileMinRuntime.freeBlock.block - 8,
    WhileMinRuntime.freeBlock.block + 8 * WhileMinRuntime.freeBlock.words⟩]

/-- The `young_ptr` word, which allocation moves. -/
def youngWord : W := ⟨f1Domain + Layout.off_young_ptr, f1Domain + Layout.off_young_ptr + 8⟩

/-- The memory `f1Runtime` reads. -/
def f1Footprint : List W := youngWord :: keptFootprint

/-- Two windows do not overlap. -/
def Apart (w v : W) : Prop := w.hi ≤ v.lo ∨ v.hi ≤ w.lo

/-- A range lies inside one footprint window. -/
def InFootprint (x n : Nat) : Prop := ∃ v ∈ f1Footprint, v.lo ≤ x ∧ x + n ≤ v.hi

/-- A range lies inside one kept footprint window. -/
def InKept (x n : Nat) : Prop := ∃ v ∈ keptFootprint, v.lo ≤ x ∧ x + n ≤ v.hi

theorem InKept.footprint {x n : Nat} (h : InKept x n) : InFootprint x n := by
  obtain ⟨v, member, low, high⟩ := h
  exact ⟨v, List.mem_cons_of_mem _ member, low, high⟩

theorem outW_of {ws : List W} {a : Nat} (h : ∀ w ∈ ws, a < w.lo ∨ w.hi ≤ a) : OutW ws a := by
  induction ws with
  | nil => trivial
  | cons w ws ih => exact ⟨h w (by simp), ih fun v hv => h v (by simp [hv])⟩

/-- Bytes inside the footprint survive a frame on windows apart from it. -/
theorem footprint_keep {ws : List W} {m m' : Std.ExtHashMap Nat (BitVec 8)} (frame : FrameOn ws m m')
    (apart : ∀ w ∈ ws, ∀ v ∈ f1Footprint, Apart w v) {x n : Nat} (inside : InFootprint x n) :
    bytesT m' x n = bytesT m x n := by
  obtain ⟨v, member, low, high⟩ := inside
  apply Reloc.bytesT_congr
  intro j hj
  have out : OutW ws (x + j) := outW_of fun w hw => by
    rcases apart w hw v member with h | h <;> omega
  have same := frame (x + j) out
  simp only [bytesT, same]

/-- A static read missing `caml_callback_depth`, which the interpreter's
entry and `STOP` update and `f1Runtime` does not read. -/
theorem in_bss {x n : Nat} (h : x + n ≤ Layout.sym_bss_end)
    (side : x + n ≤ Layout.sym_caml_callback_depth ∨ Layout.sym_caml_callback_depth + 4 ≤ x) : InKept x n := by
  rcases side with below | above
  · exact ⟨_, List.mem_cons_self, Nat.zero_le _, below⟩
  · exact ⟨⟨Layout.sym_caml_callback_depth + 4, Layout.sym_bss_end⟩, by simp [keptFootprint], above, h⟩

theorem in_youngLimit {x n : Nat} (low : f1Domain ≤ x) (h : x + n ≤ f1Domain + Layout.off_young_ptr) :
    InKept x n :=
  ⟨⟨f1Domain, f1Domain + Layout.off_young_ptr⟩, by simp [keptFootprint], low, h⟩

theorem in_youngRest {x n : Nat} (low : f1Domain + Layout.off_young_ptr + 8 ≤ x) (h : x + n ≤ f1Domain + 64) :
    InKept x n :=
  ⟨⟨f1Domain + Layout.off_young_ptr + 8, f1Domain + 64⟩, by simp [keptFootprint], low, h⟩

theorem in_stackFields {x n : Nat} (low : f1Domain + Layout.off_stack_high ≤ x)
    (h : x + n ≤ f1Domain + Layout.off_stack_threshold + 8) : InKept x n :=
  ⟨⟨f1Domain + Layout.off_stack_high, f1Domain + Layout.off_stack_threshold + 8⟩, by simp [keptFootprint], low, h⟩

theorem in_trapBarrier : InKept (f1Domain + Layout.off_trap_barrier) 8 :=
  ⟨⟨f1Domain + Layout.off_trap_barrier, f1Domain + Layout.off_trap_barrier + 8⟩, by simp [keptFootprint],
    Nat.le_refl _, Nat.le_refl _⟩

theorem in_backtrace : InKept (f1Domain + Layout.off_backtrace_active) 8 :=
  ⟨⟨f1Domain + Layout.off_backtrace_active, f1Domain + Layout.off_backtrace_active + 8⟩,
    by simp [keptFootprint], Nat.le_refl _, Nat.le_refl _⟩

theorem in_block {x n : Nat} (low : WhileMinRuntime.freeBlock.block - 8 ≤ x)
    (h : x + n ≤ WhileMinRuntime.freeBlock.block + 8 * WhileMinRuntime.freeBlock.words) : InKept x n :=
  ⟨⟨WhileMinRuntime.freeBlock.block - 8, WhileMinRuntime.freeBlock.block + 8 * WhileMinRuntime.freeBlock.words⟩,
    by simp [keptFootprint], low, h⟩

/-- Equal `n`-byte reads agree byte by byte. -/
theorem byte_of_bytesT {m m' : Std.ExtHashMap Nat (BitVec 8)} {a n : Nat}
    (h : bytesT m' a n = bytesT m a n) {i : Nat} (hi : i < n) :
    (m'[a + i]?).getD 0 = (m[a + i]?).getD 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have := congrArg (fun v => v.getLsbD (8 * i + k)) h
  rw [getLsbD_bytesT _ _ _ _ (by omega), getLsbD_bytesT _ _ _ _ (by omega)] at this
  simpa [show (8 * i + k) / 8 = i by omega, show (8 * i + k) % 8 = k by omega] using this

/-- `read8` is determined by the 8-byte read. -/
theorem read8_of_bytesT {m m' : Std.ExtHashMap Nat (BitVec 8)} {a : Nat}
    (h : bytesT m' a 8 = bytesT m a 8) : Primitives.read8 m' a = Primitives.read8 m a := by
  have b := fun i (hi : i < 8) => byte_of_bytesT h hi
  have b0 := b 0 (by decide)
  simp only [Nat.add_zero] at b0
  unfold Primitives.read8
  rw [b0, b 1 (by decide), b 2 (by decide), b 3 (by decide),
    b 4 (by decide), b 5 (by decide), b 6 (by decide), b 7 (by decide)]

/-- A zero 8-byte read is eight zero bytes. -/
theorem read8_zero {m : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} (h : bytesT m a 8 = 0#64) :
    Primitives.read8 m a = List.replicate 8 0#8 := by
  have b : ∀ i, i < 8 → (m[a + i]?).getD 0 = 0#8 := by
    intro i hi
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have := congrArg (fun v => v.getLsbD (8 * i + k)) h
    rw [getLsbD_bytesT _ _ _ _ (by omega)] at this
    simpa [show (8 * i + k) / 8 = i by omega, show (8 * i + k) % 8 = k by omega] using this
  have b0 := b 0 (by decide)
  simp only [Nat.add_zero] at b0
  unfold Primitives.read8
  rw [b0, b 1 (by decide), b 2 (by decide), b 3 (by decide), b 4 (by decide), b 5 (by decide),
    b 6 (by decide), b 7 (by decide)]
  rfl

/-- The exit globals survive any change that keeps their four words. -/
theorem ExitGlobals.transfer {c c' : Config}
    (keep : ∀ x, x + 8 ≤ Layout.sym_bss_end → (x + 8 ≤ Layout.sym_caml_callback_depth ∨ Layout.sym_caml_callback_depth + 4 ≤ x) →
      bytesT c'.σ.mem x 8 = bytesT c.σ.mem x 8)
    (h : ExitPath.ExitGlobals c) : ExitPath.ExitGlobals c' := by
  have r : ∀ (g : BitVec 64), g.toNat + 8 ≤ Layout.sym_bss_end →
      (g.toNat + 8 ≤ Layout.sym_caml_callback_depth ∨ Layout.sym_caml_callback_depth + 4 ≤ g.toNat) →
      Primitives.read8 c'.σ.mem g.toNat = Primitives.read8 c.σ.mem g.toNat :=
    fun g hg side => read8_of_bytesT (keep _ hg side)
  have bss : ∀ (g : BitVec 64), g.toNat < 0x8007d130 → g.toNat + 8 ≤ Layout.sym_bss_end := fun g hg => by
    simp only [Layout.sym_bss_end]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [r _ (bss _ (by simp [ExitPath.verbGc, Layout.sym_caml_verb_gc])) (by simp [ExitPath.verbGc, Layout.sym_caml_verb_gc, Layout.sym_caml_callback_depth])]; exact h.quiet
  · rw [r _ (bss _ (by simp [ExitPath.cleanupOnExit, Layout.sym_caml_cleanup_on_exit])) (by simp [ExitPath.cleanupOnExit, Layout.sym_caml_cleanup_on_exit, Layout.sym_caml_callback_depth])]; exact h.noCleanup
  · rw [r _ (bss _ (by simp [ExitPath.atexitList, Layout.sym_atexit])) (by simp [ExitPath.atexitList, Layout.sym_atexit, Layout.sym_caml_callback_depth])]; exact h.noAtexit
  · rw [r _ (bss _ (by simp [ExitPath.stdioExitHandler, Layout.sym_stdio_exit_handler])) (by simp [ExitPath.stdioExitHandler, Layout.sym_stdio_exit_handler, Layout.sym_caml_callback_depth])]; exact h.noHandler

/-- **Core transfer**: if every kept footprint read is unchanged, the pins
survive and only `young_ptr` may differ among the runtime fields. -/
theorem f1_core {c c' : Config} (keep : ∀ x n, InKept x n → bytesT c'.σ.mem x n = bytesT c.σ.mem x n)
    (pins : F1Pins c) :
    F1Pins c' ∧ runtimeFields c' =
      { runtimeFields c with youngPtr := (word c' (f1Domain + Layout.off_young_ptr)).toNat } := by
  have w8 : ∀ x, InKept x 8 → word c' x = word c x := fun x h => keep x 8 h
  have w4 : ∀ x, InKept x 4 → word32 c' x = word32 c x := fun x h => keep x 4 h
  have b : ∀ {x n}, x + n ≤ Layout.sym_bss_end → (x + n ≤ Layout.sym_caml_callback_depth ∨ Layout.sym_caml_callback_depth + 4 ≤ x) → InKept x n := in_bss
  have dom : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state :=
    w8 _ (b (by simp [Layout.sym_Caml_state, Layout.sym_bss_end]) (by simp only [Layout.sym_Caml_state, Layout.sym_caml_callback_depth]; omega))
  have domNat : (word c Layout.sym_Caml_state).toNat = f1Domain := by
    rw [pins.domain]; simp [f1Domain, WhileMinRuntime.domain]
  have young : ∀ off, Layout.off_young_ptr + 8 ≤ off → off + 8 ≤ 64 →
      word c' (f1Domain + off) = word c (f1Domain + off) :=
    fun off l h => w8 _ (in_youngRest (by omega) (by omega))
  have limit : word c' (f1Domain + Layout.off_young_limit) = word c (f1Domain + Layout.off_young_limit) :=
    w8 _ (in_youngLimit (by simp [Layout.off_young_limit]) (by simp [Layout.off_young_limit, Layout.off_young_ptr]))
  have fields : runtimeFields c' =
      { runtimeFields c with youngPtr := (word c' (f1Domain + Layout.off_young_ptr)).toNat } := by
    simp only [runtimeFields, domainWord, dom, domNat]
    rw [young _ (by decide) (by decide), young _ (by decide) (by decide), young _ (by decide) (by decide),
      young _ (by decide) (by decide), limit,
      w4 _ (b (by simp [Layout.sym_caml_something_to_do, Layout.sym_bss_end]) (by simp only [Layout.sym_caml_something_to_do, Layout.sym_caml_callback_depth]; omega))]
  have node : ∀ off, off + 8 ≤ 40 →
      InKept (WhileMinRuntime.freeBlock.block + off) 8 := fun off h =>
    in_block (by simp [WhileMinRuntime.freeBlock]; omega) (by simp [WhileMinRuntime.freeBlock]; omega)
  have shape := pins.freeList
  refine ⟨⟨?_, ?_, ?_, ?_, ExitGlobals.transfer (fun x hx side => keep x 8 (b hx side)) pins.exit,
    by rw [w8 _ in_trapBarrier]; exact pins.trapBarrier, by rw [w8 _ in_backtrace]; exact pins.backtraceOff,
    by rw [w8 _ (b (by simp [Layout.sym_caml_channel_mutex_unlock_exn, Layout.sym_bss_end])
      (by simp only [Layout.sym_caml_channel_mutex_unlock_exn, Layout.sym_caml_callback_depth]; omega))];
       exact pins.channelUnlock⟩, fields⟩
  · exact {
      nonnull := shape.nonnull
      aligned := shape.aligned
      large := shape.large
      fits := shape.fits
      small := fun i lo hi => by
        have e := shape.small i lo hi
        have slot : smallSlot i + 16 ≤ Layout.sym_bss_end := by
          simp only [smallSlot, Layout.sym_bf_small_fl, Layout.bf_small_size, Layout.sym_bss_end,
            Layout.bf_small_count] at hi ⊢
          omega
        exact ⟨by rw [w8 _ (b (by simp only [Layout.off_bf_small_free]; omega) (by simp only [Layout.off_bf_small_free, smallSlot, Layout.sym_bf_small_fl, Layout.bf_small_size, Layout.sym_caml_callback_depth]; omega))]; exact e.head,
          by rw [w8 _ (b (by simp only [Layout.off_bf_small_merge]; omega) (by simp only [Layout.off_bf_small_merge, smallSlot, Layout.sym_bf_small_fl, Layout.bf_small_size, Layout.sym_caml_callback_depth]; omega))]; exact e.merge⟩
      bitmap := by rw [w4 _ (b (by simp [Layout.sym_bf_small_map, Layout.sym_bss_end]) (by simp only [Layout.sym_bf_small_map, Layout.sym_caml_callback_depth]; omega))]; exact shape.bitmap
      root := by rw [w8 _ (b (by simp [Layout.sym_bf_large_tree, Layout.sym_bss_end]) (by simp only [Layout.sym_bf_large_tree, Layout.sym_caml_callback_depth]; omega))]; exact shape.root
      least := by rw [w8 _ (b (by simp [Layout.sym_bf_large_least, Layout.sym_bss_end]) (by simp only [Layout.sym_bf_large_least, Layout.sym_caml_callback_depth]; omega))]; exact shape.least
      header := by
        rw [w8 _ (in_block (by simp [WhileMinRuntime.freeBlock, Layout.header_bytes])
          (by simp [WhileMinRuntime.freeBlock, Layout.header_bytes]))]
        exact shape.header
      node := by
        rw [w4 _ (in_block (by simp [WhileMinRuntime.freeBlock, Layout.off_bf_isnode])
          (by simp [WhileMinRuntime.freeBlock, Layout.off_bf_isnode]))]
        exact shape.node
      left := by rw [w8 _ (node _ (by simp [Layout.off_bf_left]))]; exact shape.left
      right := by rw [w8 _ (node _ (by simp [Layout.off_bf_right]))]; exact shape.right
      prev := by rw [w8 _ (node _ (by simp [Layout.off_bf_prev]))]; exact shape.prev
      next := by rw [w8 _ (node _ (by simp [Layout.off_bf_next]))]; exact shape.next
      total := by rw [w8 _ (b (by simp [Layout.sym_caml_fl_cur_wsz, Layout.sym_bss_end]) (by simp only [Layout.sym_caml_fl_cur_wsz, Layout.sym_caml_callback_depth]; omega))]; exact shape.total }
  · rw [dom]; exact pins.domain
  · rw [w8 _ (in_stackFields (by simp [Layout.off_stack_high]) (by simp [Layout.off_stack_high,
      Layout.off_stack_threshold]))]
    exact pins.stackHigh
  · rw [w8 _ (in_stackFields (by simp [Layout.off_stack_high, Layout.off_stack_threshold])
      (by simp [Layout.off_stack_threshold]))]
    exact pins.threshold

/-- Read-equality on the whole footprint transfers `f1Runtime`. -/
theorem f1_transfer {c c' : Config} (keep : ∀ x n, InFootprint x n → bytesT c'.σ.mem x n = bytesT c.σ.mem x n)
    (ok : f1Runtime c) : f1Runtime c' := by
  obtain ⟨bounds, quiet, pins⟩ := ok
  obtain ⟨pins', fields⟩ := f1_core (fun x n h => keep x n h.footprint) pins
  have ptr : (word c' (f1Domain + Layout.off_young_ptr)).toNat = (runtimeFields c).youngPtr := by
    have dom : (word c Layout.sym_Caml_state).toNat = f1Domain := by
      rw [pins.domain]; simp [f1Domain, WhileMinRuntime.domain]
    have same : word c' (f1Domain + Layout.off_young_ptr) = word c (f1Domain + Layout.off_young_ptr) :=
      keep _ 8 ⟨youngWord, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    simp only [runtimeFields, domainWord, dom, same]
  rw [ptr] at fields
  exact ⟨fields ▸ bounds, fields ▸ quiet, pins'⟩

/-- **Windows apart from the footprint are runtime-stable.** -/
theorem f1_stable {ws : List W} (apart : ∀ w ∈ ws, ∀ v ∈ f1Footprint, Apart w v) :
    WindowStable f1Runtime ws :=
  fun _ _ frame ok => f1_transfer (fun _ _ inside => footprint_keep frame apart inside) ok

/-- A single window apart from the four footprint windows. -/
theorem f1_window {lo hi : Nat}
    (apart : ∀ v ∈ f1Footprint, hi ≤ v.lo ∨ v.hi ≤ lo) : WindowStable f1Runtime [⟨lo, hi⟩] :=
  f1_stable fun w hw v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    exact apart v hv

/-- The footprint, numerically. -/
theorem f1_window_of {lo hi : Nat}
    (bss : Layout.sym_bss_end ≤ lo)
    (young : hi ≤ f1Domain ∨ f1Domain + 64 ≤ lo)
    (stack : hi ≤ f1Domain + Layout.off_stack_high ∨ f1Domain + Layout.off_stack_threshold + 8 ≤ lo)
    (barrier : hi ≤ f1Domain + Layout.off_trap_barrier ∨ f1Domain + Layout.off_trap_barrier + 8 ≤ lo)
    (backtrace : hi ≤ f1Domain + Layout.off_backtrace_active ∨ f1Domain + Layout.off_backtrace_active + 8 ≤ lo)
    (block : hi ≤ WhileMinRuntime.freeBlock.block - 8 ∨
      WhileMinRuntime.freeBlock.block + 8 * WhileMinRuntime.freeBlock.words ≤ lo) :
    WindowStable f1Runtime [⟨lo, hi⟩] := by
  apply f1_window
  intro v hv
  simp only [f1Footprint, keptFootprint, youngWord, List.mem_cons, List.not_mem_nil, or_false] at hv
  simp only [Layout.off_young_ptr] at *
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only; omega
  · exact Or.inr (by simp only [Layout.sym_caml_callback_depth, Layout.sym_bss_end] at bss ⊢; omega)
  · exact Or.inr bss
  · dsimp only; omega
  · dsimp only; omega
  · exact stack
  · exact barrier
  · exact backtrace
  · exact block

/-- **`AllocationRuntime` for a nursery reservation.** Every store misses the
kept footprint (the `young_ptr` store does), and the final `young_ptr` stays
in `[young_limit, old young_ptr]`, aligned. -/
theorem f1_allocation {before : Config} {log : List WEntry}
    (stores : ∀ e ∈ log, ∀ v ∈ keptFootprint, e.1 + e.2.1 ≤ v.lo ∨ v.hi ≤ e.1)
    (young : ∀ after : Config, after.σ.mem = writeLog before.σ.mem log →
      (runtimeFields before).youngLimit ≤ (word after (f1Domain + Layout.off_young_ptr)).toNat ∧
      (word after (f1Domain + Layout.off_young_ptr)).toNat ≤ (runtimeFields before).youngPtr ∧
      (word after (f1Domain + Layout.off_young_ptr)).toNat % 8 = 0) :
    AllocationRuntime f1Runtime before log := by
  intro after memory ok
  obtain ⟨bounds, quiet, pins⟩ := ok
  have keep : ∀ x n, InKept x n → bytesT after.σ.mem x n = bytesT before.σ.mem x n := by
    intro x n inside
    obtain ⟨v, member, low, high⟩ := inside
    rw [memory]
    exact bytesT_writeLog_out _ (outLRange_of_forall fun e he => by
      rcases stores e he v member with h | h <;> omega)
  obtain ⟨pins', fields⟩ := f1_core keep pins
  obtain ⟨lowPtr, highPtr, aligned⟩ := young after memory
  refine ⟨?_, by rw [fields]; exact quiet, pins'⟩
  rw [fields]
  exact {
    nonempty := bounds.nonempty
    start := bounds.start
    alloc := Nat.le_trans bounds.limitLow lowPtr
    ptr := Nat.le_trans highPtr bounds.ptr
    stop := bounds.stop
    limitLow := bounds.limitLow
    limitHigh := bounds.limitHigh
    alignedStart := bounds.alignedStart
    alignedEnd := bounds.alignedEnd
    alignedPtr := aligned }

/-- (a) A `Caml_state` field the runtime invariant does not read
(trapsp, extern_sp, local_roots, exn_bucket, external_raise, …). -/
theorem f1_domainField {off : Nat} (notYoung : 64 ≤ off)
    (notPinned : off + 8 ≤ Layout.off_stack_high ∨
      (Layout.off_stack_threshold + 8 ≤ off ∧ off + 8 ≤ Layout.off_trap_barrier) ∨
      (Layout.off_trap_barrier + 8 ≤ off ∧ off + 8 ≤ Layout.off_backtrace_active) ∨
      Layout.off_backtrace_active + 8 ≤ off)
    (inRecord : off + 8 ≤ Layout.domainStateBytes) :
    WindowStable f1Runtime [⟨f1Domain + off, f1Domain + off + 8⟩] := by
  simp only [Layout.off_stack_high, Layout.off_stack_threshold, Layout.off_trap_barrier,
    Layout.off_backtrace_active] at notPinned
  apply f1_window_of
  · simp [f1Domain, WhileMinRuntime.domain, Layout.sym_bss_end]; omega
  · omega
  · simp only [Layout.off_stack_high, Layout.off_stack_threshold]; omega
  · simp only [Layout.off_trap_barrier]; omega
  · simp only [Layout.off_backtrace_active]; omega
  · simp only [f1Domain, WhileMinRuntime.domain, WhileMinRuntime.freeBlock, Layout.domainStateBytes] at *
    omega

theorem f1_trapsp : WindowStable f1Runtime [⟨f1Domain + Layout.off_trapsp, f1Domain + Layout.off_trapsp + 8⟩] :=
  f1_domainField (by decide) (by decide) (by decide)
theorem f1_extern_sp :
    WindowStable f1Runtime [⟨f1Domain + Layout.off_extern_sp, f1Domain + Layout.off_extern_sp + 8⟩] :=
  f1_domainField (by decide) (by decide) (by decide)
theorem f1_local_roots :
    WindowStable f1Runtime [⟨f1Domain + Layout.off_local_roots, f1Domain + Layout.off_local_roots + 8⟩] :=
  f1_domainField (by decide) (by decide) (by decide)
theorem f1_exn_bucket :
    WindowStable f1Runtime [⟨f1Domain + Layout.off_exn_bucket, f1Domain + Layout.off_exn_bucket + 8⟩] :=
  f1_domainField (by decide) (by decide) (by decide)
theorem f1_external_raise :
    WindowStable f1Runtime [⟨f1Domain + Layout.off_external_raise, f1Domain + Layout.off_external_raise + 8⟩] :=
  f1_domainField (by decide) (by decide) (by decide)

/-- (b) Any window inside the nursery `[young_start, young_end)` of the cut,
in particular the field windows of objects placed there. -/
theorem f1_nursery {lo hi : Nat} (low : 0x80082000 ≤ lo) (high : hi ≤ 0x80282000) :
    WindowStable f1Runtime [⟨lo, hi⟩] := by
  apply f1_window_of <;>
    simp only [f1Domain, WhileMinRuntime.domain, WhileMinRuntime.freeBlock, Layout.sym_bss_end,
      Layout.off_stack_high, Layout.off_stack_threshold, Layout.off_trap_barrier,
      Layout.off_backtrace_active] <;> omega

/-- (b) Any window above the free block and below `heap_end` (the initial
heap's placement and the VM stack lie there). -/
theorem f1_aboveBlock {lo hi : Nat}
    (low : WhileMinRuntime.freeBlock.block + 8 * WhileMinRuntime.freeBlock.words ≤ lo) :
    WindowStable f1Runtime [⟨lo, hi⟩] := by
  apply f1_window_of <;>
    simp only [f1Domain, WhileMinRuntime.domain, WhileMinRuntime.freeBlock, Layout.sym_bss_end,
      Layout.off_stack_high, Layout.off_stack_threshold, Layout.off_trap_barrier,
      Layout.off_backtrace_active] at * <;> omega

/-- `RuntimeFrame.stackWindow`: every window inside the VM stack allocation. -/
theorem f1_stackWindow {lo hi : Nat} (low : f1High - Layout.stackBytes ≤ lo) (_high : hi ≤ f1High) :
    WindowStable f1Runtime [⟨lo, hi⟩] :=
  f1_aboveBlock (by simp only [f1High, WhileMinEntry.high, Layout.stackBytes, WhileMinRuntime.freeBlock] at *; omega)

theorem f1_domain {c : Config} (ok : f1Runtime c) : (word c Layout.sym_Caml_state).toNat = f1Domain := by
  rw [ok.freeListShape.domain]; simp [f1Domain, WhileMinRuntime.domain]

/-- `RuntimeFrame.stackHigh`. -/
theorem f1_stackHigh {c : Config} (ok : f1Runtime c) :
    (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).toNat = f1High := by
  rw [f1_domain ok, ok.freeListShape.stackHigh]; simp [f1High, WhileMinEntry.high]

/-- `RuntimeFrame.threshold`. -/
theorem f1_threshold {c : Config} (ok : f1Runtime c) :
    (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold)).toNat =
      f1High - Layout.stackBytes + Layout.stackThresholdBytes := by
  rw [f1_domain ok, ok.freeListShape.threshold]
  simp [f1Threshold, f1High, WhileMinEntry.high, Layout.stackBytes, Layout.stackThresholdBytes]

/-- The exit path's globals (`ExitPath.do_exit_halts`, `ExitGlobals`). -/
theorem f1_exitGlobals {c : Config} (ok : f1Runtime c) : ExitPath.ExitGlobals c := ok.freeListShape.exit

/-- `RaiseQuietReady`: the trap barrier lies above the stack top. -/
theorem f1_trapBarrier {c : Config} (ok : f1Runtime c) :
    f1High ≤ (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_trap_barrier)).toNat := by
  rw [f1_domain ok, ok.freeListShape.trapBarrier]
  simp [f1High, WhileMinEntry.high]

/-- `RaiseQuietReady`: backtrace recording is off. -/
theorem f1_backtrace {c : Config} (ok : f1Runtime c) :
    word c ((word c Layout.sym_Caml_state).toNat + Layout.off_backtrace_active) = 0#64 := by
  rw [f1_domain ok]; exact ok.freeListShape.backtraceOff

/-- A window inside the VM stack allocation misses the whole footprint
(for consumers that enumerate `f1Footprint`, e.g. `Sim.F1Frame`). -/
theorem stackWindow_apart {lo hi : Nat} (low : f1High - Layout.stackBytes ≤ lo) (high : hi ≤ f1High) :
    ∀ v ∈ f1Footprint, Apart ⟨lo, hi⟩ v := by
  intro v hv
  simp only [f1Footprint, keptFootprint, youngWord, List.mem_cons, List.not_mem_nil, or_false] at hv
  simp only [f1High, f1Domain, WhileMinEntry.high, WhileMinRuntime.domain, WhileMinRuntime.freeBlock,
    Layout.stackBytes, Layout.sym_bss_end, Layout.sym_caml_callback_depth, Layout.off_young_ptr, Layout.off_stack_high,
    Layout.off_stack_threshold, Layout.off_trap_barrier, Layout.off_backtrace_active] at *
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Apart] <;> omega

/-- The VM-owned `Caml_state` fields miss the whole footprint. -/
theorem domainField_apart {off : Nat}
    (member : off ∈ [Layout.off_trapsp, Layout.off_extern_sp, Layout.off_local_roots,
      Layout.off_exn_bucket, Layout.off_external_raise]) :
    ∀ v ∈ f1Footprint, Apart ⟨f1Domain + off, f1Domain + off + 8⟩ v := by
  intro v hv
  simp only [f1Footprint, keptFootprint, youngWord, List.mem_cons, List.not_mem_nil, or_false] at hv member
  simp only [f1Domain, WhileMinRuntime.domain, WhileMinRuntime.freeBlock, Layout.sym_bss_end, Layout.sym_caml_callback_depth,
    Layout.off_young_ptr, Layout.off_stack_high, Layout.off_stack_threshold, Layout.off_trap_barrier,
    Layout.off_backtrace_active, Layout.off_trapsp, Layout.off_extern_sp, Layout.off_local_roots,
    Layout.off_exn_bucket, Layout.off_external_raise] at *
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Apart] <;> omega

/-- **`caml_callback_depth` is not read by `f1Runtime`**: the interpreter's
entry (`entry_prep`, depth + 1) and `STOP` (depth − 1) keep the invariant. -/
theorem f1_callbackDepth :
    WindowStable f1Runtime [⟨Layout.sym_caml_callback_depth, Layout.sym_caml_callback_depth + 4⟩] := by
  apply f1_window
  intro v hv
  simp only [f1Footprint, keptFootprint, youngWord, List.mem_cons, List.not_mem_nil, or_false] at hv
  simp only [f1Domain, WhileMinRuntime.domain, WhileMinRuntime.freeBlock, Layout.sym_bss_end, Layout.sym_caml_callback_depth,
    Layout.off_young_ptr, Layout.off_stack_high, Layout.off_stack_threshold, Layout.off_trap_barrier,
    Layout.off_backtrace_active] at *
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega

/-- The channel-mutex unlock hook is unset (a2-sem's division-by-zero row). -/
theorem f1_channelUnlock {c : Config} (ok : f1Runtime c) :
    word c Layout.sym_caml_channel_mutex_unlock_exn = 0#64 := ok.freeListShape.channelUnlock

/-- `RuntimeFrame.quiet`. -/
theorem f1_quiet {c : Config} (ok : f1Runtime c) : Sim.SignalCheckReady c := by
  have h := ok.noPending
  simp only [runtimeFields] at h
  exact ⟨BitVec.eq_of_toNat_eq (by simpa using h)⟩

/-- The private region of `NurseryGeometry` is the cut's free block. -/
theorem privateRegion_eq : privateRegion =
    ⟨WhileMinRuntime.freeBlock.block - 8, WhileMinRuntime.freeBlock.block + 8 * WhileMinRuntime.freeBlock.words⟩ := by
  simp [privateRegion, WhileMinRuntime.freeBlock]

/-- **(b) Object field windows.** A window inside a placed object (header or
fields) is stable under `f1Runtime`: the object lies above `.bss`
(`StackGeometry.heapLow`), apart from the `Caml_state` record and from the
private free block (`NurseryGeometry.heapDomain`/`heapPrivate`). -/
theorem f1_objectField {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {high l a x n : Nat}
    {o : Obj} (g : NurseryGeometry P s c pl cp high) (ok : f1Runtime c)
    (placed : pl.φ l = some a) (object : s.heap.get? l = some o)
    (low : Layout.sym_bss_end + 8 ≤ a) (start : a - 8 ≤ x) (finish : x + n ≤ a + 8 * o.wosize) :
    WindowStable f1Runtime [⟨x, x + n⟩] := by
  have dom := f1_domain ok
  obtain ⟨hd, -⟩ := g.heapDomain l a o placed object
  obtain ⟨hp, -⟩ := g.heapPrivate l a o placed object
  rw [dom] at hd
  rw [privateRegion_eq] at hp
  simp only at hd hp
  apply f1_window_of
  · omega
  · simp only [Layout.domainStateBytes] at hd; omega
  · simp only [Layout.domainStateBytes, Layout.off_stack_high, Layout.off_stack_threshold] at hd ⊢; omega
  · simp only [Layout.domainStateBytes, Layout.off_trap_barrier] at hd ⊢; omega
  · simp only [Layout.domainStateBytes, Layout.off_backtrace_active] at hd ⊢; omega
  · omega

theorem mem_of_logInW {ws : List W} {log : List WEntry} (h : LogInW ws log) :
    ∀ e ∈ log, InsideW ws e.1 e.2.1 := by
  induction log with
  | nil => intro e he; cases he
  | cons x rest ih =>
    intro e he
    rcases List.mem_cons.1 he with rfl | hr
    · exact h.1
    · exact ih h.2 e hr

/-- **Nursery reservations keep `f1Runtime`** (a1-arms' `AllocFrame` for the
pinned layout): the `young_ptr` store to `a - 8` within the free nursery, then
any stores inside the free nursery `[young_limit, young_ptr)`. -/
theorem f1_allocFrame_core {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high a : Nat} {log : List WEntry} (ok : f1Runtime c) (g : NurseryGeometry P s c pl cp high)
    (inside : LogInW [nurseryFree c] log)
    (low : (runtimeFields c).youngLimit ≤ a - 8) (below : a - 8 ≤ (runtimeFields c).youngPtr)
    (aligned : (a - 8) % 8 = 0) :
    AllocationRuntime f1Runtime c
      (Sim.grabReserveLog (word c Layout.sym_Caml_state).toNat a ++ log) := by
  have dom := f1_domain ok
  have stat := g.statics
  have priv := g.belowPrivate
  have top := g.top
  obtain ⟨domainApart, -⟩ := g.domain
  rw [dom] at domainApart
  simp only [nurseryFree, privateRegion, Layout.sym_bss_end, Layout.domainStateBytes, f1Domain,
    WhileMinRuntime.domain] at stat priv domainApart
  have entries := mem_of_logInW inside
  apply f1_allocation
  · intro e he v hv
    simp only [keptFootprint, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases List.mem_append.1 he with hy | hl
    · simp only [Sim.grabReserveLog, dom, List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      simp only [f1Domain, WhileMinRuntime.domain, Layout.off_young_ptr] at *
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [WhileMinRuntime.freeBlock, Layout.sym_bss_end, Layout.sym_caml_callback_depth,
          Layout.off_young_ptr, Layout.off_stack_high, Layout.off_stack_threshold, Layout.off_trap_barrier,
          Layout.off_backtrace_active] <;> omega
    · have hin := entries e hl
      simp only [InsideW, nurseryFree, or_false] at hin
      simp only [f1Domain, WhileMinRuntime.domain] at *
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [WhileMinRuntime.freeBlock, Layout.sym_bss_end, Layout.sym_caml_callback_depth,
          Layout.off_young_ptr, Layout.off_stack_high, Layout.off_stack_threshold, Layout.off_trap_barrier,
          Layout.off_backtrace_active] <;> omega
  · intro after memory
    have readback : word after (f1Domain + Layout.off_young_ptr) = BitVec.ofNat 64 (a - 8) := by
      change bytesT after.σ.mem _ 8 = _
      rw [memory]
      apply word_writeLog_at _ _ 0 _ _ (by simp [Sim.grabReserveLog, dom])
      simp only [Sim.grabReserveLog, List.drop_succ_cons, List.drop_zero, List.nil_append]
      apply outLRange_of_forall
      intro e he
      have hin := entries e he
      simp only [InsideW, nurseryFree, or_false] at hin
      simp only [f1Domain, WhileMinRuntime.domain, Layout.off_young_ptr] at *
      omega
    rw [readback, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨low, below, aligned⟩

section Cut
open Vsa.Sim.Boot WhileMinLog

/-- The pins hold on the certified cut memory. -/
theorem f1Pins_of {c : Config} {initial : Vsa.MemRepr.Mem}
    (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem initial log)) : F1Pins c := by
  obtain ⟨b, shape⟩ := (WhileMinRuntime.freeList memory).shape
  have root := shape.root
  have total := shape.total
  rw [WhileMinRuntime.read_bf_large_tree memory] at root
  rw [WhileMinRuntime.read_caml_fl_cur_wsz memory] at total
  have same : b = WhileMinRuntime.freeBlock := by
    cases b with
    | mk block words =>
      simp only [WhileMinRuntime.freeBlock, FreeBlock.mk.injEq]
      simp at root total
      omega
  subst same
  refine ⟨shape, WhileMinRuntime.read_domain memory, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact WhileMinEntry.read_stack_high memory
  · exact WhileMinEntry.read_stack_threshold memory
  · have z : ∀ (g : BitVec 64) (n : Nat), g.toNat = n → word c n = 0#64 →
        Primitives.read8 c.σ.mem g.toNat = List.replicate 8 0#8 :=
      fun g n hn hw => by rw [hn]; exact read8_zero hw
    exact ⟨by rw [z _ _ (by simp [ExitPath.verbGc, Layout.sym_caml_verb_gc]) (WhileMinEntry.read_caml_verb_gc memory)]; rfl,
      by rw [z _ _ (by simp [ExitPath.cleanupOnExit, Layout.sym_caml_cleanup_on_exit]) (WhileMinEntry.read_caml_cleanup_on_exit memory)]; rfl,
      by rw [z _ _ (by simp [ExitPath.atexitList, Layout.sym_atexit]) (WhileMinEntry.read_atexit memory)]; rfl,
      by rw [z _ _ (by simp [ExitPath.stdioExitHandler, Layout.sym_stdio_exit_handler]) (WhileMinEntry.read_stdio_exit_handler memory)]; rfl⟩
  · exact WhileMinEntry.read_trap_barrier memory
  · exact WhileMinEntry.read_backtrace_active memory
  · exact WhileMinEntry.read_caml_channel_mutex_unlock_exn memory

/-- `f1Runtime` on the certified cut memory. -/
theorem f1Runtime_of {c : Config} {initial : Vsa.MemRepr.Mem}
    (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem initial log)) : f1Runtime c := by
  have ok := WhileMinRuntime.runtimeOk memory
  exact ⟨ok.bounds, ok.noPending, f1Pins_of memory⟩

/-- Replace the runtime component of a loaded witness. -/
theorem Loaded.retarget {L L' : OCaml.Layout} {P : Prog} {c : Config} (h : OCaml.Loaded L P c)
    (runtime : L'.runtimeOk c) (budget : L'.budget = L.budget) : OCaml.Loaded L' P c := by
  obtain ⟨pl, cp, high, entry⟩ := h
  exact ⟨pl, cp, high, { entry with
    platform := ⟨entry.platform.control, entry.platform.image, runtime⟩
    geometry := ⟨entry.geometry.toArmGeometry, budget ▸ entry.geometry.room⟩ }⟩

/-- **`Loaded f1Layout whileMin`** at the captured cut. -/
theorem whileMin_loaded_f1 : OCaml.Loaded f1Layout OCaml.Programs.whileMin WhileMin.cut :=
  Loaded.retarget WhileMin.loaded (f1Runtime_of WhileMin.memory_equiv) rfl

/-- The densified entry, as a0-boot's `loaded_fillZero`. -/
theorem whileMin_loaded_f1_fillZero : OCaml.Loaded f1Layout OCaml.Programs.whileMin (Vsa.Densify.fillZero WhileMin.cut) :=
  Loaded.retarget WhileMin.loaded_fillZero
    (f1Runtime_of ((Vsa.Densify.memEqv_fillZeroMem WhileMin.cut.σ.mem).symm.trans WhileMin.memory_equiv)) rfl

end Cut

end OCaml.Vm.Gc
