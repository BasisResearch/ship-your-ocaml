import OCaml.Vm.Boot.Startup.ToCamlMain
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.MemRepr OCaml.Vm.Primitives

/-- Every byte of a zero word store is zero, for an arbitrary backing memory. -/
theorem zeroWord_byte (m : Mem) (base a : Nat) (lo : base ≤ a) (hi : a < base + 8) :
    (writeLog m [(base, 8, 0#64)])[a]? = some 0#8 := by
  have cases : a = base ∨ a = base + 1 ∨ a = base + 2 ∨ a = base + 3 ∨
      a = base + 4 ∨ a = base + 5 ∨ a = base + 6 ∨ a = base + 7 := by omega
  rcases cases with h | h | h | h | h | h | h | h
  all_goals subst a
  all_goals first
    | exact getElem_writeMap8_0 m base (sdData_val 0#64)
    | exact getElem_writeMap8_1 m base (sdData_val 0#64)
    | exact getElem_writeMap8_2 m base (sdData_val 0#64)
    | exact getElem_writeMap8_3 m base (sdData_val 0#64)
    | exact getElem_writeMap8_4 m base (sdData_val 0#64)
    | exact getElem_writeMap8_5 m base (sdData_val 0#64)
    | exact getElem_writeMap8_6 m base (sdData_val 0#64)
    | exact getElem_writeMap8_7 m base (sdData_val 0#64)

/-- Reads inside the counted BSS clear follow by induction on its abstract effect,
not by executing the concrete startup loop. -/
theorem clearWords_inside (m : Mem) (base n a : Nat)
    (lo : base ≤ a) (hi : a < base + 8 * n) :
    (clearWords m base n)[a]? = some 0#8 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [clearWords]
    by_cases last : base + 8 * n ≤ a
    · exact zeroWord_byte _ _ a last (by omega)
    · rw [writeLog_out _ _ _ (show OutL [(base + 8 * n, 8, 0#64)] a from
        ⟨Or.inl (by omega), True.intro⟩)]
      exact ih (by omega)

/-- Any eight-byte window inside the cleared region supplies the total load pins. -/
theorem clearWords_pins (m : Mem) (base n a : Nat)
    (lo : base ≤ a) (hi : a + 8 ≤ base + 8 * n) :
    LPins8 (clearWords m base n) a (List.replicate 8 0#8) := by
  simp (disch := omega) [LPins8, clearWords_inside]
  decide

/-- A framed log preserves a cleared eight-byte window; compose before choosing
concrete BSS dimensions so no memory map is unfolded. -/
theorem clearWords_log_pins (m : Mem) (base n a : Nat) (log : List WEntry)
    (lo : base ≤ a) (hi : a + 8 ≤ base + 8 * n)
    (outside : ∀ i < 8, OutL log (a + i)) :
    LPins8 (writeLog (clearWords m base n) log) a (List.replicate 8 0#8) := by
  have agree : ∀ b, a ≤ b → b < a + 8 →
      (writeLog (clearWords m base n) log)[b]? = (clearWords m base n)[b]? := by
    intro b lower upper
    apply writeLog_out
    have hb : a + (b - a) = b := by omega
    exact hb ▸ outside (b - a) (by omega)
  simpa (disch := omega) only [LPins8, agree] using clearWords_pins m base n a lo hi

/-- The two main stores preserve any disjoint zero-initialized BSS word. -/
theorem CrtCamlMainPost.bss_pins {initial c : Config} (post : CrtCamlMainPost initial c)
    (a : Nat) (lo : Layout.sym_bss_start ≤ a)
    (hi : a + 8 ≤ Layout.sym_bss_start + 8 * bssWords)
    (outside : ∀ i < 8, OutL
      (mainWrites 0x8000003c#64 (read8 initial.σ.mem Layout.sym_embedded_env)) (a + i)) :
    LPins8 c.σ.mem a (List.replicate 8 0#8) := by
  rw [post.memory]
  exact clearWords_log_pins initial.σ.mem Layout.sym_bss_start bssWords a _ lo hi outside

/-- All addresses between main's global and stack stores are framed. -/
theorem mainWrites_between (ra : BitVec 64) (env : List (BitVec 8)) (a : Nat)
    (lo : Layout.sym_environ + 8 ≤ a) (hi : a < Layout.sym_stack_top - 8) :
    OutL (mainWrites ra env) a := ⟨Or.inl hi, Or.inr lo, True.intro⟩

/-- Pooling is disabled when crt0/main first enter the runtime. -/
theorem CrtCamlMainPost.pool_zero {initial c : Config} (post : CrtCamlMainPost initial c) :
    LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8) := by
  apply post.bss_pins Layout.sym_pool (by decide) (by decide)
  intro i hi
  apply mainWrites_between <;>
    simp only [Layout.sym_stack_top, Layout.sym_environ, Layout.sym_pool] <;> omega

/-- Domain initialization takes its fresh-domain branch on the first runtime entry. -/
theorem CrtCamlMainPost.domain_zero {initial c : Config} (post : CrtCamlMainPost initial c) :
    LPins8 c.σ.mem Layout.sym_Caml_state (List.replicate 8 0#8) := by
  apply post.bss_pins Layout.sym_Caml_state (by decide) (by decide)
  intro i hi
  apply mainWrites_between <;>
    simp only [Layout.sym_stack_top, Layout.sym_environ, Layout.sym_Caml_state] <;> omega
end OCaml.Vm.Boot.Startup
