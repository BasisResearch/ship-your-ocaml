import OCaml.Vm.Sim.DecodeFetch
import OCaml.Vm.Sim.SwitchInt
import OCaml.Vm.Sim.SwitchBlock
import OCaml.Vm.Sim.AccRows

/-!
# The SWITCH row of the F1 arm table

SWITCH's operand list is the packed size word and the jump table, so its row
is stated directly over `decode_fetch` (every table entry is a fetched
operand word). Integer selectors use `switch_int_step_arm`; pointers to an
ordinary block (`.ptr l 0`) use `switch_block_step_arm` with the tag and
header read from the represented object. Atom and infix selectors need the
atom table's headers and infix headers in the representation; that row is
the named premise `SwitchExotic` (open).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- **Atom and infix SWITCH selectors** (named obligation): their header
words are the atom table's and the infix headers, not yet represented. -/
def SwitchExotic (L : OCaml.Layout) (P : Prog) : Prop :=
  ∀ s s' c sizes table, Reach P s → OCaml.LoopAt L P s c →
    (∀ n, s.accu ≠ .int n) → (∀ l, s.accu ≠ .ptr l 0) →
    stepI P s ⟨.SWITCH, sizes :: table⟩ = .next s' → ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c'

/-- A placed object's header byte is readable. -/
theorem StackGeometry.header_read {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high l a : Nat} {o : Obj} (g : StackGeometry P s c pl cp high)
    (placed : pl.φ l = some a) (object : s.heap.get? l = some o) : RamReadAt (a - 8) 1 := by
  have lo := g.heapLow l a o placed object
  have hi := g.heapArena l a o placed object
  refine ⟨?_, ?_, Or.inr ?_⟩ <;> simp only [Layout.sym_bss_end, Layout.sym_tohost,
    Vsa.Sim.DlHeap.heapEnd] at * <;> omega

theorem opt_ne_halt {α : Type} {o : Option α} {k : α → Res} {e : Nat} {w : World}
    (hk : ∀ a, k a ≠ .halt e w) : opt o k ≠ .halt e w := by
  cases o with
  | none => simp [opt]
  | some a => exact hk a

theorem switch_no_halt {P : Prog} {s : St} {sizes : Int} {table : List Int} {e : Nat} {w : World} :
    stepI P s ⟨.SWITCH, sizes :: table⟩ ≠ .halt e w :=
  opt_ne_halt fun _ => opt_ne_halt fun _ => opt_ne_halt fun _ => nofun

/-- **The SWITCH row.** -/
theorem switch_row {L : OCaml.Layout} {P : Prog} (stable : MemoryStable L.runtimeOk)
    (exotic : SwitchExotic L P) : OCaml.OpArm P (OCaml.LoopAt L P) .SWITCH := by
  intro s c i reach h hd hop _
  obtain ⟨code, fetches⟩ := decode_fetch hd
  obtain ⟨o, args⟩ := i
  simp only at hop
  subst hop
  cases args with
  | nil => trivial
  | cons sizes table =>
    apply OCaml.ArmOutcome.of_next
    · intro s' step
      obtain ⟨sw, sfetch, rfl⟩ := fetches 0 sizes rfl
      -- the table entry selected by index `k` is a fetched operand word
      have entryWord : ∀ k x, table[k]? = some x →
          ∃ w : BitVec 32, P.code[s.pc + 2 + k]? = some w ∧ w.toInt = x := fun k x hx => by
        obtain ⟨w, hw, hx'⟩ := fetches (k + 1) x (by simpa using hx)
        exact ⟨w, by rw [show s.pc + 2 + k = s.pc + 1 + (k + 1) by omega]; exact hw, hx'⟩
      cases ha : s.accu with
      | int n =>
        have unfolded := step
        simp only [stepI, ha] at unfolded
        obtain ⟨k, hk, rest⟩ := opt_next unfolded
        obtain ⟨x, hx, -⟩ := opt_next rest
        split at hk
        · cases hk
          obtain ⟨w, wfetch, rfl⟩ := entryWord _ _ hx
          obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
          obtain ⟨c', run, running⟩ := switch_int_step_arm stable input ha
            (OperandAt.of_fetch input.geometry wfetch) hx step
          exact ⟨c', run, h.of_plus run running⟩
        · cases hk
      | ptr l k =>
        cases k with
        | zero =>
          obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
          obtain ⟨xw, -, word⟩ := input.accu
          rw [ha] at word
          simp only [valWord, Option.map_eq_some_iff] at word
          obtain ⟨a, placed, -⟩ := word
          have live : Live s.heap (roots P s) l := .root (v := s.accu) (by simp [roots]) (by simp [ha, Val.loc?])
          obtain ⟨a', ob, placed', object, -⟩ := input.heap.1 l live
          rw [placed] at placed'; cases placed'
          have selected := SwitchTag.of_object input.toVmReprAt input.geometry.even ha placed object
          have unfolded := step
          rw [switch_tag_step sw.toInt table selected.tagOf] at unfolded
          obtain ⟨k, hk, rest⟩ := opt_next unfolded
          obtain ⟨x, hx, -⟩ := opt_next rest
          split at hk
          · rename_i bound
            cases hk
            have positive : 0 ≤ sw.toInt := by omega
            rw [switch_sizes_nat sw positive] at hx
            obtain ⟨w, wfetch, rfl⟩ := entryWord _ _ hx
            have low := input.geometry.heapLow l a ob placed object
            obtain ⟨c', run, running⟩ := switch_block_step_arm stable input selected (by omega)
              (input.geometry.header_read placed object) (OperandAt.of_fetch input.geometry sfetch)
              (OperandAt.of_fetch input.geometry wfetch) hx step
            exact ⟨c', run, h.of_plus run running⟩
          · cases hk
        | succ k =>
          exact exotic s s' c _ table reach h (by simp [ha]) (by simp [ha]) step
      | atom t => exact exotic s s' c _ table reach h (by simp [ha]) (by simp [ha]) step
      | code pc =>
        have unfolded := step
        simp [stepI, ha, tag?, opt] at unfolded
      | raw w =>
        have unfolded := step
        simp [stepI, ha, tag?, opt] at unfolded
    · intro e w; exact switch_no_halt

end OCaml.Vm.Sim
