import Vsa.Machine

/-! A reusable execution summary for initialization code that only writes registers.
The induction is over an abstract write list, so concrete initializers do not need
kernel evaluation of their accumulated machine states. -/
namespace Vsa.Sim.RegisterWrites
open Vsa.Machine LeanRV64DExecutable Sail ConcurrencyInterfaceV1

abbrev Assignment := (r : Register) × RegisterType r

def program : List Assignment → SailM PUnit
  | [] => pure ()
  | ⟨r, v⟩ :: rest => do writeReg r v; program rest

def registers (xs : List Assignment) (rs : Std.ExtDHashMap Register RegisterType) :=
  xs.foldl (fun rs x => rs.insert x.1 x.2) rs

def apply (xs : List Assignment) (s : MState) : MState :=
  { s with regs := registers xs s.regs }

theorem run (xs : List Assignment) (s : MState) :
    (program xs).run s = .ok () (apply xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | mk r v =>
      simp only [program, EStateM.run, bind, EStateM.bind,
        writeReg, PreSail.writeReg, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
      simpa only [EStateM.run, apply, registers, List.foldl_cons] using
        ih { s with regs := s.regs.insert r v }

theorem run_apply (xs : List Assignment) (s : MState) :
    program xs s = .ok () (apply xs s) := by
  simpa only [EStateM.run] using run xs s

/-- Observe only the final assignment to a register, without constructing a state. -/
def lastValue : List Assignment → (r : Register) → Option (RegisterType r)
  | [], _ => none
  | ⟨q, v⟩ :: xs, r => (lastValue xs r).or (if h : q = r then some (h ▸ v) else none)

theorem lastValue_append (xs ys : List Assignment) (r : Register) :
    lastValue (xs ++ ys) r = (lastValue ys r).or (lastValue xs r) := by
  induction xs with
  | nil => simp [lastValue]
  | cons x xs ih =>
    cases x with
    | mk q v =>
      simp only [List.cons_append, lastValue, ih, Option.or_assoc]

theorem registers_read (xs : List Assignment) (rs : Std.ExtDHashMap Register RegisterType)
    (r : Register) : (registers xs rs).get? r = (lastValue xs r).or (rs.get? r) := by
  induction xs generalizing rs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | mk q v =>
      change (registers xs (rs.insert q v)).get? r = _
      rw [ih]
      by_cases eq : q = r
      · subst q
        simp [lastValue, Std.ExtDHashMap.get?_insert]
      · simp [lastValue, Std.ExtDHashMap.get?_insert, eq]

theorem apply_read (xs : List Assignment) (s : MState) (r : Register) :
    (apply xs s).regs.get? r = (lastValue xs r).or (s.regs.get? r) :=
  registers_read xs s.regs r

theorem apply_read_append (xs ys : List Assignment) (s : MState)
    (r : Register) (v : RegisterType r) (value : lastValue ys r = some v) :
    (apply (xs ++ ys) s).regs.get? r = some v := by
  rw [apply_read, lastValue_append, value]
  rfl

/-- A register outside an assignment list retains its value. -/
theorem registers_frame (xs : List Assignment) (rs : Std.ExtDHashMap Register RegisterType)
    (r : Register) (absent : ∀ x ∈ xs, x.1 ≠ r) :
    (registers xs rs).get? r = rs.get? r := by
  induction xs generalizing rs with
  | nil => rfl
  | cons x xs ih =>
    have head : x.1 ≠ r := absent x (by simp)
    have tail : ∀ y ∈ xs, y.1 ≠ r := fun y hy => absent y (by simp [hy])
    simp only [registers, List.foldl_cons]
    rw [show xs.foldl (fun rs x => rs.insert x.1 x.2) (rs.insert x.1 x.2) =
      registers xs (rs.insert x.1 x.2) from rfl, ih _ tail]
    simp [Std.ExtDHashMap.get?_insert, head]

theorem memory (xs : List Assignment) (s : MState) : (apply xs s).mem = s.mem := rfl
theorem output (xs : List Assignment) (s : MState) : (apply xs s).sailOutput = s.sailOutput := rfl
theorem cycles (xs : List Assignment) (s : MState) : (apply xs s).cycleCount = s.cycleCount := rfl

end Vsa.Sim.RegisterWrites
