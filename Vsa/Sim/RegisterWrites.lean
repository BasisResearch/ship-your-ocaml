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

theorem memory (xs : List Assignment) (s : MState) : (apply xs s).mem = s.mem := rfl
theorem output (xs : List Assignment) (s : MState) : (apply xs s).sailOutput = s.sailOutput := rfl
theorem cycles (xs : List Assignment) (s : MState) : (apply xs s).cycleCount = s.cycleCount := rfl

end Vsa.Sim.RegisterWrites
