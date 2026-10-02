import TCB.Os.Syscall

/-! The HTIF directory buffer drops a successfully created 256-byte name.
The C reproducer is scripts/probe_htif_directory_name.py. These facts
check the specification side of that finite trace, not a Sail execution. -/
namespace OCaml.Os
open TCB.Os

/-- After dot entries are consumed, this existing name must be reported. -/
def longNameDirectory : OsState :=
  let name := String.ofList (List.replicate 256 'x')
  { OsState.init with
    fs := { Fs.State.init with
      dirs := [(0, ⟨[(name, .file 1)], none, []⟩)],
      files := [(1, [])], next := 2 },
    dhs := [(1, ⟨0, 0, [name], [], none, false⟩)] }

/-- HTIF's observed EOF has no specified successor. -/
theorem longName_eof_rejected : next longNameDirectory (.readdir 1) .none = [] := by decide

/-- This is not one of the spec's unconstrained OS cases. -/
theorem longName_not_special : special longNameDirectory (.readdir 1) = false := by decide

end OCaml.Os
