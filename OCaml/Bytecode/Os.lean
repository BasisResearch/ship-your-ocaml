import TCB.Os.Syscall

/-! Executable OS selection for the bare-metal world. Every transition goes
through `TCB.Os.allowed`; its existing `allowed_sound` theorem supplies the
`OsStep` boundary. The selector chooses complete writes, maximal reads, a
frozen clock, and the first specified result for other calls. Matching the
machine's choice in ambiguous cases remains part of `HtifFsImplements`. -/
namespace OCaml.Bytecode

/-- One specified OS call. Spec-special cases have no selected successor. -/
def osReturn (s : TCB.Os.OsState) (c : TCB.Os.Call) : Option TCB.Os.Ret :=
  match c with
  | .clock => some (.num s.clock.now)
  | _ => ((TCB.Os.outs s c).filterMap fun
      | .ok _ r => some r
      | .special _ => none).getLast?

def osCall (s : TCB.Os.OsState) (c : TCB.Os.Call) : Option (TCB.Os.Ret × TCB.Os.OsState) := do
  let r ← osReturn s c
  let s' ← TCB.Os.allowed s c r
  pure (r, s')

/-- Selected transitions inherit the trusted OS specification's relation. -/
theorem osCall_sound {s s' : TCB.Os.OsState} {c : TCB.Os.Call} {r : TCB.Os.Ret}
    (h : osCall s c = some (r, s')) : TCB.Os.OsStep s c r s' := by
  cases hr : osReturn s c with
  | none => simp [osCall, hr] at h
  | some ret =>
    cases hs : TCB.Os.allowed s c ret with
    | none => simp [osCall, hr, hs] at h
    | some st =>
      simp [osCall, hr, hs] at h
      rcases h with ⟨rfl, rfl⟩
      exact TCB.Os.allowed_sound hs

/-- The embedded-file table is loaded before the interpreter cut point.
Parent directories are created as in htif.c's embedded-file initialization. -/
def osInitial (files : List (String × List UInt8)) : TCB.Os.OsState :=
  let insert := fun (fs : TCB.Os.Fs.State) (path : String) (bytes : List UInt8) => Id.run do
    let names := (path.splitOn "/").filter (· != "")
    let mut fs := fs
    let mut dir := TCB.Os.Fs.root
    for name in names.take (names.length - 1) do
      match fs.resolve dir name with
      | some (.dir d) => dir := d
      | _ => let (fs', d) := fs.mkdir dir name; fs := fs'; dir := d
    match names.getLast? with
    | none => return fs
    | some name =>
      let (fsNew, i) := fs.mkfile dir name
      return fsNew.setFile i bytes
  { TCB.Os.OsState.init with fs := files.foldl (fun fs (p, bs) => insert fs p bs) TCB.Os.Fs.State.init }

/-- Observable named files, derived from the OS state rather than a second
mutable file map. Unlinked but open files have no path in this observation. -/
def osFiles (s : TCB.Os.OsState) : List (String × List UInt8) :=
  s.fs.dirs.flatMap fun (d, dir) => dir.entries.filterMap fun (name, e) =>
    match e with
    | .file i => some ("/" ++ "/".intercalate (s.fs.realPath d ++ [name]), s.fs.contents i)
    | .dir _ => none

end OCaml.Bytecode
