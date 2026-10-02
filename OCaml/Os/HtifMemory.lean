import OCaml.Os
import OCaml.Vm.Repr

/-! Concrete HTIF entry addresses and filesystem memory relation. Layout is
measured by the target compiler, including static table sizes and field offsets.
No function execution is claimed here. Generated function summaries must supply
the remaining ABI decoding and per-function obligations. -/
namespace OCaml.Os
open Vsa.Machine OCaml.Vm TCB.Os TCB.Os.Fs

/-- Every address is a symbol in the pinned image. -/
def htifAddress : HtifFunction → Nat
  | .open => Layout.sym_open | .read => Layout.sym_read
  | .write => Layout.sym_write | .lseek => Layout.sym_lseek
  | .close => Layout.sym_close | .fstat => Layout.sym_fstat
  | .stat => Layout.sym_stat | .unlink => Layout.sym_unlink
  | .rename => Layout.sym_rename | .opendir => Layout.sym_opendir
  | .readdir => Layout.sym_readdir | .closedir => Layout.sym_closedir
  | .gettimeofday => Layout.sym_gettimeofday | .times => Layout.sym_times

def htifFunctions : List HtifFunction :=
  [.open, .read, .write, .lseek, .close, .fstat, .stat, .unlink,
   .rename, .opendir, .readdir, .closedir, .gettimeofday, .times]

/-- Executable classification of a machine PC. -/
def htifFunctionAt (c : Config) : Option HtifFunction :=
  htifFunctions.find? fun f => pcOf c == some (BitVec.ofNat 64 (htifAddress f))

/-- All function entries are distinct in the pinned image. -/
theorem htif_addresses_distinct : (htifFunctions.map htifAddress).Nodup := by decide

/-- Entry-sensitive result decoding is essential: read/stat/gettimeofday write
through pointers supplied at entry, which caller-saved registers need not retain. -/
def htifCallConv (decode : HtifFunction → Config → Option Call)
    (result : Config → Config → Ret) : CallConv where
  callAt c := (htifFunctionAt c).bind (fun f => decode f c)
  returnsTo c c' := pcOf c' = gpr c 1 ∧ gpr c' 2 = gpr c 2
  retOf := result

/-- Classification is concrete even while the ABI result decoder remains open. -/
def htifEntries (decode : HtifFunction → Config → Option Call)
    (result : Config → Config → Ret) : HtifEntries (htifCallConv decode result) where
  entry f c := htifFunctionAt c = some f
  covers := by
    intro c call hc
    cases hf : htifFunctionAt c with
    | none => simp [htifCallConv, hf] at hc
    | some f => exact ⟨f, rfl⟩

def nodeAddr (i : Nat) : Nat := Layout.sym_files + i * Layout.htif_size_mfile
def fdAddr (i : Nat) : Nat := Layout.sym_fds + i * Layout.htif_size_mfd
def dirAddr (i : Nat) : Nat := Layout.sym_dirs + i * Layout.htif_size_baremetal_dir

def nodeUsed (c : Config) (i : Nat) : Bool :=
  byte c (nodeAddr i + Layout.htif_off_mfile_used) != 0

def nodeIsDir (c : Config) (i : Nat) : Bool :=
  byte c (nodeAddr i + Layout.htif_off_mfile_dir) != 0

def nodeLinked (c : Config) (i : Nat) : Bool :=
  byte c (nodeAddr i + Layout.htif_off_mfile_linked) != 0

def nodeParent (c : Config) (i : Nat) : Nat :=
  (word32 c (nodeAddr i + Layout.htif_off_mfile_parent)).toNat

/-- Total byte reads, using the same zero convention as Sail. -/
def bytesAt (c : Config) (a : Nat) (bs : List UInt8) : Prop :=
  ∀ j b, bs[j]? = some b → byte c (a + j) = BitVec.ofNat 8 b.toNat

/-- Names have their actual length; there is deliberately no 255-byte bound.
Such a bound would hide the long-name readdir obstruction. -/
structure NodeNameAt (c : Config) (i : Nat) (name : String) : Prop where
  length : word c (nodeAddr i + Layout.htif_off_mfile_nlen) =
    BitVec.ofNat 64 name.toUTF8.size
  bytes : bytesAt c (word c (nodeAddr i + Layout.htif_off_mfile_name)).toNat name.toUTF8.toList
  terminator : byte c ((word c (nodeAddr i + Layout.htif_off_mfile_name)).toNat + name.toUTF8.size) = 0

structure FileBytesAt (c : Config) (i : Nat) (bs : List UInt8) : Prop where
  size : (word c (nodeAddr i + Layout.htif_off_mfile_size)).toNat = bs.length
  capacity : bs.length ≤ (word c (nodeAddr i + Layout.htif_off_mfile_cap)).toNat
  bytes : bytesAt c (word c (nodeAddr i + Layout.htif_off_mfile_data)).toNat bs
  readonlyFlag : byte c (nodeAddr i + Layout.htif_off_mfile_ro) = 0 ∨
    byte c (nodeAddr i + Layout.htif_off_mfile_ro) = 1

/-- Reusable C slots are not abstract inode identities. Only live nodes need
placement; dead unlinked abstract files can remain in Fs.State. -/
abbrev NodePlace := Entry → Option Nat

def decodeOpenFlags (v : Nat) : OpenFlags :=
  { access := if v &&& Layout.htif_o_accmode == Layout.htif_o_wronly then .wronly
      else if v &&& Layout.htif_o_accmode == Layout.htif_o_rdwr then .rdwr else .rdonly
    creat := v &&& Layout.htif_o_creat != 0
    excl := v &&& Layout.htif_o_excl != 0
    trunc := v &&& Layout.htif_o_trunc != 0
    append := v &&& Layout.htif_o_append != 0
    directory := v &&& Layout.htif_o_directory != 0 }

/-- Exact descriptor-table projection (HTIF opendir consumes no fd). -/
def fdObject (c : Config) (pl : NodePlace) (fd : Nat) (obj : FdObj) : Prop :=
  let a := fdAddr fd
  let kind := (word32 c (a + Layout.htif_off_mfd_kind)).toNat
  match obj with
  | .stream stream => kind = match stream with
      | .stdin => Layout.htif_fd_stdin
      | .stdout => Layout.htif_fd_stdout
      | .stderr => Layout.htif_fd_stderr
  | .file e pos flags => kind = Layout.htif_fd_file ∧
      pl e = some (word32 c (a + Layout.htif_off_mfd_node)).toNat ∧
      (word c (a + Layout.htif_off_mfd_pos)).toNat = pos ∧
      decodeOpenFlags (word32 c (a + Layout.htif_off_mfd_flags)).toNat = flags
  | .dirfd _ => False

/-- Apply pending observer notifications exactly as osReaddir does. -/
def observedHandle (fs : Fs.State) (h : DhState) : DhState :=
  let changes := (((fs.dir? h.dir).bind fun d => alookup d.observers h.obs).getD []).reverse
  changes.foldl (fun h change => match change with
    | .added n => { h with may := n :: h.may }
    | .removed n => if h.must.contains n then
        { h with must := h.must.erase n, may := n :: h.may } else h) h

/-- Remaining names in table order, including dot entries. Not filtered by
readdir's small return buffer: dropping a mandatory long name is a real error. -/
def remainingNames (c : Config) (pl : NodePlace) (s : OsState)
    (slot : Nat) (h : DhState) : List String :=
  let pos := (word32 c (dirAddr slot + Layout.htif_off_baremetal_dir_pos)).toInt
  let entries := ((s.fs.dir? h.dir).getD ⟨[], none, []⟩).entries
  (if pos ≤ -2 then ["."] else []) ++ (if pos ≤ -1 then [".."] else []) ++
    ((List.range Layout.htif_max_files).filterMap fun i =>
      if (i : Int) < pos then none else
      (entries.find? fun e => pl e.2 == some i).map (·.1))

structure DirectoryCursorAt (c : Config) (pl : NodePlace) (s : OsState)
    (slot : Nat) (h : DhState) : Prop where
  node : pl (.dir h.dir) = some (word32 c (dirAddr slot + Layout.htif_off_baremetal_dir_node)).toNat
  positionLower : -2 ≤ (word32 c (dirAddr slot + Layout.htif_off_baremetal_dir_pos)).toInt
  positionUpper : (word32 c (dirAddr slot + Layout.htif_off_baremetal_dir_pos)).toInt ≤ Layout.htif_max_files
  noFd : h.fd = none
  unbroken : h.broken = false
  observer : ∃ d changes, s.fs.dir? h.dir = some d ∧ alookup d.observers h.obs = some changes
  required : ∀ n ∈ (observedHandle s.fs h).must, n ∈ remainingNames c pl s slot h
  allowed : ∀ n ∈ remainingNames c pl s slot h,
    n ∈ (observedHandle s.fs h).must ++ (observedHandle s.fs h).may

/-- Initialized HTIF memory. Startup must establish this relation after
fs_init. Console output is observed in Sail, stdin is EOF, and time is frozen.
This is a concrete candidate invariant, not an assertion it is inductive:
DirectoryObstruction exhibits the known failure of readdir. Resource exhaustion
and allocator failure also need explicit treatment in the function proofs. -/
structure HtifMemoryAt (c : Config) (s : OsState) (pl : NodePlace) : Prop where
  initialized : word32 c Layout.sym_fs_ready = 1
  root : pl (.dir Fs.root) = some 0
  cwd : s.cwd = Fs.root
  injective : ∀ e e' i, pl e = some i → pl e' = some i → e = e'
  placed : ∀ e i, pl e = some i → i < Layout.htif_max_files ∧ nodeUsed c i = true
  used : ∀ i, i < Layout.htif_max_files → nodeUsed c i = true → ∃ e, pl e = some i
  directories : ∀ d i, pl (.dir d) = some i → nodeIsDir c i = true ∧ (s.fs.dir? d).isSome = true
  files : ∀ f i, pl (.file f) = some i → nodeIsDir c i = false ∧
    ∃ bs, s.fs.file? f = some bs ∧ FileBytesAt c i bs
  links : ∀ d dir name e, s.fs.dir? d = some dir →
    (alookup dir.entries name = some e ↔
      ∃ parent i, pl (.dir d) = some parent ∧ pl e = some i ∧
        nodeLinked c i = true ∧ nodeParent c i = parent ∧ NodeNameAt c i name)
  linkedPlaced : ∀ i, i < Layout.htif_max_files → nodeUsed c i = true →
    nodeLinked c i = true → ∃ d dir name e, s.fs.dir? d = some dir ∧
      alookup dir.entries name = some e ∧ pl e = some i
  parents : ∀ d i dir parent name, pl (.dir d) = some i → s.fs.dir? d = some dir →
    dir.parent = some (parent, name) →
    pl (.dir parent) = some (nodeParent c i) ∧ NodeNameAt c i name
  descriptors : ∀ fd obj, lookupFd s fd = some obj ↔
    fd < Layout.htif_max_fds ∧ fdObject c pl fd obj
  freeDescriptors : ∀ fd, fd < Layout.htif_max_fds →
    (lookupFd s fd = none ↔ (word32 c (fdAddr fd + Layout.htif_off_mfd_kind)).toNat = Layout.htif_fd_free)
  handles : ∀ dh h, lookupDh s dh = some h →
    0 < dh ∧ dh ≤ Layout.htif_max_dirs ∧
    word32 c (dirAddr (dh - 1) + Layout.htif_off_baremetal_dir_used) = 1 ∧
    DirectoryCursorAt c pl s (dh - 1) h
  usedHandles : ∀ slot, slot < Layout.htif_max_dirs →
    (word32 c (dirAddr slot + Layout.htif_off_baremetal_dir_used) ≠ 0 ↔
      (lookupDh s (slot + 1)).isSome = true)
  opens : ∀ e i, pl e = some i →
    (word32 c (nodeAddr i + Layout.htif_off_mfile_opens)).toNat =
      (s.fds.filter (fun pair => match pair.2 with
        | .file e' _ _ => e' == e | _ => false)).length +
      (s.dhs.filter (fun pair => Entry.dir pair.2.dir == e)).length
  input : s.streams.input = []
  output : Vsa.Machine.output c.σ = OCaml.Bytecode.bytesToString s.streams.console
  clock : s.clock.now = 0

/-- Existential slot placement permits node reuse after the last close. -/
def htifMemory (c : Config) (s : OsState) : Prop := ∃ pl, HtifMemoryAt c s pl

end OCaml.Os
