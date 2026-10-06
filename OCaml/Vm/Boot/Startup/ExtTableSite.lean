import OCaml.Vm.Boot.Startup.CamlSharedTable
import OCaml.Vm.Boot.Startup.StartupAuxMemory
import OCaml.Vm.Boot.Startup.TableAllocatorInput
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- A 16-byte global table header between the startup globals and the arena,
clear of allocator metadata and the runtime observations `RuntimeReady` pins. -/
structure ExtTableGlobal (t : Nat) : Prop where
  low : Layout.sym_startup_count ≤ t
  high : t + Layout.ext_table_bytes ≤ heapStart
  domain : t + Layout.ext_table_bytes ≤ Layout.sym_Caml_state ∨ Layout.sym_Caml_state + 8 ≤ t
  pool : t + Layout.ext_table_bytes ≤ Layout.sym_pool ∨ Layout.sym_pool + 8 ≤ t
  allocator : ∀ a, t ≤ a → a < t + Layout.ext_table_bytes → ¬ allocGlobal a
  files : t + Layout.ext_table_bytes ≤ Layout.sym_files + 56 ∨ Layout.sym_files + 56 * 64 ≤ t

/-- Where caml_ext_table_init (entered with stack pointer `sp`) may find its
`struct ext_table`: a global header, or a header in a caller's native frame at
or above `sp`. Both actual startup shapes occur: `caml_shared_libs_path` and
the primitive tables are globals, while `caml_search_exe_in_path` keeps its
path table on its own stack. -/
structure ExtTableSite (sp t : BitVec 64) : Prop where
  write : WriteWindow t 8
  place : (sp.toNat ≤ t.toNat ∧ t.toNat + Layout.ext_table_bytes ≤ Layout.sym_stack_top) ∨
    ExtTableGlobal t.toNat

theorem ExtTableGlobal.shared : ExtTableGlobal Layout.sym_caml_shared_libs_path where
  files := by decide
  low := by decide
  high := by decide
  domain := by decide
  pool := by decide
  allocator := by
    intro a lo hi
    unfold allocGlobal InRange
    unfold Layout.sym_caml_shared_libs_path Layout.ext_table_bytes at *
    omega

theorem ExtTableSite.shared (sp : BitVec 64) : ExtTableSite sp sharedTableAddress := by
  refine ⟨by constructor <;> decide, Or.inr ?_⟩
  have eq : sharedTableAddress.toNat = Layout.sym_caml_shared_libs_path := by decide
  rw [eq]
  exact ExtTableGlobal.shared

/-- A table at the callee's own entry stack pointer, as in
`caml_search_exe_in_path`, whose `struct ext_table path` is at offset 0 of its frame. -/
theorem ExtTableSite.at_sp {sp : BitVec 64} (frame : NativeFrame sp 16)
    (top : sp.toNat + Layout.ext_table_bytes ≤ Layout.sym_stack_top) : ExtTableSite sp sp := by
  have lower := frame.lower
  have aligned := frame.aligned
  refine ⟨?_, Or.inl ⟨Nat.le_refl _, top⟩⟩
  unfold Layout.ext_table_bytes Layout.sym_stack_top heapEnd at *
  constructor
  · omega
  · omega
  · unfold Layout.sym_tohost; omega
  · omega

theorem ExtTableSite.bound {sp t} (site : ExtTableSite sp t) : t.toNat + 16 ≤ 0x100000000 := by
  have g := site.write
  rcases site.place with ⟨_, top⟩ | g'
  · unfold Layout.ext_table_bytes Layout.sym_stack_top at top; omega
  · have := g'.high; unfold Layout.ext_table_bytes heapStart at this; omega

theorem ExtTableSite.addr {sp t} (site : ExtTableSite sp t) {k : Nat} (small : k ≤ 16) :
    (t + BitVec.ofNat 64 k).toNat = t.toNat + k := by
  have := site.bound
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ExtTableSite.window {sp t} (site : ExtTableSite sp t) (off width : Nat)
    (fits : off + width ≤ 16) (aligned : off % width = 0) (wide : 8 % width = 0) :
    WriteWindow (t + BitVec.ofNat 64 off) width := by
  have w := site.write
  have b := site.bound
  have e := site.addr (k := off) (by omega)
  have wa := w.aligned
  have wl := w.lower
  have wh := w.htif
  constructor <;> rw [e]
  · omega
  · omega
  · omega
  · rw [Nat.add_mod, aligned, Nat.add_zero]
    have := Nat.mod_mod_of_dvd t.toNat (Nat.dvd_of_mod_eq_zero wide)
    rw [← this, wa]
    simp

/-- Every runtime observation lies outside the header. -/
theorem ExtTableSite.image {sp t} (site : ExtTableSite sp t) (frame : NativeFrame sp 16) :
    Image.textBase + Image.textSize ≤ t.toNat ∧ Image.rodataBase + Image.rodataSize ≤ t.toNat := by
  have lower := frame.lower
  rcases site.place with ⟨above, _⟩ | g
  · unfold Image.textBase Image.textSize Image.rodataBase Image.rodataSize heapEnd at *; omega
  · have := g.low; unfold Image.textBase Image.textSize Image.rodataBase Image.rodataSize Layout.sym_startup_count at *; omega

theorem ExtTableSite.pin {sp t a} (site : ExtTableSite sp t) (frame : NativeFrame sp 16)
    (low : a < Layout.sym_startup_count) : a < t.toNat := by
  have lower := frame.lower
  rcases site.place with ⟨above, _⟩ | g
  · unfold Layout.sym_startup_count heapEnd at *; omega
  · have := g.low; omega

theorem ExtTableSite.foot {sp t H a} (site : ExtTableSite sp t) (frame : NativeFrame sp 16)
    (owned : vsaFoot H a) : a < t.toNat ∨ t.toNat + Layout.ext_table_bytes ≤ a := by
  have lower := frame.lower
  have below := allocator_foot_below owned
  rcases site.place with ⟨above, _⟩ | g
  · left; omega
  · by_cases lo : a < t.toNat
    · exact Or.inl lo
    by_cases hi : t.toNat + Layout.ext_table_bytes ≤ a
    · exact Or.inr hi
    exfalso
    have high := g.high
    rcases owned with glob | ⟨start, _, _⟩
    · exact g.allocator a (by omega) (by omega) glob
    · omega

theorem ExtTableSite.domain {sp t} (site : ExtTableSite sp t) (frame : NativeFrame sp 16) :
    t.toNat + Layout.ext_table_bytes ≤ Layout.sym_Caml_state ∨ Layout.sym_Caml_state + 8 ≤ t.toNat := by
  have lower := frame.lower
  rcases site.place with ⟨above, _⟩ | g
  · right; unfold Layout.sym_Caml_state heapEnd at *; omega
  · exact g.domain

theorem ExtTableSite.pool {sp t} (site : ExtTableSite sp t) (frame : NativeFrame sp 16) :
    t.toNat + Layout.ext_table_bytes ≤ Layout.sym_pool ∨ Layout.sym_pool + 8 ≤ t.toNat := by
  have lower := frame.lower
  rcases site.place with ⟨above, _⟩ | g
  · right; unfold Layout.sym_pool heapEnd at *; omega
  · exact g.pool

/-- The header never overlaps the callee's own 16-byte save area. -/
theorem ExtTableSite.frame {sp t} (site : ExtTableSite sp t) (frame : NativeFrame sp 16) :
    sp.toNat ≤ t.toNat ∨ t.toNat + Layout.ext_table_bytes ≤ nativeFrameBase sp 16 := by
  have lower := frame.lower
  rcases site.place with ⟨above, _⟩ | g
  · exact Or.inl above
  · right; have := g.high; unfold nativeFrameBase heapStart heapEnd at *; omega
end OCaml.Vm.Boot.Startup
