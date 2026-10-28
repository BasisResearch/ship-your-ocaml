import OCaml.Vm.Boot.WhileMinRuntimeReads
import OCaml.Vm.Reloc
import OCaml.Vm.Gc.NurseryDefs
import VsaIris.Vsa.HeapRoom

/-! Read-only inputs of the quiet channel-custom path. These are independent
of mutable resource/table accounting; readiness alone supplies none of them.
The lambda-zero branch avoids the local context and sampling reads. -/
namespace OCaml.Vm.Gc
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Actual runtime reads at fixed G1 addresses, including the stable identity
of the domain and its custom table. Values are certified at the captured cut. -/
def customCallWords : List (Nat × BitVec 64) :=
  [(Layout.sym_Caml_state, BitVec.ofNat 64 Boot.WhileMinRuntime.domain),
   (Layout.sym_caml_custom_minor_max_bsz, 8192#64),
   (Layout.sym_caml_custom_minor_ratio, 100#64),
   (Layout.sym_caml_custom_major_ratio, 44#64),
   (Layout.sym_lambda, 0#64),
   (Boot.WhileMinRuntime.domain + Layout.off_minor_heap_wsz, 0x40000#64),
   (Boot.WhileMinRuntime.domain + Layout.off_stat_heap_wsz, 0x1f000#64),
   (Boot.WhileMinRuntime.domain + Layout.off_custom_table, BitVec.ofNat 64 Boot.WhileMinRuntime.customTable)]

def CustomCallRead (a : Nat) : Prop :=
  ∃ obs ∈ customCallWords, VsaIris.InExt (obs.1, 8) a

structure CustomCallPins (c : Config) : Prop where
  words : ∀ obs ∈ customCallWords, word c obs.1 = obs.2

/-- Read-only transfer uses its own byte frame, never the Ready frame. -/
theorem CustomCallPins.frame {c d : Config} (pins : CustomCallPins c)
    (keep : ∀ a, CustomCallRead a → byte d a = byte c a) : CustomCallPins d := by
  constructor
  intro obs member
  calc
    word d obs.1 = word c obs.1 := by
      apply Reloc.bytesT_congr
      intro j hj
      exact keep _ ⟨obs, member, by constructor <;> dsimp only <;> omega⟩
    _ = obs.2 := pins.words obs member

/-- Captured-memory read certificates; no execution from reset is asserted. -/
theorem CustomCallPins.startup {c : Config} {initial : Vsa.MemRepr.Mem}
    (memory : Vsa.Densify.MemEqv c.σ.mem
      (Vsa.Sim.Boot.observedMem initial Boot.WhileMinLog.log)) :
    CustomCallPins c := by
  constructor
  intro obs member
  simp only [customCallWords, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Boot.WhileMinRuntime.read_domain memory
  · exact Boot.WhileMinRuntime.read_caml_custom_minor_max_bsz memory
  · exact Boot.WhileMinRuntime.read_caml_custom_minor_ratio memory
  · exact Boot.WhileMinRuntime.read_caml_custom_major_ratio memory
  · exact Boot.WhileMinRuntime.read_lambda memory
  · exact Boot.WhileMinRuntime.read_minor_heap_wsz memory
  · exact Boot.WhileMinRuntime.read_stat_heap_wsz memory
  · exact Boot.WhileMinRuntime.read_custom_table memory

/-- Numeric placement of the independent call reads, used by actual caller
windows and native return frames. -/
structure CustomCallReadBounds (a : Nat) : Prop where
  location : a < DlHeap.heapStart ∨
    VsaIris.InExt (Boot.WhileMinRuntime.domain, Layout.domainStateBytes) a
  below : a < DlHeap.heapEnd
  minor : a + 24 < minorRegion.lo
  young : Boot.WhileMinRuntime.domain + 16 ≤ a ∨ a + 8 ≤ Boot.WhileMinRuntime.domain
  roots : a + 8 ≤ Boot.WhileMinRuntime.domain + Layout.off_local_roots ∨
    Boot.WhileMinRuntime.domain + Layout.off_local_roots + 8 ≤ a
  externalRaise : a + 8 ≤ Boot.WhileMinRuntime.domain + Layout.off_external_raise ∨
    Boot.WhileMinRuntime.domain + Layout.off_external_raise + 8 ≤ a
  callback : a + 4 ≤ Layout.sym_caml_callback_depth ∨ Layout.sym_caml_callback_depth + 4 ≤ a
  errno1 : a < Layout.sym_impure_data ∨ Layout.sym_impure_data + 4 ≤ a
  errno2 : a < Layout.sym_errno ∨ Layout.sym_errno + 4 ≤ a
  opened : a < Layout.sym_caml_all_opened_channels ∨ Layout.sym_caml_all_opened_channels + 8 ≤ a
  resource : ¬ VsaIris.InExt (Layout.sym_caml_extra_heap_resources, 8) a
  minorResource : ¬ VsaIris.InExt (Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor, 8) a
  allocator : ¬ VsaIris.VsaHeap.allocGlobal a

/-- Finite address arithmetic about the actual generated ABI/symbol offsets. -/
theorem CustomCallRead.bounds {a : Nat} (read : CustomCallRead a) : CustomCallReadBounds a := by
  obtain ⟨obs, member, lo, hi⟩ := read
  simp only [customCallWords, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Layout.sym_Caml_state, Layout.sym_caml_custom_minor_max_bsz,
      Layout.sym_caml_custom_minor_ratio, Layout.sym_caml_custom_major_ratio, Layout.sym_lambda,
      Boot.WhileMinRuntime.domain, Layout.off_minor_heap_wsz, Layout.off_stat_heap_wsz,
      Layout.off_custom_table] at lo hi <;>
    constructor <;>
    (try simp only [minorRegion, VsaIris.InExt, DlHeap.heapStart, DlHeap.heapEnd, Boot.WhileMinRuntime.domain,
      Layout.domainStateBytes, Layout.off_local_roots, Layout.off_external_raise,
      Layout.sym_caml_callback_depth, Layout.sym_caml_extra_heap_resources,
      Layout.off_extra_heap_resources_minor, Layout.sym_impure_data, Layout.sym_errno,
      Layout.sym_caml_all_opened_channels, VsaIris.VsaHeap.allocGlobal, VsaIris.VsaHeap.InRange]) <;>
    (try dsimp only at lo hi) <;> omega

/-- Native addressing uses the same fixed domain as the observed fields. -/
theorem CustomCallPins.domain {c : Config} (pins : CustomCallPins c) :
    word c Layout.sym_Caml_state = BitVec.ofNat 64 Boot.WhileMinRuntime.domain :=
  pins.words (Layout.sym_Caml_state, BitVec.ofNat 64 Boot.WhileMinRuntime.domain) List.mem_cons_self

/-- The call really reads the owned fixed custom table. -/
theorem CustomCallPins.table {c : Config} (pins : CustomCallPins c) :
    word c ((word c Layout.sym_Caml_state).toNat + Layout.off_custom_table) =
      BitVec.ofNat 64 Boot.WhileMinRuntime.customTable := by
  rw [pins.domain]
  exact pins.words (Boot.WhileMinRuntime.domain + Layout.off_custom_table,
    BitVec.ofNat 64 Boot.WhileMinRuntime.customTable) (by simp [customCallWords])

end OCaml.Vm.Gc
