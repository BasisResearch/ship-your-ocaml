import OCaml.Vm.Primitives.CamlInt64FloatOfBits
import OCaml.Vm.Primitives.CamlSysGetArgv
import OCaml.Vm.Primitives.CamlSysExecutableName
import OCaml.Vm.Primitives.CamlSysGetConfig
import OCaml.Vm.Primitives.OutChannelsList

/-! Where the allocating F1 primitives place their fresh objects, as a
function of the state at the `C_CALL` and the young pointer at entry. The
C_CALL row extends the placement with these (`Place.put`) before the call, so
each contract's `placed` premise holds by `put_self`. -/
namespace OCaml.Vm.Primitives
open OCaml.Bytecode

/-- The fresh `(location, value address)` pairs of an allocating F1 primitive,
in allocation order. `young` is the young pointer at the call entry
(`(runtimeFields c).youngPtr`). Non-allocating primitives place nothing. -/
def allocPlaces (name : String) (s : St) (young : BitVec 64) : List (Nat × Nat) :=
  match name with
  | "caml_int64_float_of_bits" =>
    match s.accu with
    | .ptr l 0 =>
      match s.heap.get? l with
      | some (.int64 bits) => [((s.heap.alloc (.double bits)).2, (young - 16#64).toNat + 8)]
      | _ => []
    | _ => []
  | "caml_ml_open_descriptor_out" | "caml_ml_open_descriptor_in" =>
    -- the channel's custom block (`caml_alloc_custom_mem`: ops and one data word)
    match s.accu with
    | .int _ => [((s.heap.alloc (.channel s.world.chans.length)).2, (young - 24#64).toNat + 8)]
    | _ => []
  | "caml_sys_executable_name" =>
    [((s.heap.alloc (.bytes progExeName)).2,
      (StringCopy.resultWord young progExeName.length).toNat)]
  | "caml_sys_get_argv" =>
    -- the name string, then the pair whose young pointer is the string's header
    [((s.heap.alloc (.bytes progExeName)).2,
      (StringCopy.resultWord young progExeName.length).toNat),
     (((ArgvTuple.afterName s).heap.alloc (ArgvTuple.argvPair s)).2,
      (ArgvTuple.tupleWord (StringCopy.resultWord young progExeName.length - 8#64)).toNat)]
  | "caml_sys_get_config" =>
    [((s.heap.alloc (.bytes ConfigTuple.osType)).2,
      (StringCopy.resultWord young ConfigTuple.osType.length).toNat),
     (((ConfigTuple.afterOsType s).heap.alloc (ConfigTuple.configTriple s)).2,
      (ConfigTuple.tripleWord (StringCopy.resultWord young ConfigTuple.osType.length - 8#64)).toNat)]
  | "caml_ml_out_channels_list" =>
    -- per listed channel, its custom block and then the cons cell
    outListPlaces s young
  | _ => []

end OCaml.Vm.Primitives
