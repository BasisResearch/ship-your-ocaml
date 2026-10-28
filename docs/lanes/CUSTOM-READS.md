# Quiet channel-custom native reads

The target is the pinned RV64 ELF and OCaml 4.14.4 `runtime/custom.c`,
`memory.c`, `minor_gc.c`, and `memprof.c`. This is a source/disassembly audit,
not a native execution proof. The accepted native obligation is still
`CustomMemCall`; no new primitive summary is assumed.

| Native site | Observation and producer |
| --- | --- |
| `caml_alloc_custom_mem` `0x80024804` | `Caml_state`: `CustomCallPins.domain`, produced by generated captured reads and retained in F1Pins. |
| `0x8002481c`, `0x80024838`, `0x80024844` | `minor_heap_wsz=0x40000`, custom minor ratio `100`, minor max `8192`. |
| `0x80024854`, `0x80024870` | `stat_heap_wsz=0x1f000`, custom major ratio `44`. Both division and multiplication use the native integer order. |
| `alloc_custom_gen` `0x80024654` | Current `local_roots`, saved/restored through the actual native frame; its value is arbitrary, not a fixed startup pin. |
| `caml_alloc_small` `0x8000c0cc`–`0x8000c0e0` | Actual young pointer and young limit, room for 24 bytes and alignment from CustomMemInput and the opening/listing nursery geometry. The room branch skips allocation dispatch and its sampling/collector reads. |
| `0x800246b4` | `channel_operations.finalize`, an actual total load at the supplied ops address. No particular loaded value is needed: OR with nonzero `mem=65616` makes the branch nonzero. |
| `0x800246d4`–`0x800246dc` | Domain custom-table identity, insertion pointer and limit. The identity is a read-only CustomCallPins observation. PhysicalCustoms observes all seven table words, occupancy and the exact allocated shape. |
| `realloc_generic_table` | The first null-base request is `(0x40000/8+256)*24=792576` bytes; existing CustomMemCredit proves the actual request expression. HeapReady supplies selected allocator/pool facts. Native allocation and spending on that same returned ledger/capacity remain open. |
| `caml_adjust_gc_speed` `0x8000a8c4` | Mutable static resource double, initially positive zero; accounted by PhysicalCustoms.major and the existing CustomFoot. |
| `alloc_custom_gen` `0x80024724` | Mutable domain minor-resource double, initially positive zero; accounted by PhysicalCustoms.minor. |
| `caml_memprof_track_custom` `0x80029484`–`0x80029490` | `lambda=+0`, retained in CustomCallPins. Native __eqdf2 has an existing proved abstraction. Its zero branch skips `local` and `local->suspended`, random state and callbacks. Those outside reads are not inferred from Ready. |
| Soft-double helpers | Code/rodata and their native stack/ABI context. ExecutableImage supplies immutable text/rodata; LeafInput and NativeFrame supply the machine context. |

Call-context pins are separate from mutable custom accounting. The ordinary
F1 footprint adds exactly the three read-only domain words above, with all
actual static parameter words already in the static kept gaps. Concrete
startup certificates establish their values. Opening transports them through
its saves, malloc/open record effects and flags; listing transports them
through its actual prologue, refcount/scratch stores, native returned frames
and cons-cell stores. The existing Ready frame is never used to establish
these external reads.

PhysicalCustoms records unique natural occupancy, count <=5, both resource
bit-pattern targets, caller separation of the full footprint, and either all seven initial zero table words or
CustomTableShape's actual base/ptr/threshold/limit/end/size/reserve. Combining
its allocated shape with separately retained CustomCallPins constructs the
existing QuietCustomTable. Its `not_full` compares the actual ptr and limit;
occupancy alone does not prove this. PhysicalState restricts CustomFoot to states with a physical witness.
The null-footprint startup producer and Caml_state/address frame prove all
existing CallerApart and full accounting/readiness/state frame laws; malformed
arbitrary backing pointers do not acquire a global apartness law.
Ledger ownership/CustomSpace and numeric CustomHeapCredit remain separate
selected-heap facts.

The integer rounding model in CustomResources gives kernel-checked finite
positive binary64 *targets*, including values below one through five charges
and the sixth major target above one. It follows the separate ratio rounding
and then repeated addition, using denominators **297968** and **2097100**
(the latter is `(0x40000*8/100)*100`, not 2097152). The native obligation still
owes the connection to actual `__floatundidf`, `__divdf3`, `__adddf3`, and
`__gedf2` executions, their ABI returns, and the exact threshold branches.
The rational quietBound_spec does not discharge that connection. These target
facts are not presented as machine semantics or proved helper summaries.

CustomMemCall still owns actual allocation/table initialization, table
insertion, exact count/resource transition, quiet return and full returned
ledger. CustomMemSpending still needs native production and propagation of
separate credit through counted callers. Spatial HeapReady/CustomLedger
cannot imply numeric LibHeapAt.room. Captured memory certification does not
establish execution from reset. GoodF1, counted BarrierGrowthFull's G2 owner,
and C4 round 2's F1 dependency are unchanged.
