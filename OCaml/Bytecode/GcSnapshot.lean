import OCaml.Bytecode.Value

/-! `gc_ctrl.c:caml_gc_quick_stat` observes the concrete collector, which
is intentionally absent from the abstract heap. Its observations are
explicit execution inputs. They must be matched to the concrete counters
by the Layer A observation premise; they are never inferred from Heap.size. -/
namespace OCaml.Bytecode

/-- The exact 17-field quick-stat snapshot, before allocating its result. -/
structure GcSnapshot where
  minorWords : BitVec 64
  promotedWords : BitVec 64
  majorWords : BitVec 64
  minorCollections : Int
  majorCollections : Int
  heapWords : Int
  heapChunks : Int
  liveWords : Int
  liveBlocks : Int
  freeWords : Int
  freeBlocks : Int
  largestFree : Int
  fragments : Int
  compactions : Int
  topHeapWords : Int
  stackSize : Int
  forcedMajorCollections : Int
  deriving DecidableEq, Repr

/-- quick_stat deliberately returns zero for the six uncomputed fields. -/
def GcSnapshot.valid (s : GcSnapshot) : Bool :=
  s.liveWords == 0 && s.liveBlocks == 0 && s.freeWords == 0 &&
  s.freeBlocks == 0 && s.largestFree == 0 && s.fragments == 0

def GcSnapshot.counters (s : GcSnapshot) : List Val :=
  [s.minorCollections, s.majorCollections, s.heapWords, s.heapChunks,
   s.liveWords, s.liveBlocks, s.freeWords, s.freeBlocks, s.largestFree,
   s.fragments, s.compactions, s.topHeapWords, s.stackSize,
   s.forcedMajorCollections].map Val.ofInt

/-- Tuple allocation precedes the three boxed doubles, as in gc_ctrl.c. -/
def GcSnapshot.allocate (s : GcSnapshot) (h : Heap) : Val × Heap := Id.run do
  let (h, l) := h.alloc (.block 0 (List.replicate 17 .unit))
  let (h, minor) := h.alloc (.double s.minorWords)
  let (h, promoted) := h.alloc (.double s.promotedWords)
  let (h, major) := h.alloc (.double s.majorWords)
  return (.ptr l 0, h.set l (.block 0
    ([.ptr minor 0, .ptr promoted 0, .ptr major 0] ++ s.counters)))

/-- Text interchange for the differential validation capture tool. -/
def GcSnapshot.parse (line : String) : Option GcSnapshot := do
  let numbers ← (line.splitOn ",").mapM String.toInt?
  match numbers with
  | [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q] =>
    let s : GcSnapshot := ⟨BitVec.ofInt 64 a, BitVec.ofInt 64 b, BitVec.ofInt 64 c,
      d,e,f,g,h,i,j,k,l,m,n,o,p,q⟩
    if s.valid then some s else none
  | _ => none

end OCaml.Bytecode
