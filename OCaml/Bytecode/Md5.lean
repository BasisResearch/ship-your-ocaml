import OCaml.Bytecode.Value

/-! MD5 from runtime/md5.c, Colin Plumb's public-domain implementation.
The table records its 64 MD5STEP invocations; the fold rotates a,b,c,d
between invocations, with uint32 arithmetic. -/
namespace OCaml.Bytecode

private def md5Steps : List (Nat × Nat × BitVec 32 × Nat) := [
  (1, 0, 0xd76aa478#32, 7),
  (1, 1, 0xe8c7b756#32, 12),
  (1, 2, 0x242070db#32, 17),
  (1, 3, 0xc1bdceee#32, 22),
  (1, 4, 0xf57c0faf#32, 7),
  (1, 5, 0x4787c62a#32, 12),
  (1, 6, 0xa8304613#32, 17),
  (1, 7, 0xfd469501#32, 22),
  (1, 8, 0x698098d8#32, 7),
  (1, 9, 0x8b44f7af#32, 12),
  (1, 10, 0xffff5bb1#32, 17),
  (1, 11, 0x895cd7be#32, 22),
  (1, 12, 0x6b901122#32, 7),
  (1, 13, 0xfd987193#32, 12),
  (1, 14, 0xa679438e#32, 17),
  (1, 15, 0x49b40821#32, 22),
  (2, 1, 0xf61e2562#32, 5),
  (2, 6, 0xc040b340#32, 9),
  (2, 11, 0x265e5a51#32, 14),
  (2, 0, 0xe9b6c7aa#32, 20),
  (2, 5, 0xd62f105d#32, 5),
  (2, 10, 0x02441453#32, 9),
  (2, 15, 0xd8a1e681#32, 14),
  (2, 4, 0xe7d3fbc8#32, 20),
  (2, 9, 0x21e1cde6#32, 5),
  (2, 14, 0xc33707d6#32, 9),
  (2, 3, 0xf4d50d87#32, 14),
  (2, 8, 0x455a14ed#32, 20),
  (2, 13, 0xa9e3e905#32, 5),
  (2, 2, 0xfcefa3f8#32, 9),
  (2, 7, 0x676f02d9#32, 14),
  (2, 12, 0x8d2a4c8a#32, 20),
  (3, 5, 0xfffa3942#32, 4),
  (3, 8, 0x8771f681#32, 11),
  (3, 11, 0x6d9d6122#32, 16),
  (3, 14, 0xfde5380c#32, 23),
  (3, 1, 0xa4beea44#32, 4),
  (3, 4, 0x4bdecfa9#32, 11),
  (3, 7, 0xf6bb4b60#32, 16),
  (3, 10, 0xbebfbc70#32, 23),
  (3, 13, 0x289b7ec6#32, 4),
  (3, 0, 0xeaa127fa#32, 11),
  (3, 3, 0xd4ef3085#32, 16),
  (3, 6, 0x04881d05#32, 23),
  (3, 9, 0xd9d4d039#32, 4),
  (3, 12, 0xe6db99e5#32, 11),
  (3, 15, 0x1fa27cf8#32, 16),
  (3, 2, 0xc4ac5665#32, 23),
  (4, 0, 0xf4292244#32, 6),
  (4, 7, 0x432aff97#32, 10),
  (4, 14, 0xab9423a7#32, 15),
  (4, 5, 0xfc93a039#32, 21),
  (4, 12, 0x655b59c3#32, 6),
  (4, 3, 0x8f0ccc92#32, 10),
  (4, 10, 0xffeff47d#32, 15),
  (4, 1, 0x85845dd1#32, 21),
  (4, 8, 0x6fa87e4f#32, 6),
  (4, 15, 0xfe2ce6e0#32, 10),
  (4, 6, 0xa3014314#32, 15),
  (4, 13, 0x4e0811a1#32, 21),
  (4, 4, 0xf7537e82#32, 6),
  (4, 11, 0xbd3af235#32, 10),
  (4, 2, 0x2ad7d2bb#32, 15),
  (4, 9, 0xeb86d391#32, 21)]

private def md5Block (state : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32)
    (bytes : List UInt8) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let words := (List.range 16).map fun i => BitVec.ofNat 32
    (((bytes.drop (4 * i)).take 4).reverse.foldl (fun n b => 256 * n + b.toNat) 0)
  let (a, b, c, d) := md5Steps.foldl (fun (a, b, c, d) (f, i, k, r) =>
    let mix := if f = 1 then d ^^^ (b &&& (c ^^^ d))
      else if f = 2 then c ^^^ (d &&& (b ^^^ c))
      else if f = 3 then b ^^^ c ^^^ d else c ^^^ (b ||| ~~~d)
    let t := a + mix + words[i]! + k
    (d, b + ((t <<< r) ||| (t >>> (32 - r))), b, c)) state
  (state.1 + a, state.2.1 + b, state.2.2.1 + c, state.2.2.2 + d)

/-- Little-endian digest bytes, with the runtime's 64-bit bit-length suffix. -/
def md5 (bytes : List UInt8) : List UInt8 :=
  let bitlen := bytes.length * 8
  let padded := bytes ++ [128] ++ List.replicate ((119 - bytes.length % 64) % 64) 0 ++
    (List.range 8).map (fun i => (bitlen / 256^i % 256).toUInt8)
  let state := (List.range (padded.length / 64)).foldl (fun state i =>
    md5Block state ((padded.drop (64 * i)).take 64))
    (0x67452301#32, 0xefcdab89#32, 0x98badcfe#32, 0x10325476#32)
  [state.1, state.2.1, state.2.2.1, state.2.2.2].flatMap fun w =>
    (List.range 4).map fun i => (w.toNat / 256^i % 256).toUInt8

end OCaml.Bytecode
