"""Native integer-format certificates and caller composition on the pinned ELF.
The bounded parser includes l/n/L compression; the caller executes both signed
and unsigned argument routes through the actual alloc_sprintf call entry."""
from ocaml_argv_tuple import emit_tuple_blocks

FLAG = '--ocaml-format'


def functions_spec(ld, rest):
    """(function, stem, namespace, route, taken blocks, [(start, name, keys, regs)])."""
    return [
      # `caml_string_length(s)`: the header's word size, minus the padding byte.
      ('caml_string_length', 'Caml_string_length', 'StringLength', {}, (), [
        (0x80013570, 'length', [1, 10],
         f'[(10, {ld(0)} >>> 10 <<< 3 + (18446744073709551615#64 + -{ld(1, "lbu")})), (15, {ld(0)} >>> 10 <<< 3 + 18446744073709551615#64), {rest([1])}]',
         {'mem': [('R 10 + 18446744073709551608#64', 'window'),
                  ('R 10 + (@0 >>> 10 <<< 3 + 18446744073709551615#64)', 'window')], 'addrSimpOnly': True}),
      ]),
      # `parse_format(fmt, suffix, buf)`: copy fmt and the suffix into buf,
      # then the conversion byte and the terminator; returns the conversion.
      ('parse_format', 'Parse_format', 'ParseFormat', {0x80010440: 'F', 0x80010474: 'TF'}, ('plain',), [
        (0x800103fc, 'pro', [1, 2, 8, 9, 10, 11, 12, 18, 19, 20],
         f'[(20, R 10), (8, R 12), (18, R 11), (2, R 2 - 48#64), {rest([1, 9, 10, 11, 12, 19])}]',
         {'mem': [(f'R 2 - 48#64 + {k}#64', 'window') for k in (40, 32, 16, 8)] + [('R 2 - 48#64', 'window'),
                  ('R 2 - 48#64 + 24#64', 'window')],
          'log': '[((R 2 - 48#64 + 40#64).toNat, 8, R 1), ((R 2 - 48#64 + 32#64).toNat, 8, R 8), '
                 '((R 2 - 48#64 + 16#64).toNat, 8, R 18), ((R 2 - 48#64 + 8#64).toNat, 8, R 19), '
                 '((R 2 - 48#64).toNat, 8, R 20), ((R 2 - 48#64 + 24#64).toNat, 8, R 9)]'}),
        (0x80010428, 'suffix', [1, 2, 8, 10, 18, 20],
         f'[(10, R 18), (19, R 10), {rest([1, 2, 8, 18, 20])}]', {}),
        (0x80010434, 'fits', [1, 2, 8, 10, 18, 19, 20],
         f'[(14, 31#64), (15, R 19 + R 10 + 1#64), {rest([1, 2, 8, 10, 18, 19, 20])}]', {}),
        (0x80010444, 'copy', [1, 2, 8, 10, 18, 19, 20],
         f'[(10, R 8), (11, R 20), (9, R 10), (12, R 19), {rest([1, 2, 8, 18, 19, 20])}]', {}),
        (0x80010458, 'plain', [1, 2, 8, 9, 10, 18, 19],
         f'[(13, BitVec.signExtend 64 (Sail.BitVec.extractLsb ({ld(0, "lbu")} + 18446744073709551540#64) 31 0) &&& 255#64), '
         f'(8, {ld(1, "lbu")}), (14, 34#64), (15, R 8 + (R 19 - 1#64)), (19, R 19 - 1#64), {rest([1, 2, 9, 10, 18])}]',
         {'mem': [('R 8 + (R 19 + 18446744073709551615#64) + 18446744073709551615#64', 'window'),
                  ('R 8 + (R 19 + 18446744073709551615#64)', 'window')], 'addrSimpOnly': True}),
        (0x80010458, 'annotation_test', [1, 2, 8, 9, 10, 18, 19],
         f'[(13, BitVec.signExtend 64 (Sail.BitVec.extractLsb ({ld(0, "lbu")} + 18446744073709551540#64) 31 0) &&& 255#64), '
         f'(8, {ld(1, "lbu")}), (14, 34#64), (15, R 8 + (R 19 - 1#64)), (19, R 19 - 1#64), {rest([1, 2, 9, 10, 18])}]',
         {'mem': [('R 8 + (R 19 + 18446744073709551615#64) + 18446744073709551615#64', 'window'),
                  ('R 8 + (R 19 + 18446744073709551615#64)', 'window')], 'addrSimpOnly': True}),
        (0x80010478, 'annotation', [1, 2, 8, 9, 10, 13, 15, 18, 19],
         f'[(15, R 15 - (21474836481#64 >>> ((R 13).toNat % 64) &&& 1#64)), '
         f'(14, 21474836481#64 >>> ((R 13).toNat % 64) &&& 1#64), {rest([1, 2, 8, 9, 10, 13, 18, 19])}]', {}),
        (0x80010490, 'append', [1, 2, 8, 9, 10, 15, 18],
         f'[(10, R 15), (12, R 9), (11, R 18), {rest([1, 2, 8, 9, 15, 18])}]', {}),
        (0x800104a0, 'finish', [2, 8, 9, 10],
         f'[(2, R 2 + 48#64), (20, {ld(5)}), (19, {ld(4)}), (18, {ld(3)}), (9, {ld(2)}), (8, {ld(1)}), (10, R 8), (1, {ld(0)}), (15, R 10 + R 9)]',
         {'mem': [('R 10 + R 9', 'window'), ('R 10 + R 9 + 1#64', 'window')]
                 + [(f'R 2 + {k}#64', 'window') for k in (40, 32, 24, 16, 8)] + [('R 2', 'window')],
          'log': '[((R 10 + R 9).toNat, 1, R 8), ((R 10 + R 9 + 1#64).toNat, 1, 0#64)]', 'ra': 0}),
      ]),
      # `caml_alloc_sprintf(fmt, ...)`: vsnprintf into a 128-byte stack buffer;
      # a result under 128 bytes becomes an OCaml string by caml_alloc_initialized_string.
      ('caml_alloc_sprintf', 'Caml_alloc_sprintf', 'AllocSprintf', {0x80013f14: 'F'}, (), [
        (0x80013ec4, 'pro', [1, 2, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18],
         f'[(11, 128#64), (10, R 2 + 18446744073709551392#64), (13, R 2 + 18446744073709551560#64), (18, R 10), (12, R 10), '
         f'(8, R 2 + 18446744073709551560#64), (2, R 2 + 18446744073709551376#64), {rest([1, 14, 15, 16, 17])}]',
         {'mem': [(f'R 2 - 240#64 + {k}#64', 'window') for k in (160, 144, 184, 192, 200, 216, 168, 208, 224, 232, 8)],
          'log': '[((R 2 - 240#64 + 160#64).toNat, 8, R 8), ((R 2 - 240#64 + 144#64).toNat, 8, R 18), '
                 '((R 2 - 240#64 + 184#64).toNat, 8, R 11), ((R 2 - 240#64 + 192#64).toNat, 8, R 12), '
                 '((R 2 - 240#64 + 200#64).toNat, 8, R 13), ((R 2 - 240#64 + 216#64).toNat, 8, R 15), '
                 '((R 2 - 240#64 + 168#64).toNat, 8, R 1), ((R 2 - 240#64 + 208#64).toNat, 8, R 14), '
                 '((R 2 - 240#64 + 224#64).toNat, 8, R 16), ((R 2 - 240#64 + 232#64).toNat, 8, R 17), '
                 '((R 2 - 240#64 + 8#64).toNat, 8, R 2 - 240#64 + 184#64)]'}),
        (0x80013f10, 'fits', [1, 2, 8, 10, 18], f'[(15, 127#64), {rest([1, 2, 8, 10, 18])}]', {}),
        (0x80013f18, 'copy', [1, 2, 8, 10, 18], f'[(11, R 2 + 16#64), {rest([1, 2, 8, 10, 18])}]', {}),
        (0x80013f20, 'done', [2, 10],
         f'[(2, R 2 + 240#64), (18, {ld(2)}), (8, {ld(1)}), (10, R 10), (1, {ld(0)})]',
         {'mem': [(f'R 2 + {k}#64', 'window') for k in (168, 160, 144)], 'ra': 0}),
      ]),
      # caml_format_int: full parser, native conversion mask and both argument routes.
      ('caml_format_int', 'Caml_format_int', 'FormatInt', {0x80010944: 'F', 0x8001095c: 'TF'}, ('mask',), [
        (0x80010918, 'pro', [1, 2, 8, 10, 11],
         f'[(11, 2147831944#64), (8, R 11), (12, R 2 + 18446744073709551568#64), (2, R 2 + 18446744073709551568#64), {rest([1, 10])}]',
         {'mem': [('R 2 - 48#64 + 32#64', 'window'), ('R 2 - 48#64 + 40#64', 'window')],
          'log': '[((R 2 - 48#64 + 32#64).toNat, 8, R 8), ((R 2 - 48#64 + 40#64).toNat, 8, R 1)]'}),
        (0x80010938, 'kind', [1, 2, 8, 10],
         f'[(15, 32#64), (10, BitVec.signExtend 64 (Sail.BitVec.extractLsb (R 10 + 18446744073709551528#64) 31 0) &&& 255#64), {rest([1, 2, 8])}]', {}),
        (0x80010948, 'mask', [1, 2, 8, 10], f'[(15, 4840226817#64 >>> ((R 10).toNat % 64) &&& 1#64), {rest([1, 2, 8, 10])}]', {}),
        (0x80010948, 'unsigned_mask', [1, 2, 8, 10], f'[(15, 4840226817#64 >>> ((R 10).toNat % 64) &&& 1#64), {rest([1, 2, 8, 10])}]', {}),
        (0x80010960, 'unsigned', [1, 2, 8],
         f'[(10, R 2), (11, R 8 >>> 1), {rest([1, 2, 8])}]', {}),
        (0x8001097c, 'signed', [1, 2, 8],
         f'[(10, R 2), (11, Functions.shift_bits_right_arith (R 8) 1#6), {rest([1, 2, 8])}]', {}),
        (0x80010988, 'done', [2, 10], f'[(2, R 2 + 48#64), (8, {ld(1)}), (1, {ld(0)}), (10, R 10)]',
         {'mem': [('R 2 + 40#64', 'window'), ('R 2 + 32#64', 'window')], 'ra': 0}),
      ]),
    ]


def emit_format(root, functions, decode, code, text_base, lib, build_cfg, literal):
    ld = lambda n, k='ld': f'bytesVal .{k} (loads.getD {n} [])'
    rest = lambda ks: ', '.join(f'({k}, R {k})' for k in ks)
    result = {}
    args = (root, functions, decode, code, text_base, lib, build_cfg, literal)
    for fn, stem, ns, route, taken, fblocks in functions_spec(ld, rest):
        sel = [(blk[1], blk[2], blk[3], blk[1] in taken) + tuple(blk[4:]) for blk in fblocks]
        result.update(emit_tuple_blocks(*args, fn, stem, f'OCaml.Vm.Primitives.Format.{ns}',
            f'OCaml/Vm/Primitives/Format/{ns}.lean', sel, starts=[blk[0] for blk in fblocks],
            chunked=(), flag=FLAG, route=route))
    target = root / 'OCaml/Vm/Primitives/Format/FormatInt.lean'
    extra_imports = ('import OCaml.Bytecode.IntegerFormatFacts\n'
                     'import OCaml.Vm.Primitives.Format.ParseFormatCall\n'
                     'import OCaml.Vm.Primitives.TagArithmetic\n'
                     'import OCaml.Vm.Sim.DivisionArithmetic\n'
                     'import OCaml.Vm.Boot.Startup.DomainRecord\n')
    result[target] = extra_imports + result[target] + FORMAT_CALLER
    return result

# Native caller composition, emitted with its decoded block certificates.
FORMAT_CALLER = r"""
namespace OCaml.Vm.Primitives.Format.FormatInt
set_option autoImplicit false
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open OCaml.Bytecode OCaml.Vm.Boot.Startup LeanRV64DExecutable
open ParseFormat

def unsignedConversion (conv : BitVec 8) : Bool :=
  [0x75#8, 0x78#8, 0x58#8, 0x6f#8].contains conv

def conversionIndex (conv : BitVec 8) : BitVec 64 :=
  BitVec.signExtend 64 (Sail.BitVec.extractLsb (conv.setWidth 64 + 18446744073709551528#64) 31 0) &&& 255#64

/-- Every supported conversion reaches the switch mask; the mask selects
Long_val for d/i and Unsigned_long_val for u/x/X/o. -/
theorem conversion_table : ∀ k : Fin 256,
    k.val ∈ [100, 105, 117, 120, 88, 111] →
    let conv := BitVec.ofNat 8 k.val
    guardB .BLTU 32#64 (conversionIndex conv) = false ∧
    guardB .BEQ (4840226817#64 >>> ((conversionIndex conv).toNat % 64) &&& 1#64) 0#64 =
      !(unsignedConversion conv) := by
  decide +kernel

theorem conversion_facts (conv : BitVec 8) (supported : conv.toNat ∈ [100, 105, 117, 120, 88, 111]) :
    guardB .BLTU 32#64 (conversionIndex conv) = false ∧
    guardB .BEQ (4840226817#64 >>> ((conversionIndex conv).toNat % 64) &&& 1#64) 0#64 =
      !(unsignedConversion conv) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using conversion_table ⟨conv.toNat, conv.isLt⟩ supported

/-- Logical unboxing is the unsigned 63-bit semantic magnitude. -/
theorem unsigned_argument (n : BitVec 63) : (tag64 n >>> 1) = BitVec.ofNat 64 n.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, tag_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have := n.isLt
  omega

def printfArgument (conv : BitVec 8) (n : BitVec 63) : BitVec 64 :=
  if unsignedConversion conv then BitVec.ofNat 64 n.toNat else n.signExtend 64

def printfLink (conv : BitVec 8) : BitVec 64 :=
  if unsignedConversion conv then unsigned_call.link else signed_call.link

/-- Actual alloc_sprintf entry after executing the native switch and JAL. -/
structure ArgumentReady (live : Nat → Prop) (sp : BitVec 64) (conv : BitVec 8) (n : BitVec 63)
    (before after : Config) : Prop extends LeafInput (printfLink conv) after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some 0x80013ec4#64
  format : gpr after 10 = some sp
  argument : gpr after 11 = some (printfArgument conv n)
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  kept : GprsSame before after [1, 10, 11, 15]

/-- The real switch, signed/unsigned setup and call instruction. -/
theorem setup_argument {live : Nat → Prop} {ra sp : BitVec 64} {conv : BitVec 8} {n : BitVec 63}
    (c : Config) (leaf : LeafInput ra c) (good : VsaOk live c)
    (stack : gpr c 2 = some sp) (arg : gpr c 8 = some (tag64 n))
    (conversion : gpr c 10 = some (conv.setWidth 64))
    (supported : conv.toNat ∈ [100, 105, 117, 120, 88, 111]) :
    FnSummary 0x80010938#64 (fun x => x = c) (ArgumentReady live sp conv n c) := by
  let R := entryRegs c
  have h10 : R 10 = conv.setWidth 64 := entry_value conversion
  have leafR : LeafInput (R 1) c := by rw [show R 1 = ra from entry_value leaf.raReg]; exact leaf
  apply summary_bind (kind_fast c R leafR (holds_entry good [1, 2, 8, 10] (by decide)) (by
    rw [h10]; exact (conversion_facts conv supported).1)) (fun _ p => p.pc)
  intro d p
  have goodD := p.vsaOk good (by decide) (by simp [kind_regs, keysG])
  have kp := GprsSame.of_post p (by decide)
  let R1 := entryRegs d
  have hi : R1 10 = conversionIndex conv := by
    exact (entry_value (gholds_lookup (n := 10) _ p.regs rfl)).trans (by rw [h10]; rfl)
  have leafD : LeafInput (R1 1) d := by
    have pin := kp.get (by decide) (by decide) (by decide) leaf.raReg
    rw [show R1 1 = ra from entry_value pin]
    exact ⟨p.good, p.image, p.minstret, pin, leaf.aligned, p.tick⟩
  let next := if unsignedConversion conv then 0x80010960#64 else 0x8001097c#64
  have M : FnSummary 0x80010948#64 (fun x => x = d)
      (WriteRegistersPost [15] [] d next (R1 10) (mask_regs R1 (mask_loads d.σ.mem R1))) := by
    cases u : unsignedConversion conv
    · simp only [next, u, Bool.false_eq_true, ite_false]
      exact mask_fast d R1 leafD (holds_entry goodD [1, 2, 8, 10] (by decide)) (by
        rw [hi, (conversion_facts conv supported).2, u]; rfl)
    · simp only [next, u, ite_true]
      exact unsigned_mask_fast d R1 leafD (holds_entry goodD [1, 2, 8, 10] (by decide)) (by
        rw [hi, (conversion_facts conv supported).2, u]; rfl)
  apply summary_bind M (fun _ q => q.pc)
  intro e q
  have goodE := q.vsaOk goodD (by decide) (by simp [mask_regs, keysG])
  have kq := GprsSame.of_post q (by decide)
  have ke := kp.trans kq
  let R2 := entryRegs e
  have h2 : R2 2 = sp := entry_value (ke.get (by decide) (by decide) (by decide) stack)
  have h8 : R2 8 = tag64 n := entry_value (ke.get (by decide) (by decide) (by decide) arg)
  have pin := ke.get (by decide) (by decide) (by decide) leaf.raReg
  have leafE : LeafInput (R2 1) e := by
    rw [show R2 1 = ra from entry_value pin]
    exact ⟨q.good, q.image, q.minstret, pin, leaf.aligned, q.tick⟩
  let call := if unsignedConversion conv then unsigned_call else signed_call
  have A : FnSummary next (fun x => x = e)
      (WriteRegistersPost [10, 11] [] e call.pc sp
        [(10, sp), (11, printfArgument conv n), (1, R2 1), (2, R2 2), (8, R2 8)]) := by
    have signedEq : Functions.shift_bits_right_arith (tag64 n) 1#6 = n.signExtend 64 :=
      OCaml.Vm.Sim.unbox_signExtend n
    cases u : unsignedConversion conv
    · simpa only [next, call, u, Bool.false_eq_true, ite_false, signed_regs, signed_loads,
        h2, h8, printfArgument, signedEq] using
        (signed_fast e R2 leafE (holds_entry goodE [1, 2, 8] (by decide)))
    · simpa only [next, call, u, ite_true, unsigned_regs, unsigned_loads, h2, h8,
        printfArgument, unsigned_argument] using
        (unsigned_fast e R2 leafE (holds_entry goodE [1, 2, 8] (by decide)))
  apply summary_bind A (fun _ a => a.pc)
  intro a ap
  have shape : CallShape call := by cases u : unsignedConversion conv <;> simp only [call, u, Bool.false_eq_true, ite_false, ite_true] <;> first | exact signed_call_shape | exact unsigned_call_shape
  have decode : CallDecode call := by cases u : unsignedConversion conv <;> simp only [call, u, Bool.false_eq_true, ite_false, ite_true] <;> first | exact signed_call_decode | exact unsigned_call_decode
  have pins : CallPins call a := by cases u : unsignedConversion conv <;> simp only [call, u, Bool.false_eq_true, ite_false, ite_true] <;> first | exact signed_call_pins ap.image | exact unsigned_call_pins ap.image
  have target : call.target = 0x80013ec4#64 := by cases u : unsignedConversion conv <;> simp only [call, u, Bool.false_eq_true, ite_false, ite_true] <;> first | exact signed_call_target | exact unsigned_call_target
  have link : call.link = printfLink conv := by cases u : unsignedConversion conv <;> simp only [call, printfLink, u, Bool.false_eq_true, ite_false, ite_true]
  have J := call_registers_summary shape decode a pins ap.good ap.image ap.tick ap.minstret
    [(2, R2 2), (8, R2 8), (10, sp), (11, printfArgument conv n)]
    (holds_project ap.regs (by simp [lookupG])) (by change KeysOK [2, 8, 10, 11]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  apply J.weaken (fun _ eq => eq)
  intro after j
  have ka := GprsSame.of_post ap (by decide)
  have kj := GprsSame.of_post j (by decide)
  have kept : GprsSame c after [1, 10, 11, 15] :=
    ⟨fun k lo hi out => ((ke.trans ka).trans kj).same k lo hi (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      omega)⟩
  refine ⟨⟨j.good, j.image, j.minstret, ?_, ?_, j.tick⟩,
    j.vsaOk_of_present (ap.vsaOk goodE (by decide) (by simp [keysG])) (by decide) (by simp [keysG])
      (fun x hx => by rw [j.memory, ap.memory]; exact goodE.live x hx),
    by rw [← target]; exact j.pc,
    gholds_lookup (n := 10) _ j.regs rfl, gholds_lookup (n := 11) _ j.regs rfl,
    j.memory.trans (ap.memory.trans (q.memory.trans p.memory)),
    j.output.trans (ap.output.trans (q.output.trans p.output)), kept⟩
  · rw [← link]; exact gholds_lookup (n := 1) _ j.regs rfl
  · rw [← link]; cases u : unsignedConversion conv <;> simp only [call, u, Bool.false_eq_true, ite_false, ite_true] <;> decide



/-- The format object's payload view used by both semantic and native parsers. -/
def formatByte (fmt : List UInt8) (i : Nat) : BitVec 8 := BitVec.ofNat 8 (fmt.getD i 0).toNat

theorem conversion_byte_table : ∀ k : Fin 256,
    Char.ofNat k.val ∈ ['d', 'i', 'u', 'x', 'X', 'o'] →
    k.val ∈ [100, 105, 117, 120, 88, 111] := by
  decide +kernel

theorem supported_conversion {fmt : List UInt8} (h : IntegerFormatConditions fmt) :
    (formatByte fmt (fmt.length - 1)).toNat ∈ [100, 105, 117, 120, 88, 111] := by
  have long := h.long
  have last : (fmt.map fun b => Char.ofNat b.toNat).getLast? =
      some (Char.ofNat (fmt.getD (fmt.length - 1) 0).toNat) := by
    rw [List.getLast?_map, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    simp only [Option.map_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : fmt.length - 1 < fmt.length), Option.getD_some]
  have supported := h.conversion _ last
  have bound : (fmt.getD (fmt.length - 1) 0).toNat < 256 := UInt8.toNat_lt _
  have fact := conversion_byte_table ⟨_, bound⟩ supported
  simpa only [formatByte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using fact

/-- Initial caller geometry and actual format bytes. No parser execution,
formatting execution or returned runtime state is assumed. -/
structure CallerInput (live : Nat → Prop) (ra : BitVec 64) (sp f : Nat)
    (fmt : List UInt8) (n : BitVec 63) (bytes : List UInt8) (c : Config) : Prop
    extends LeafInput ra c where
  libraryGood : VsaOk live c
  globalPointer : ROHolds (vsaModel live) c roR []
  stack : gpr c 2 = some (BitVec.ofNat 64 (sp + 48))
  format : gpr c 10 = some (BitVec.ofNat 64 f)
  argument : gpr c 11 = some (tag64 n)
  callerFrame : NativeFrame (BitVec.ofNat 64 (sp + 48)) 48
  parserFrame : NativeFrame (BitVec.ofNat 64 sp) 48
  upper : sp + 48 < 0x100000000
  geometry : StringGeometry f fmt.length
  shape : StringShape c f fmt.length
  source : ∀ i, i < fmt.length → byte c (f + i) = formatByte fmt i
  fmtLow : 0x8007d138 ≤ f
  fmtHigh : f + fmt.length ≤ 0x100000000
  /-- The whole object, including header, avoids both native frames. -/
  objectApart : f + 8 * ((fmt.length + 8) / 8) ≤ sp - 48 ∨ sp + 56 ≤ f
  success : formatInteger fmt n = some bytes

/-- Original ra/s0 slots from the real caller's two stores. -/
structure CallerSaved (R : Nat → BitVec 64) (sp : Nat) (c : Config) : Prop where
  ra : word c (sp + 40) = R 1
  s0 : word c (sp + 32) = R 8

/-- Parser return in the real caller, observed relative to the original
caml_format_int input. `cut + 2` is the returned C format's byte length. -/
structure CallerParsed (live : Nat → Prop) (R : Nat → BitVec 64) (sp : Nat)
    (fmt : List UInt8) (n : BitVec 63) (before after : Config) : Prop
    extends LeafInput pro_call.link after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some 0x80010938#64
  stack : gpr after 2 = some (BitVec.ofNat 64 sp)
  argument : gpr after 8 = some (tag64 n)
  conversion : gpr after 10 = some ((formatByte fmt (fmt.length - 1)).setWidth 64)
  length : formatCut fmt.length (formatByte fmt (fmt.length - 2)) + 2 =
    fmt.length + 1 - annotationSize (formatByte fmt (fmt.length - 2))
  prefixBytes : ∀ i, i < formatCut fmt.length (formatByte fmt (fmt.length - 2)) →
    byte after (sp + i) = formatByte fmt i
  suffixByte : byte after (sp + formatCut fmt.length (formatByte fmt (fmt.length - 2))) = 0x6c#8
  conversionByte : byte after (sp + (formatCut fmt.length (formatByte fmt (fmt.length - 2)) + 1)) =
    formatByte fmt (fmt.length - 1)
  nul : byte after (sp + formatCut fmt.length (formatByte fmt (fmt.length - 2)) + 2) = 0#8
  saves : CallerSaved R sp after
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  memory : ∀ x, (x + 1 ≤ sp - 48 ∨ sp + 48 ≤ x) → byte after x = byte before x
  abi : ∀ k ∈ abiSaved, k ≠ 8 → gpr after k = gpr before k

/-- Package the returned native parser observations in a small context.
All source, save-bank and frame inputs are derived by caller_parse below. -/
theorem CallerParsed.of_returned {live : Nat → Prop} {R : Nat → BitVec 64}
    {sp f : Nat} {fmt : List UInt8} {n : BitVec 63} {c entered after : Config}
    (r : ReturnedFormat live pro_call.link (BitVec.ofNat 64 sp) f sp fmt.length
      (formatCut fmt.length (formatByte fmt (fmt.length - 2))) entered after)
    (long : 2 ≤ fmt.length) (fits : fmt.length + 2 < 32)
    (natSp : (BitVec.ofNat 64 sp).toNat = sp)
    (argument : gpr entered 8 = some (tag64 n))
    (sourceE : ∀ i, i < fmt.length → byte entered (f + i) = formatByte fmt i)
    (saves : CallerSaved R sp after)
    (output : Vsa.Machine.output entered.σ = Vsa.Machine.output c.σ)
    (byteE : ∀ x, x + 1 ≤ sp + 32 ∨ sp + 48 ≤ x → byte entered x = byte c x)
    (ke : GprsSame c entered [1, 2, 8, 11, 12]) :
    CallerParsed live R sp fmt n c after := by
  refine ⟨r.toLeafInput, r.libraryGood, r.pc, r.stack, ?_, ?_, ?_, ?_, r.suffixByte, ?_, r.nul, saves,
    r.output.trans output, ?_, ?_⟩
  · rw [r.restored 8 (by simp)]; exact argument
  · rw [r.result, sourceE _ (by omega)]
  · have prev := sourceE (fmt.length - 2) (by omega)
    simpa only [prev] using r.length
  · intro i hi
    rw [r.prefixBytes i hi, sourceE i (by dsimp only [formatCut] at hi; omega)]
  · rw [r.conversion, sourceE _ (by omega)]
  · intro x hx
    rw [r.rest x (by rw [nativeFrameBase, natSp]; omega) (by dsimp only [formatCut]; omega)]
    exact byteE x (by omega)
  · intro k hk ne
    have bounds : 1 ≤ k ∧ k ≤ 31 := by simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    have first : gpr entered k = gpr c k := ke.same k bounds.1 bounds.2 (by
      have hk' := hk
      simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at hk'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      omega)
    by_cases restored : k ∈ [8, 9, 18, 19, 20]
    · exact (r.restored k restored).trans first
    · exact (r.kept k bounds.1 bounds.2 (by
        have hk' := hk
        simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at hk'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at restored
        simp only [parseWritten, List.mem_cons, List.not_mem_nil, or_false]
        omega)).trans first



/-- The caller's two real saves, normalized once for all observers. -/
theorem caller_log {R : Nat → BitVec 64} {sp : Nat}
    (stack : R 2 = BitVec.ofNat 64 (sp + 48)) (upper : sp + 48 < 0x100000000) :
    proLog R [] = [(sp + 32, 8, R 8), (sp + 40, 8, R 1)] := by
  have base : R 2 - 48#64 = BitVec.ofNat 64 sp := by rw [stack, BitVec.ofNat_add, BitVec.add_sub_cancel]
  simp only [proLog, base, ofNat_add_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : sp + 32 < 2^64), Nat.mod_eq_of_lt (by omega : sp + 40 < 2^64)]

/-- The real caller log stays inside its native frame. -/
theorem caller_log_outside {R : Nat → BitVec 64} {sp : Nat}
    (stack : R 2 = BitVec.ofNat 64 (sp + 48)) (upper : sp + 48 < 0x100000000)
    (frame : NativeFrame (BitVec.ofNat 64 (sp + 48)) 48) : ImageOutside (proLog R []) := by
  apply frame.image_outside
  have natTop : (BitVec.ofNat 64 (sp + 48)).toNat = sp + 48 := Nat.mod_eq_of_lt (by omega)
  rw [nativeFrameBase, natTop, Nat.add_sub_cancel, caller_log stack upper]
  simp [LogInW, InsideW]

/-- Actual parser entry produced by the caller's prologue and JAL. -/
structure ParserEntry (live : Nat → Prop) (sp f : Nat) (formatBytes : List UInt8) (n : BitVec 63)
    (before after : Config) : Prop
    extends MeasureInput live pro_call.link (BitVec.ofNat 64 sp) f sp formatBytes.length after where
  pc : OCaml.Vm.pcOf after = some 0x800103fc#64
  bufferGeometry : BufferInput f sp formatBytes.length
  long : 2 ≤ formatBytes.length
  fits : formatBytes.length + 2 < 32
  natSp : (BitVec.ofNat 64 sp).toNat = sp
  argument : gpr after 8 = some (tag64 n)
  source : ∀ i, i < formatBytes.length → byte after (f + i) = formatByte formatBytes i
  saves : CallerSaved (entryRegs before) sp after
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  outside : ∀ x, x + 1 ≤ sp + 32 ∨ sp + 48 ≤ x → byte after x = byte before x
  kept : GprsSame before after [1, 2, 8, 11, 12]

/-- Initial data transported through the two real caller-entry posts. -/
theorem caller_entry_post {live : Nat → Prop} {ra : BitVec 64} {sp f : Nat} {fmt : List UInt8}
    {n : BitVec 63} {bytes : List UInt8} {c d entered : Config}
    (h : CallerInput live ra sp f fmt n bytes c)
    (p : WriteRegistersPost [2, 8, 11, 12] (proLog (entryRegs c) []) c pro_call.pc
      ((entryRegs c) 10) (pro_regs (entryRegs c) []) d)
    (j : RegistersPost [1] d.σ.mem d 0x800103fc#64 (BitVec.ofNat 64 f)
      [(1, pro_call.link), (2, BitVec.ofNat 64 sp), (8, tag64 n),
       (10, BitVec.ofNat 64 f), (11, 0x80055088#64), (12, BitVec.ofNat 64 sp)] entered) :
    ParserEntry live sp f fmt n c entered := by
  let R := entryRegs c
  have accepted := formatInteger_conditions h.success
  have long := accepted.long
  have fits := accepted.fits
  have upper := h.upper
  have lower := h.parserFrame.lower
  have natSp : (BitVec.ofNat 64 sp).toNat = sp := Nat.mod_eq_of_lt (by omega)
  have natTop : (BitVec.ofNat 64 (sp + 48)).toNat = sp + 48 := Nat.mod_eq_of_lt (by omega)
  have h2 : R 2 = BitVec.ofNat 64 (sp + 48) := entry_value h.stack
  have logEq := caller_log h2 upper
  have inside : LogInW [⟨sp + 32, sp + 48⟩] (proLog R []) := by
    rw [logEq]; simp [LogInW, InsideW]
  have out (x w : Nat) (sep : x + w ≤ sp + 32 ∨ sp + 48 ≤ x) : OutLRange (proLog R []) x w :=
    OCaml.Vm.Sim.outLRange_of_windows inside ⟨sep, trivial⟩
  have goodD := p.vsaOk h.libraryGood (by decide) (by simp [pro_regs, keysG])
  have kp := GprsSame.of_post p (by decide)
  have kj := GprsSame.of_post j (by decide)
  have ke := kp.trans kj
  have goodE := j.vsaOk_of_present goodD (by decide) (by simp [keysG])
    (fun x hx => by rw [j.memory]; exact goodD.live x hx)
  have memE : entered.σ.mem = writeLog c.σ.mem (proLog R []) := j.memory.trans p.memory
  have byteE (x : Nat) (sep : x + 1 ≤ sp + 32 ∨ sp + 48 ≤ x) : byte entered x = byte c x := by
    rw [StringLength.byte_getD, memE, writeLog_out _ _ _ (outL_of_range (out x 1 sep) (by omega) (by omega)), ← StringLength.byte_getD]
  have objectOut (x w : Nat) (lo : f - 8 ≤ x)
      (hi : x + w ≤ f + 8 * ((fmt.length + 8) / 8)) : OutLRange (proLog R []) x w := by
    apply out
    have := h.geometry.lower
    rcases h.objectApart with b | b <;> omega
  have shapeE : StringShape entered f fmt.length := by
    refine ⟨?_, ?_⟩
    · have eq := Reloc.bytesT_congr (copied_of_writeLog memE (objectOut (f - 8) 8 (by omega) (by omega)))
      rw [show word entered (f - 8) = word c (f - 8) from eq]; exact h.shape.headerSize
    · rw [byteE _ (by rcases h.objectApart with b | b <;> omega)]; exact h.shape.padding
  have sourceE (i : Nat) (hi : i < fmt.length) : byte entered (f + i) = formatByte fmt i := by
    rw [byteE _ (by have := h.geometry.upper; rcases h.objectApart with b | b <;> omega)]
    exact h.source i hi
  have gpE := globalPointer_of_gpr (show gpr entered 3 = gpr c 3 from ke.same 3 (by decide) (by decide) (by simp)) h.globalPointer
  have pin : gpr entered 1 = some pro_call.link := gholds_lookup (n := 1) _ j.regs rfl
  have input : MeasureInput live pro_call.link (BitVec.ofNat 64 sp) f sp fmt.length entered :=
    ⟨⟨j.good, j.image, j.minstret, pin, by decide, j.tick⟩, goodE, gpE,
      gholds_lookup (n := 2) _ j.regs rfl, gholds_lookup (n := 10) _ j.regs rfl,
      gholds_lookup (n := 11) _ j.regs rfl, gholds_lookup (n := 12) _ j.regs rfl,
      h.parserFrame, h.geometry, shapeE, by
        rw [nativeFrameBase, natSp]
        rcases h.objectApart with b | b <;> omega⟩
  have buffer : BufferInput f sp fmt.length :=
    ⟨by rw [natSp] at lower; unfold Vsa.Sim.DlHeap.heapEnd at lower; omega,
      by omega, by omega, h.fmtLow, h.fmtHigh, by
        have := h.geometry.upper; rcases h.objectApart with b | b <;> omega⟩
  have saves : CallerSaved R sp entered := by
    constructor
    · change bytesT entered.σ.mem (sp + 40) 8 = R 1
      rw [memE, logEq]
      exact word_log_last c.σ.mem [(sp + 32, 8, R 8)] [] (sp + 40) (R 1) (by simp [OutLRange])
    · change bytesT entered.σ.mem (sp + 32) 8 = R 8
      rw [memE, logEq]
      exact word_log_last c.σ.mem [] [(sp + 40, 8, R 1)] (sp + 32) (R 8) (by simp [OutLRange] <;> omega)
  refine ⟨input, j.pc, buffer, long, fits, natSp,
    gholds_lookup (n := 8) _ j.regs rfl, sourceE, saves, ?_, byteE, ?_⟩
  · exact congrArg (fun xs : Array String => String.join xs.toList) (j.output.trans p.output)
  · refine ⟨fun k lo hi out => ke.same k lo hi ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; omega


theorem caller_prologue {live : Nat → Prop} {ra : BitVec 64} {sp f : Nat} {fmt : List UInt8}
    {n : BitVec 63} {bytes : List UInt8} (c : Config)
    (codeLive : ∀ p ∈ snpText, live p.1) (liveImage : ImageLive live)
    (h : CallerInput live ra sp f fmt n bytes c) :
    FnSummary 0x80010918#64 (fun x => x = c) (WriteRegistersPost [2, 8, 11, 12] (proLog (entryRegs c) []) c pro_call.pc
        ((entryRegs c) 10) (pro_regs (entryRegs c) [])) := by
  let R := entryRegs c
  have upper := h.upper
  have natTop : (BitVec.ofNat 64 (sp + 48)).toNat = sp + 48 := Nat.mod_eq_of_lt (by omega)
  have h2 : R 2 = BitVec.ofNat 64 (sp + 48) := entry_value h.stack
  have h10 : R 10 = BitVec.ofNat 64 f := entry_value h.format
  have h11 : R 11 = tag64 n := entry_value h.argument
  have base : R 2 - 48#64 = BitVec.ofNat 64 sp := by rw [h2, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have logEq := caller_log h2 upper
  have proOutside := caller_log_outside h2 upper h.callerFrame
  have proLeaf : LeafInput (R 1) c := by rw [show R 1 = ra from entry_value h.raReg]; exact h.toLeafInput
  have S := pro_fast c R proLeaf (holds_entry h.libraryGood [1, 2, 8, 10, 11] (by decide))
    (by rw [h2, ParseFormat.frame_slot h.callerFrame 32 (by decide)]; exact h.callerFrame.word (by decide) (by decide))
    (by rw [h2, ParseFormat.frame_slot h.callerFrame 40 (by decide)]; exact h.callerFrame.word (by decide) (by decide)) proOutside
  exact S

/-- The generated prologue register observations, with the actual input
arguments substituted once. -/
theorem caller_pro_arguments {R : Nat → BitVec 64} {c d : Config} {sp f : Nat} {n : BitVec 63}
    (p : WriteRegistersPost [2, 8, 11, 12] (proLog R []) c pro_call.pc (R 10) (pro_regs R []) d)
    (base : R 2 - 48#64 = BitVec.ofNat 64 sp)
    (h10 : R 10 = BitVec.ofNat 64 f) (h11 : R 11 = tag64 n) :
    GHolds d.σ [(2, BitVec.ofNat 64 sp), (8, tag64 n), (10, BitVec.ofNat 64 f),
      (11, 0x80055088#64), (12, BitVec.ofNat 64 sp)] := by
  have v : GHolds d.σ [(2, R 2 + 18446744073709551568#64), (8, R 11), (10, R 10),
      (11, 0x80055088#64), (12, R 2 + 18446744073709551568#64)] :=
    holds_project p.regs (by simp [pro_regs, lookupG])
  have address : R 2 + 18446744073709551568#64 = R 2 - 48#64 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  rw [address] at v
  simpa only [base, h11, h10] using v

theorem caller_enter {live : Nat → Prop} {ra : BitVec 64} {sp f : Nat} {fmt : List UInt8}
    {n : BitVec 63} {bytes : List UInt8} (c : Config)
    (codeLive : ∀ p ∈ snpText, live p.1) (liveImage : ImageLive live)
    (h : CallerInput live ra sp f fmt n bytes c) :
    FnSummary 0x80010918#64 (fun x => x = c) (ParserEntry live sp f fmt n c) := by
  apply summary_bind (caller_prologue c codeLive liveImage h) (fun _ p => p.pc)
  intro d p
  have R2 := entry_value h.stack
  have base : (entryRegs c) 2 - 48#64 = BitVec.ofNat 64 sp := by
    rw [R2, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have args := caller_pro_arguments p base (entry_value h.format) (entry_value h.argument)
  have J := call_registers_summary pro_call_shape pro_call_decode d (pro_call_pins p.image)
    p.good p.image p.tick p.minstret _ args (by change KeysOK [2, 8, 10, 11, 12]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl
  rw [pro_call_target] at J
  apply J.weaken (fun _ eq => eq)
  intro entered j
  exact caller_entry_post h p j

/-- The full native parser, composed after the original caller entry. -/
theorem caller_parse {live : Nat → Prop} {ra : BitVec 64} {sp f : Nat} {fmt : List UInt8}
    {n : BitVec 63} {bytes : List UInt8} (c : Config)
    (codeLive : ∀ p ∈ snpText, live p.1) (liveImage : ImageLive live)
    (h : CallerInput live ra sp f fmt n bytes c) :
    FnSummary 0x80010918#64 (fun x => x = c) (CallerParsed live (entryRegs c) sp fmt n c) := by
  apply summary_bind (caller_enter c codeLive liveImage h) (fun _ p => p.pc)
  intro entered p
  have long := p.long
  have fits := p.fits
  apply (parse_format_full_call entered codeLive liveImage p.toMeasureInput p.bufferGeometry long
    (by rw [p.natSp]; exact Nat.le_refl _)).weaken (fun _ eq => eq)
  intro after r
  have prevE := p.source (fmt.length - 2) (by omega)
  rw [prevE] at r
  have keptSlots (off : Nat) (hoff : off = 32 ∨ off = 40) : word after (sp + off) = word entered (sp + off) := by
    apply Reloc.bytesT_congr
    intro i hi
    change byte after (sp + off + i) = byte entered (sp + off + i)
    exact r.rest _ (Or.inr (by rw [p.natSp]; omega)) (Or.inr (by dsimp only [formatCut]; omega))
  have saves : CallerSaved (entryRegs c) sp after :=
    ⟨(keptSlots 40 (Or.inr rfl)).trans p.saves.ra,
      (keptSlots 32 (Or.inl rfl)).trans p.saves.s0⟩
  exact CallerParsed.of_returned r long fits p.natSp p.argument p.source saves p.output p.outside p.kept

/-- The C format bytes at the actual variadic entry. -/
structure FormatObservation (fmt : List UInt8) (sp : Nat) (c : Config) : Prop where
  length : formatCut fmt.length (formatByte fmt (fmt.length - 2)) + 2 =
    fmt.length + 1 - annotationSize (formatByte fmt (fmt.length - 2))
  prefixBytes : ∀ i, i < formatCut fmt.length (formatByte fmt (fmt.length - 2)) →
    byte c (sp + i) = formatByte fmt i
  suffix : byte c (sp + formatCut fmt.length (formatByte fmt (fmt.length - 2))) = 0x6c#8
  conversion : byte c (sp + (formatCut fmt.length (formatByte fmt (fmt.length - 2)) + 1)) =
    formatByte fmt (fmt.length - 1)
  nul : byte c (sp + formatCut fmt.length (formatByte fmt (fmt.length - 2)) + 2) = 0#8

/-- Original caml_format_int input through actual caml_alloc_sprintf entry.
The original return address/s0 are supplied in the caller save bank; the
callee has the real branch-specific return link and represented argument. -/
structure CallerPrefix (live : Nat → Prop) (R : Nat → BitVec 64) (sp : Nat)
    (fmt : List UInt8) (n : BitVec 63) (before after : Config) : Prop
    extends LeafInput (printfLink (formatByte fmt (fmt.length - 1))) after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some 0x80013ec4#64
  stack : gpr after 2 = some (BitVec.ofNat 64 sp)
  format : gpr after 10 = some (BitVec.ofNat 64 sp)
  argument : gpr after 11 = some (printfArgument (formatByte fmt (fmt.length - 1)) n)
  observation : FormatObservation fmt sp after
  saves : CallerSaved R sp after
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  memory : ∀ x, (x + 1 ≤ sp - 48 ∨ sp + 48 ≤ x) → byte after x = byte before x
  abi : ∀ k ∈ abiSaved, k ≠ 8 → gpr after k = gpr before k

/-- Compose the real caller, full parser and both argument routes. -/
theorem caller_prefix {live : Nat → Prop} {ra : BitVec 64} {sp f : Nat} {fmt : List UInt8}
    {n : BitVec 63} {bytes : List UInt8} (c : Config)
    (codeLive : ∀ p ∈ snpText, live p.1) (liveImage : ImageLive live)
    (h : CallerInput live ra sp f fmt n bytes c) :
    FnSummary 0x80010918#64 (fun x => x = c) (CallerPrefix live (entryRegs c) sp fmt n c) := by
  apply summary_bind (caller_parse c codeLive liveImage h) (fun _ r => r.pc)
  intro parsed r
  apply (setup_argument parsed r.toLeafInput r.libraryGood r.stack r.argument r.conversion
    (supported_conversion (formatInteger_conditions h.success))).weaken (fun _ eq => eq)
  intro after a
  refine ⟨a.toLeafInput, a.libraryGood, a.pc,
    a.kept.get (by decide) (by decide) (by decide) r.stack, a.format, a.argument,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨r.length, ?_, ?_, ?_, ?_⟩ <;> simp only [byte, a.memory]
    · exact r.prefixBytes
    · exact r.suffixByte
    · exact r.conversionByte
    · exact r.nul
  · constructor
    · simpa only [word, a.memory] using r.saves.ra
    · simpa only [word, a.memory] using r.saves.s0
  · have output : Vsa.Machine.output after.σ = Vsa.Machine.output parsed.σ := by
      simp only [Vsa.Machine.output, a.output]
    exact output.trans r.output
  · intro x hx
    simpa only [byte, a.memory] using r.memory x hx
  · intro k hk ne
    have bounds : 1 ≤ k ∧ k ≤ 31 := by simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    exact (a.kept.same k bounds.1 bounds.2 (by simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega)).trans (r.abi k hk ne)

/-- Selected allocator blocks survive the entire prefix when their actual
arena lies below the explicit parser frame. -/
theorem CallerPrefix.live {live R sp fmt n before after H}
    (p : CallerPrefix live R sp fmt n before after)
    (frame : NativeFrame (BitVec.ofNat 64 sp) 48) (high : sp < 2^64)
    (bounds : ∀ e ∈ H, Vsa.Sim.DlHeap.heapStart ≤ e.1 ∧ e.1 + e.2 ≤ Vsa.Sim.DlHeap.heapEnd) :
    LiveFrame H before after := by
  apply LiveFrame.of_arena bounds
  intro x lo hi
  have lower := frame.lower
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt high] at lower
  rw [← StringLength.byte_getD after x, ← StringLength.byte_getD before x]
  exact p.memory x (Or.inl (by omega))

/-- Read-only runtime/data/nursery windows below the native frame are kept.
Their actual placement remains explicit for the later formatting supplier. -/
theorem CallerPrefix.window {live R sp fmt n before after a len}
    (p : CallerPrefix live R sp fmt n before after) (below : a + len ≤ sp - 48) :
    OCaml.Vm.Reloc.Copied before after a a len := by
  intro i hi
  exact p.memory (a + i) (Or.inl (by omega))

end OCaml.Vm.Primitives.Format.FormatInt
"""
