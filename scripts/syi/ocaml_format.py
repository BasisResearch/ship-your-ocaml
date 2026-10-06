"""Generated block certificates of `caml_format_int`'s `"%d"` path on this ELF:
`parse_format` (string length, suffix length, the two copies, the conversion
byte), `caml_string_length`, `caml_alloc_sprintf` (the short-result path) and
`caml_format_int` (the signed conversion)."""
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
      ('parse_format', 'Parse_format', 'ParseFormat', {0x80010440: 'F', 0x80010474: 'T'}, ('plain',), [
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
      # `caml_format_int(fmt, arg)` for a signed conversion ('d', 'i'):
      # parse_format into a 32-byte stack buffer, then caml_alloc_sprintf(buf, Long_val(arg)).
      ('caml_format_int', 'Caml_format_int', 'FormatInt', {0x80010944: 'F', 0x8001095c: 'T'}, ('mask',), [
        (0x80010918, 'pro', [1, 2, 8, 10, 11],
         f'[(11, 2147831944#64), (8, R 11), (12, R 2 + 18446744073709551568#64), (2, R 2 + 18446744073709551568#64), {rest([1, 10])}]',
         {'mem': [('R 2 - 48#64 + 32#64', 'window'), ('R 2 - 48#64 + 40#64', 'window')],
          'log': '[((R 2 - 48#64 + 32#64).toNat, 8, R 8), ((R 2 - 48#64 + 40#64).toNat, 8, R 1)]'}),
        (0x80010938, 'kind', [1, 2, 8, 10],
         f'[(15, 32#64), (10, BitVec.signExtend 64 (Sail.BitVec.extractLsb (R 10 + 18446744073709551528#64) 31 0) &&& 255#64), {rest([1, 2, 8])}]', {}),
        (0x80010948, 'mask', [1, 2, 8, 10], f'[(15, 4840226817#64 >>> ((R 10).toNat % 64) &&& 1#64), {rest([1, 2, 8, 10])}]', {}),
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
    return result
