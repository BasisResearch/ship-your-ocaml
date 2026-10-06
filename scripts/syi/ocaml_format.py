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
         f'[(10, ({ld(0)} >>> 10 <<< 3) - 1#64 - {ld(1, "lbu")}), (15, ({ld(0)} >>> 10 <<< 3) - 1#64), {rest([1])}]',
         {'mem': [('R 10 - 8#64', 'window'), ('R 10 + ((@0 >>> 10 <<< 3) - 1#64)', 'window')], 'shiftAddr': True}),
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
         {'mem': [('R 8 + (R 19 - 1#64) - 1#64', 'window'), ('R 8 + (R 19 - 1#64)', 'window')]}),
        (0x80010490, 'append', [1, 2, 8, 9, 10, 15, 18],
         f'[(10, R 15), (12, R 9), (11, R 18), {rest([1, 2, 8, 9, 15, 18])}]', {}),
        (0x800104a0, 'finish', [2, 8, 9, 10],
         f'[(2, R 2 + 48#64), (20, {ld(5)}), (19, {ld(4)}), (18, {ld(3)}), (9, {ld(2)}), (8, {ld(1)}), (10, R 8), (1, {ld(0)}), (15, R 10 + R 9)]',
         {'mem': [('R 10 + R 9', 'window'), ('R 10 + R 9 + 1#64', 'window')]
                 + [(f'R 2 + {k}#64', 'window') for k in (40, 32, 24, 16, 8)] + [('R 2', 'window')],
          'log': '[((R 10 + R 9).toNat, 1, R 8), ((R 10 + R 9 + 1#64).toNat, 1, 0#64)]', 'ra': 0}),
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
