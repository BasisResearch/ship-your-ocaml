"""Generated block certificates of the channel-opening path on this ELF:
newlib's `lseek` → `_lseek_r` → htif.c's `_lseek` on a non-file descriptor
(ESPIPE/EBADF: -1), `caml_open_descriptor_in` (allocate, seek, initialize,
link at the head of `caml_all_opened_channels`), and the two primitives
`caml_ml_open_descriptor_{in,out}`, which differ only in `max := NULL`."""
from ocaml_argv_tuple import emit_tuple_blocks

FLAG = '--ocaml-channel'


def AUIPC_SUM(pc, word, lo):
    """`auipc` (instruction `word` at `pc`) plus the 12-bit `lo`, as a literal."""
    return (f"(show {pc}#64 + BitVec.signExtend 64 (BitVec.extractLsb' 12 20 {word}#32 +++ 0#12) + "
            f"{lo % (1 << 64)}#64 = {(pc + (word & ~0xfff) + lo) % (1 << 64)}#64 by decide)")


def AUIPC_FACT(pc, word, lo):
    """A global store's address, `auipc` (instruction `word` at `pc`) minus `|lo|`, as a `Nat` literal."""
    return (f"(show ({pc}#64 + BitVec.signExtend 64 (BitVec.extractLsb' 12 20 {word}#32 +++ 0#12) - {-lo}#64).toNat = "
            f"{(pc + (word & ~0xfff) + lo) % (1 << 64)} by decide)")


def functions_spec(ld, rest):
    """(function, stem, namespace, route, taken blocks, [(start, name, keys, regs[, access])])."""
    return [
      # `lseek(fd, off, whence)`: `_lseek_r(_impure_ptr, fd, off, whence)`.
      ('lseek', 'Lseek', 'Lseek', {}, (), [
        (0x80042574, 'tail', [1, 10, 11, 12],
         f'[(11, R 10), (12, R 11), (13, R 12), (10, {ld(0)}), (14, R 10), {rest([1])}]',
         {'mem': [('2147895544#64', 'global')]}),
      ]),
      # `_lseek_r(r, fd, off, whence)`: clear errno, `_lseek`, copy errno into r on -1.
      ('_lseek_r', '_lseek_r', 'LseekR', {0x80042358: 'T', 0x80042374: 'T'}, ('check', 'errno'), [
        (0x80042328, 'pro', [1, 2, 8, 10, 11, 12, 13],
         f'[(15, 2147898184#64), (10, R 11), (12, R 13), (8, R 10), (11, R 12), (2, R 2 - 16#64), {rest([1, 13])}]',
         {'mem': [('R 2 - 16#64', 'window'), ('R 2 - 16#64 + 8#64', 'window'), ('2147896648#64', 'global')],
          'log': '[((R 2 - 16#64).toNat, 8, R 8), ((R 2 - 16#64 + 8#64).toNat, 8, R 1), (2147896648, 4, 0#64)]',
          'logFacts': ['imm20Of', AUIPC_FACT(0x80042348, 0x00023797, -1536)]}),
        (0x80042354, 'check', [1, 2, 8, 10], f'[(15, 18446744073709551615#64), {rest([1, 2, 8, 10])}]', {}),
        (0x8004236c, 'errno', [1, 2, 8, 10], f'[(15, {ld(0, "lw")}), {rest([1, 2, 8, 10])}]',
         {'mem': [('2147896648#64', 'global')]}),
        (0x8004235c, 'done', [2, 10], f'[(2, R 2 + 16#64), (8, {ld(1)}), (1, {ld(0)}), (10, R 10)]',
         {'mem': [('R 2 + 8#64', 'window'), ('R 2', 'window')], 'ra': 0}),
      ]),
      # `_lseek(fd, off, whence)` on a live non-file descriptor: ESPIPE.
      ('_lseek', '_lseek', 'HtifLseek', {0x800010a8: 'T', 0x800010cc: 'F', 0x800010ec: 'F', 0x800010f4: 'F',
                                        0x800010fc: 'T'}, ('ready', 'kind'), [
        (0x80001098, 'ready', [1, 2, 10, 11, 12], f'[(2, R 2 - 48#64), (15, {ld(0, "lw")}), {rest([1, 10, 11, 12])}]',
         {'mem': [('2147895576#64', 'global'), ('R 2 - 48#64 + 40#64', 'window')],
          'log': '[((R 2 - 48#64 + 40#64).toNat, 8, R 1)]'}),
        (0x800010c8, 'range', [1, 2, 10, 11, 12], f'[(15, 31#64), {rest([1, 2, 10, 11, 12])}]', {}),
        (0x800010d0, 'slot', [1, 2, 10, 11, 12],
         f'[(17, {ld(0, "lw")}), (13, 2147896728#64 + (R 10 <<< 1 + R 10) <<< 3), (16, 2147896728#64), (15, R 10 <<< 1), '
         f'{rest([1, 2, 10, 11, 12])}]',
         {'mem': [('2147896728#64 + (R 10 <<< 1 + R 10) <<< 3', 'window')], 'addrSimpOnly': True,
          'addrFacts': ['imm20Of', AUIPC_SUM(0x800010dc, 0x00064817, -836)]}),
        (0x800010f0, 'whence', [1, 2, 10, 11, 12, 17], f'[(14, 2#64), {rest([1, 2, 10, 11, 12, 17])}]', {}),
        (0x800010f8, 'kind', [1, 2, 10, 17], f'[(6, 4#64), {rest([1, 2, 10, 17])}]', {}),
        (0x80001180, 'espipe', [1, 2, 10], f'[{rest([1, 2, 10])}]', {}),
        (0x80001184, 'fail', [2, 10], f'[(10, 18446744073709551615#64), (15, 29#64), {rest([2])}]',
         {'mem': [('R 10', 'window')], 'log': '[((R 10).toNat, 4, 29#64)]'}),
        (0x80001124, 'done', [2, 10], f'[(2, R 2 + 48#64), (1, {ld(0)}), (10, R 10)]',
         {'mem': [('R 2 + 40#64', 'window')], 'ra': 0}),
      ]),
      # `caml_open_descriptor_in(fd)`: allocate the record, seek, initialize,
      # and link it at the head of `caml_all_opened_channels` (empty or not).
      ('caml_open_descriptor_in', 'Caml_open_descriptor_in', 'OpenDescriptor', {0x800151b4: 'TF'}, ('first',), [
        (0x80015130, 'pro', [1, 2, 8, 9, 10, 18],
         f'[(10, 65616#64), (18, R 10), (2, R 2 - 32#64), {rest([1, 8, 9])}]',
         {'mem': [('R 2 - 32#64', 'window'), ('R 2 - 32#64 + 24#64', 'window'), ('R 2 - 32#64 + 16#64', 'window'),
                  ('R 2 - 32#64 + 8#64', 'window')],
          'log': '[((R 2 - 32#64).toNat, 8, R 18), ((R 2 - 32#64 + 24#64).toNat, 8, R 1), '
                 '((R 2 - 32#64 + 16#64).toNat, 8, R 8), ((R 2 - 32#64 + 8#64).toNat, 8, R 9)]'}),
        (0x80015154, 'fd', [1, 2, 10, 18], f'[(8, R 10), {rest([1, 2, 10, 18])}]',
         {'mem': [('R 10', 'window')], 'log': '[((R 10).toNat, 4, R 18)]'}),
        (0x80015160, 'seek', [1, 2, 8, 18], f'[(10, R 18), (11, 0#64), (12, 1#64), {rest([1, 2, 8, 18])}]', {}),
        (0x80015170, 'offset', [1, 2, 8, 10], f'[{rest([1, 2, 8, 10])}]',
         {'mem': [('R 8 + 8#64', 'window')], 'log': '[((R 8 + 8#64).toNat, 8, R 10)]'}),
      ] + [
        (0x80015178, name, [2, 8, 10],
         f'[(9, R 8 + 65536#64), (15, R 8 + 65608#64), (13, R 8 + 72#64), (14, {ld(0)}), {rest([2, 8, 10])}]',
         {'mem': [('2147896128#64', 'global')] + [(f'R 8 + {k}#64', 'window') for k in (40, 64, 56, 16, 32, 24, 48)]
                 + [('R 8 + 65536#64 + 72#64', 'window')],
          'log': f'[((R 8 + 40#64).toNat, 8, 0#64), ((R 8 + 64#64).toNat, 8, 0#64), ((R 8 + 56#64).toNat, 8, 0#64), '
                 f'((R 8 + 16#64).toNat, 8, R 8 + (65536#64 + 72#64)), ((R 8 + 32#64).toNat, 8, R 8 + 72#64), '
                 f'((R 8 + 24#64).toNat, 8, R 8 + 72#64), ((R 8 + 48#64).toNat, 8, {ld(0)}), '
                 f'((R 8 + 65536#64 + 72#64).toNat, 8, 0#64)]',
          'logFacts': ['imm20Of', "show BitVec.signExtend 64 (BitVec.extractLsb' 12 20 66743#32 +++ 0#12) = 65536#64 by decide"]})
        for name in ('first', 'link')
      ] + [
        (0x800151b8, 'prev', [2, 8, 10, 14], f'[{rest([2, 8, 10, 14])}]',
         {'mem': [('R 14 + 56#64', 'window')], 'log': '[((R 14 + 56#64).toNat, 8, R 8)]'}),
        (0x800151bc, 'done', [2, 8],
         f'[(2, R 2 + 32#64), (18, {ld(3)}), (9, {ld(2)}), (8, {ld(1)}), (10, R 8), (15, 2147897792#64), (1, {ld(0)})]',
         {'mem': [('R 2 + 24#64', 'window'), ('2147896128#64', 'global'), ('R 2 + 16#64', 'window'),
                  ('R 2 + 8#64', 'window'), ('R 2', 'window')],
          'log': '[(2147896128, 8, R 8)]', 'ra': 0, 'logFacts': ['imm20Of', AUIPC_FACT(0x800151c0, 0x00050797, -1664)]}),
      ]),
    ] + [ml_open(ld, rest, out) for out in (False, True)]


def ml_open(ld, rest, out):
    """`caml_ml_open_descriptor_{in,out}(vfd)`: open the record, mark it
    managed by the GC (flags |= 4, refcount + 1), `max := NULL` for output,
    and wrap it in a custom block (`caml_alloc_channel`, inlined)."""
    base = 0x80015f50 if out else 0x80015ef0
    stem = 'out' if out else 'in'
    fields = [('R 10 + 68#64', 'window'), ('R 10 + 64#64', 'window')] + ([('R 10 + 32#64', 'window')] if out else []) \
        + [('R 10 + 68#64', 'window'), ('R 10 + 64#64', 'window')]
    count = 'BitVec.signExtend 64 (Sail.BitVec.extractLsb (bytesVal .lw (loads.getD (0 + 1) []) + 1#64) 31 0)'
    return (f'caml_ml_open_descriptor_{stem}', f'Caml_ml_open_descriptor_{stem}', 'OpenOut' if out else 'OpenIn', {}, (), [
        (base, 'pro', [1, 2, 8, 10],
         f'[(10, BitVec.signExtend 64 (BitVec.extractLsb 31 0 (Functions.shift_bits_right_arith (R 10) 1#6))), '
         f'(2, R 2 - 16#64), {rest([1, 8])}]',
         {'mem': [('R 2 - 16#64 + 8#64', 'window'), ('R 2 - 16#64', 'window')],
          'log': '[((R 2 - 16#64 + 8#64).toNat, 8, R 1), ((R 2 - 16#64).toNat, 8, R 8)]'}),
        (base + 0x18, 'flags', [1, 2, 10],
         f'[(10, 2147891728#64), (11, 8#64), (12, 65616#64), (8, R 10), (15, {count}), (14, {ld(0, "lw")} ||| 4#64), {rest([1, 2])}]',
         {'mem': fields,
          'log': '[' + ('((R 10 + 32#64).toNat, 8, 0#64), ' if out else '')
                 + f'((R 10 + 68#64).toNat, 4, {ld(0, "lw")} ||| 4#64), ((R 10 + 64#64).toNat, 4, {count})]'}),
        (base + (0x50 if out else 0x4c), 'done', [2, 8, 10], f'[(2, R 2 + 16#64), (8, {ld(1)}), (1, {ld(0)}), (10, R 10)]',
         {'mem': [('R 10 + 8#64', 'window'), ('R 2 + 8#64', 'window'), ('R 2', 'window')],
          'log': '[((R 10 + 8#64).toNat, 8, R 8)]', 'ra': 0}),
    ])



def emit_channel(root, functions, decode, code, text_base, lib, build_cfg, literal):
    ld = lambda n, k='ld': f'bytesVal .{k} (loads.getD {n} [])'
    rest = lambda ks: ', '.join(f'({k}, R {k})' for k in ks)
    result = {}
    args = (root, functions, decode, code, text_base, lib, build_cfg, literal)
    for fn, stem, ns, route, taken, fblocks in functions_spec(ld, rest):
        sel = [(blk[1], blk[2], blk[3], blk[1] in taken) + tuple(blk[4:]) for blk in fblocks]
        result.update(emit_tuple_blocks(*args, fn, stem, f'OCaml.Vm.Primitives.Channel.{ns}',
            f'OCaml/Vm/Primitives/Channel/{ns}.lean', sel, starts=[blk[0] for blk in fblocks],
            chunked=(), flag=FLAG, route=route))
    return result
