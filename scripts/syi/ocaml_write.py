"""Generated block certificates of newlib `_write`'s console path on this
ELF: the fd checks, then one HTIF putchar store per byte, then the return."""
from ocaml_argv_tuple import emit_tuple_blocks

FLAG = '--ocaml-write'
# fs_ready set; fd in range; fd kind neither invalid nor a regular file;
# both outcomes of the empty-buffer test and of the loop back-edge.
ROUTE = {0x80000d7c: 'T', 0x80000d88: 'F', 0x80000dac: 'F', 0x80000db4: 'T',
         0x80000f68: 'TF', 0x80000f80: 'TF'}
TAKEN = ('entry', 'console', 'empty', 'again')


def emit_write(root, functions, decode, code, text_base, lib, build_cfg, literal):
    ld = lambda n, k='ld': f'bytesVal .{k} (loads.getD {n} [])'
    rest = lambda ks: ', '.join(f'({k}, R {k})' for k in ks)
    blocks = [
        (0x80000d54, 'entry', [1, 2, 8, 9, 10, 11, 12, 18],
         f'[(9, R 12), (18, R 11), (8, R 10), (2, R 2 - 96#64), (15, {ld(0, "lw")}), {rest([1, 10, 11, 12])}]'),
        (0x80000d84, 'range', [1, 8, 10], f'[(15, 31#64), {rest([1, 8, 10])}]'),
        (0x80000d8c, 'kind', [1, 8, 10], f'[(11, 1#64), (13, {ld(0, "lw")}), (15, 2147896728#64 + (R 8 <<< 4 + R 8 <<< 3)), (16, 0x80064d98#64), (14, R 8 <<< 1), {rest([1, 8, 10])}]'),
        (0x80000db0, 'console', [1, 10, 13], f'[(12, 4#64), {rest([1, 10, 13])}]'),
        (0x80000f58, 'empty', [1, 9, 10, 18], f'[(14, 257#64 <<< 48), (13, R 18 + R 9), (11, R 18), {rest([1, 9, 10, 18])}]'),
        (0x80000f58, 'start', [1, 9, 10, 18], f'[(14, 257#64 <<< 48), (13, R 18 + R 9), (11, R 18), {rest([1, 9, 10, 18])}]'),
        (0x80000f6c, 'byte', [1, 10, 11, 13, 14], f'[(12, 0x80061f78#64), (15, {ld(0, "lbu")} ||| R 14), (11, R 11 + 1#64), {rest([1, 10, 13, 14])}]'),
        (0x80000f80, 'again', [1, 10, 11, 13], f'[{rest([1, 10, 11, 13])}]'),
        (0x80000f80, 'done', [1, 10, 11, 13], f'[{rest([1, 10, 11, 13])}]'),
        (0x80000f84, 'jump', [1, 10], f'[{rest([1, 10])}]'),
        (0x80000f3c, 'result', [1, 9, 10], f'[(10, R 9), {rest([1, 9])}]'),
        (0x80000f40, 'leave', [2, 10],
         f'[(2, R 2 + 96#64), (18, {ld(3)}), (9, {ld(2)}), (8, {ld(1)}), (1, {ld(0)}), (10, R 10)]'),
    ]
    selected = [(name, keys, regs, name in TAKEN) for _, name, keys, regs in blocks]
    result = emit_tuple_blocks(root, functions, decode, code, text_base, lib, build_cfg, literal,
        '_write', '_write', 'OCaml.Vm.Primitives.ConsoleWrite', 'OCaml/Vm/Primitives/ConsoleWrite.lean',
        selected, starts=[a for a, _, _, _ in blocks], chunked=(), flag=FLAG, route=ROUTE)
    args = (root, functions, decode, code, text_base, lib, build_cfg, literal)
    for fn, stem, ns, route, taken, fblocks in callers(ld, rest):
        sel = [(name, keys, regs, name in taken) for _, name, keys, regs in fblocks]
        result.update(emit_tuple_blocks(*args, fn, stem, f'OCaml.Vm.Primitives.FdWrite.{ns}',
            f'OCaml/Vm/Primitives/FdWrite/{ns}.lean', sel, starts=[a for a, _, _, _ in fblocks],
            chunked=(), flag=FLAG, route=route))
    return result


def callers(ld, rest):
    """`caml_write_fd` and the newlib/runtime functions on its console path."""
    saved = [18, 19, 20, 21, 22, 23]
    return [
      ('caml_write_fd', 'Caml_write_fd', 'WriteFd', {0x800252d4: 'T'}, ('check',), [
        (0x80025274, 'pro', [1, 2, 8, 9, 10, 12, 13] + saved,
         f'[(21, 1#64), (18, 11#64), (20, 4#64), (19, 18446744073709551615#64), (23, R 12), (22, R 10), (9, R 13), (2, R 2 - 80#64), {rest([1, 8, 10, 12, 13])}]'),
        (0x800252b8, 'enter', [1, 9, 10, 22, 23], f'[{rest([1, 9, 10, 22, 23])}]'),
        (0x800252bc, 'call', [1, 9, 10, 22, 23], f'[(10, R 22), (11, R 23), (12, R 9), {rest([1, 9, 22, 23])}]'),
        (0x800252cc, 'leave', [1, 10], f'[(8, BitVec.signExtend 64 (Sail.BitVec.extractLsb (R 10) 31 0)), {rest([1, 10])}]'),
        (0x800252d4, 'check', [1, 8, 10, 19], f'[{rest([1, 8, 10, 19])}]'),
        (0x80025308, 'epi', [2, 8],
         f'[(2, R 2 + 80#64), (23, {ld(8)}), (22, {ld(7)}), (21, {ld(6)}), (20, {ld(5)}), (19, {ld(4)}), (18, {ld(3)}), (9, {ld(2)}), (8, {ld(1)}), (10, R 8), (1, {ld(0)})]')]),
      ('caml_enter_blocking_section_no_pending', 'Caml_enter_blocking_section_no_pending', 'EnterBlocking', None, (), [
        (0x8000d4ac, 'hook', [1, 10], f'[(15, {ld(0)}), {rest([1, 10])}]')]),
      ('write', 'Write', 'Write', None, (), [
        (0x80042628, 'tail', [1, 10, 11, 12], f'[(11, R 10), (12, R 11), (13, R 12), (10, {ld(0)}), (14, R 10), (1, R 1)]')]),
      ('_write_r', '_write_r', 'WriteR', {0x800424e4: 'F'}, (), [
        (0x800424b4, 'enter', [1, 2, 8, 10, 11, 12, 13],
         f'[(15, 0x800654d4#64), (10, R 11), (12, R 13), (8, R 10), (11, R 12), (2, R 2 - 16#64), {rest([1, 13])}]'),
        (0x800424e0, 'check', [1, 2, 8, 10], f'[(15, 18446744073709551615#64), {rest([1, 2, 8, 10])}]'),
        (0x800424e8, 'ret', [2, 10], f'[(2, R 2 + 16#64), (8, {ld(1)}), (1, {ld(0)}), (10, R 10)]')]),
      ('caml_leave_blocking_section', 'Caml_leave_blocking_section', 'LeaveBlocking',
       {0x8000d500: 'T', 0x8000d4ec: 'TF'}, ('slot', 'last'), [
        (0x8000d4b8, 'enter', [1, 2, 8, 10], f'[(2, R 2 - 16#64), {rest([1, 8, 10])}]'),
        (0x8000d4c8, 'hook', [1, 2, 10], f'[(8, {ld(1, "lw")}), (15, {ld(0)}), {rest([1, 2, 10])}]'),
        (0x8000d4d8, 'scan', [1, 2, 8, 10], f'[(12, 32#64), (13, 0x80068690#64), (15, 0#64), {rest([1, 2, 8, 10])}]'),
        (0x8000d4ec, 'more', [1, 2, 8, 10, 12, 13, 15], f'[{rest([1, 2, 8, 10, 12, 13, 15])}]'),
        (0x8000d4ec, 'last', [1, 2, 8, 10, 12, 13, 15], f'[{rest([1, 2, 8, 10, 12, 13, 15])}]'),
        (0x8000d4f0, 'slot', [1, 2, 8, 10, 12, 13, 15], f'[(15, BitVec.signExtend 64 (BitVec.extractLsb 31 0 (R 15 + 1#64))), (14, {ld(0)}), {rest([1, 2, 8, 10, 12, 13])}]'),
        (0x8000d528, 'errno', [1, 2, 8, 10], f'[{rest([1, 2, 8, 10])}]'),
        (0x8000d52c, 'ret', [2, 8, 10], f'[(2, R 2 + 16#64), (8, {ld(1)}), (1, {ld(0)}), (10, R 10)]')]),
      ('__errno', '__errno', 'Errno', None, (), [
        (0x80042518, 'leaf', [1], f'[(10, {ld(0)}), (1, R 1)]')]),
      ('caml_enter_blocking_section_default', 'Caml_enter_blocking_section_default', 'EnterDefault', None, (), [
        (0x8000d2a4, 'leaf', [1, 10], f'[{rest([1, 10])}]')]),
      ('caml_leave_blocking_section_default', 'Caml_leave_blocking_section_default', 'LeaveDefault', None, (), [
        (0x8000d2a8, 'leaf', [1, 10], f'[{rest([1, 10])}]')]),
    ]
