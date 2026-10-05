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
    return emit_tuple_blocks(root, functions, decode, code, text_base, lib, build_cfg, literal,
        '_write', '_write', 'OCaml.Vm.Primitives.ConsoleWrite', 'OCaml/Vm/Primitives/ConsoleWrite.lean',
        selected, starts=[a for a, _, _, _ in blocks], chunked=(), flag=FLAG, route=ROUTE)
