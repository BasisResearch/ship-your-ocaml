"""Generated block certificates of `caml_named_value` and
`caml_register_named_value` (`runtime/callback.c`) on this ELF: the prologue
and empty-name test, the `hash_value_name` byte loop, the `% Named_value_size`
call (`__umoddi3`), the bucket head load, the chain walk with its `strcmp`
call and the return; for the registration also the in-place update call, the
new node's `strlen`/`caml_stat_alloc`/`memcpy` calls and its link."""
from ocaml_argv_tuple import emit_tuple_blocks

FLAG = '--ocaml-named'

# `&named_value_table[h]` as the block's address arithmetic leaves it (auipc + addi)
BUCKET_ADDR = ('2147620184#64 + BitVec.signExtend 64 (BitVec.extractLsb\' 12 20 309143#32 +++ 0#12) + '
               '18446744073709550232#64 + R 10 <<< 32 >>> 29')
# the registration's `&named_value_table[h]` (s3 + (s2 << 3))
REG_BUCKET_ADDR = ('2147619900#64 + BitVec.signExtend 64 (BitVec.extractLsb\' 12 20 309655#32 +++ 0#12) + '
                   '18446744073709550516#64 + (R 10 <<< 32 >>> 32 <<< 3)')


def functions_spec(ld, rest):
    """(function, stem, namespace, route, [(start, name, keys, regs, taken, fast)])."""
    low = lambda x: f'BitVec.extractLsb 31 0 ({x})'
    sx = lambda x: f'BitVec.signExtend 64 ({x})'
    # h * 5 * 4 (slliw, addw, slliw), then (h * 20 - h) + byte (subw, addw)
    h5 = sx(f'{low(sx(f"{low('R 10')} <<< 2"))} + {low("R 10")}')
    h20 = sx(f'{low(h5)} <<< 2')
    step = sx(f'{low("R 14")} + {low(sx(f"{low(h20)} + -{low('R 10')}"))}')
    hash_regs = f'[(14, {ld(0, "lbu")}), (10, {step}), (13, R 13 + 1#64), (15, {h20})]'
    frame = lambda k: f'R 2 - 64#64 + {k}#64'
    pro_regs = (f'[(20, R 11), (9, R 10), (14, {ld(0, "lbu")}), (2, R 2 + 18446744073709551552#64), '
                f'{rest([1, 8, 10, 11, 18, 19])}]')
    saves = [(40, 9), (16, 20), (56, 1), (48, 8), (32, 18), (24, 19)]
    pro_fast = {'mem': [(frame(k), 'window') for k, _ in saves] + [('R 10', 'window')],
                'log': '[' + ', '.join(f'(({frame(k)}).toNat, 8, R {r})' for k, r in saves) + ']'}
    s2 = 'R 10 <<< 32 >>> 32'
    bucket_regs = f'[(8, {ld(0)}), (15, 2147926000#64 + ({s2} <<< 3)), (19, 2147926000#64), (18, {s2}), (10, R 10)]'
    return [
      # `__umoddi3(n, d)`: `__udivdi3` leaves the remainder in a1; t0 keeps ra.
      ('__umoddi3', '__umoddi3', 'Umoddi3', {}, [
        (0x800372e8, 'save', [1, 10, 11], f'[(5, R 1), {rest([1, 10, 11])}]', False, {}),
        (0x800372f0, 'back', [5, 11], f'[(10, R 11), {rest([5, 11])}]', False, None),
      ]),
      ('caml_named_value', 'Caml_named_value', 'NamedValue',
       {0x80021514: 'TF', 0x8002153c: 'TF', 0x80021568: 'TF', 0x80021574: 'TF', 0x80021584: 'TF'}, [
        # prologue: frame, saved s1/ra/s0, the name's first byte
        (0x800214fc, 'pro', [1, 2, 8, 9, 10],
         f'[(9, R 10), (14, {ld(0, "lbu")}), (2, R 2 + 18446744073709551584#64), {rest([1, 8, 10])}]', False,
         {'mem': [('R 2 - 32#64 + 8#64', 'window'), ('R 2 - 32#64 + 24#64', 'window'),
                  ('R 2 - 32#64 + 16#64', 'window'), ('R 10', 'window')],
          'log': '[((R 2 - 32#64 + 8#64).toNat, 8, R 9), ((R 2 - 32#64 + 24#64).toNat, 8, R 1), '
                 '((R 2 - 32#64 + 16#64).toNat, 8, R 8)]'}),
        (0x800214fc, 'proEmpty', [1, 2, 8, 9, 10],
         f'[(9, R 10), (14, {ld(0, "lbu")}), (2, R 2 + 18446744073709551584#64), {rest([1, 8, 10])}]', True,
         {'mem': [('R 2 - 32#64 + 8#64', 'window'), ('R 2 - 32#64 + 24#64', 'window'),
                  ('R 2 - 32#64 + 16#64', 'window'), ('R 10', 'window')],
          'log': '[((R 2 - 32#64 + 8#64).toNat, 8, R 9), ((R 2 - 32#64 + 24#64).toNat, 8, R 1), '
                 '((R 2 - 32#64 + 16#64).toNat, 8, R 8)]'}),
        # the hash loop's entry: cursor and h = 0
        (0x80021518, 'start', [10], '[(10, 0#64), (13, R 10)]', False, {}),
        # one hash step: h = h * 19 + byte (32-bit), next byte
        (0x80021520, 'hashMore', [10, 13, 14], hash_regs, True, {'mem': [('R 13 + 1#64', 'window')]}),
        (0x80021520, 'hashEnd', [10, 13, 14], hash_regs, False, {'mem': [('R 13 + 1#64', 'window')]}),
        # h % 13 by __umoddi3
        (0x80021540, 'mod', [1, 10], '[(11, 13#64), (10, R 10 <<< 32 >>> 32), (1, R 1)]', False, {}),
        (0x800215a0, 'empty', [10], '[(10, 0#64)]', False, {}),
        # the bucket head
        (0x80021550, 'bucketHit', [10], f'[(8, {ld(0)}), (15, 2147926000#64 + R 10 <<< 32 >>> 29), (10, R 10 <<< 32 >>> 29)]', True,
         {'mem': [(BUCKET_ADDR, 'window')], 'addrSimpOnly': True}),
        (0x80021550, 'bucketEmpty', [10], f'[(8, {ld(0)}), (15, 2147926000#64 + R 10 <<< 32 >>> 29), (10, R 10 <<< 32 >>> 29)]', False,
         {'mem': [(BUCKET_ADDR, 'window')], 'addrSimpOnly': True}),
        (0x8002156c, 'none', [10], f'[{rest([10])}]', False, {}),
        # the chain walk
        (0x80021570, 'nextEnd', [8, 10], f'[(8, {ld(0)}), {rest([10])}]', True, {'mem': [('R 8 + 8#64', 'window')]}),
        (0x80021570, 'nextMore', [8, 10], f'[(8, {ld(0)}), {rest([10])}]', False, {'mem': [('R 8 + 8#64', 'window')]}),
        (0x80021578, 'cmp', [1, 8, 9, 10], f'[(10, R 9), (11, R 8 + 16#64), {rest([1, 8, 9])}]', False, {}),
        (0x80021584, 'differ', [10], f'[{rest([10])}]', True, {}),
        (0x80021584, 'match', [10], f'[{rest([10])}]', False, {}),
        # the return: restore ra/s0/s1, return the node (or NULL)
        (0x80021588, 'done', [2, 8, 10],
         f'[(2, R 2 + 32#64), (9, {ld(2)}), (8, {ld(1)}), (10, R 8), (1, {ld(0)})]', False,
         {'mem': [('R 2 + 24#64', 'window'), ('R 2 + 16#64', 'window'), ('R 2 + 8#64', 'window')], 'ra': 0}),
      ]),
      ('caml_register_named_value', 'Caml_register_named_value', 'NamedRegister',
       {0x800213f8: 'TF', 0x80021420: 'TF', 0x80021450: 'TF', 0x8002145c: 'TF', 0x8002146c: 'TF'}, [
        # prologue: 64-byte frame, saved s1/s4/ra/s0/s2/s3, the name's first byte
        (0x800213d0, 'pro', [1, 2, 8, 9, 10, 11, 18, 19, 20], pro_regs, False, pro_fast),
        (0x800213d0, 'proEmpty', [1, 2, 8, 9, 10, 11, 18, 19, 20], pro_regs, True, pro_fast),
        (0x800213fc, 'start', [10], '[(10, 0#64), (13, R 10)]', False, {}),
        (0x80021404, 'hashMore', [10, 13, 14], hash_regs, True, {'mem': [('R 13 + 1#64', 'window')]}),
        (0x80021404, 'hashEnd', [10, 13, 14], hash_regs, False, {'mem': [('R 13 + 1#64', 'window')]}),
        (0x80021424, 'mod', [1, 10], '[(11, 13#64), (10, R 10 <<< 32 >>> 32), (1, R 1)]', False, {}),
        (0x800214f4, 'empty', [10], '[(10, 0#64)]', False, {}),
        # the bucket head; s2 keeps the bucket, s3 the table
        (0x80021434, 'bucketHit', [10], bucket_regs, True, {'mem': [(REG_BUCKET_ADDR, 'window')], 'addrSimpOnly': True}),
        (0x80021434, 'bucketEmpty', [10], bucket_regs, False, {'mem': [(REG_BUCKET_ADDR, 'window')], 'addrSimpOnly': True}),
        (0x80021454, 'none', [10], f'[{rest([10])}]', False, {}),
        # the chain walk
        (0x80021458, 'nextEnd', [8, 10], f'[(8, {ld(0)}), {rest([10])}]', True, {'mem': [('R 8 + 8#64', 'window')]}),
        (0x80021458, 'nextMore', [8, 10], f'[(8, {ld(0)}), {rest([10])}]', False, {'mem': [('R 8 + 8#64', 'window')]}),
        (0x80021460, 'cmp', [1, 8, 9, 10], f'[(10, R 9), (11, R 8 + 16#64), {rest([1, 8, 9])}]', False, {}),
        (0x8002146c, 'differ', [10], f'[{rest([10])}]', True, {}),
        (0x8002146c, 'match', [10], f'[{rest([10])}]', False, {}),
        # a registered name: caml_modify_generational_global_root(node, v)
        (0x80021470, 'found', [1, 8, 10, 20], f'[(10, R 8), (11, R 20), {rest([1, 8, 20])}]', False, {}),
        (0x8002147c, 'foundJoin', [10], f'[{rest([10])}]', False, {}),
        # a new name: strlen, caml_stat_alloc(len + 24), memcpy(node + 16, name, len + 1)
        (0x80021480, 'miss', [1, 9, 10], f'[(10, R 9), {rest([1, 9])}]', False, {}),
        (0x80021488, 'alloc', [1, 2, 10], f'[(10, R 10 + 24#64), (12, R 10), {rest([1, 2])}]', False,
         {'mem': [('R 2 + 8#64', 'window')], 'log': '[((R 2 + 8#64).toNat, 8, R 10)]'}),
        (0x80021498, 'copy', [1, 2, 9, 10, 18],
         f'[(18, R 18 <<< 3), (10, R 10 + 16#64), (12, {ld(0)} + 1#64), (11, R 9), (8, R 10), {rest([1, 2, 9])}]', False,
         {'mem': [('R 2 + 8#64', 'window')]}),
        # the link: node->val, node->next = bucket head, bucket = node; then the root
        (0x800214b4, 'link', [1, 8, 18, 19, 20],
         f'[(10, R 8), (15, {ld(0)}), (19, R 19 + R 18), {rest([1, 8, 18, 20])}]', False,
         {'mem': [('R 19 + R 18', 'window'), ('R 8', 'window'), ('R 8 + 8#64', 'window'), ('R 19 + R 18', 'window')],
          'log': f'[((R 8).toNat, 8, R 20), ((R 8 + 8#64).toNat, 8, {ld(0)}), ((R 19 + R 18).toNat, 8, R 8)]'}),
        # the return: restore ra/s0-s4, return Val_unit
        (0x800214d0, 'done', [2],
         f'[(2, R 2 + 64#64), (10, 1#64), (20, {ld(5)}), (19, {ld(4)}), (18, {ld(3)}), (9, {ld(2)}), (8, {ld(1)}), (1, {ld(0)})]', False,
         {'mem': [(f'R 2 + {k}#64', 'window') for k in (56, 48, 40, 32, 24, 16)], 'ra': 0}),
      ]),
    ]


def emit_named(root, functions, decode, code, text_base, lib, build_cfg, literal):
    ld = lambda n, k='ld': f'bytesVal .{k} (loads.getD {n} [])'
    rest = lambda ks: ', '.join(f'({k}, R {k})' for k in ks)
    result = {}
    args = (root, functions, decode, code, text_base, lib, build_cfg, literal)
    for fn, stem, ns, route, fblocks in functions_spec(ld, rest):
        sel = [(blk[1], blk[2], blk[3], blk[4]) + ((blk[5],) if blk[5] is not None else ()) for blk in fblocks]
        result.update(emit_tuple_blocks(*args, fn, stem, f'OCaml.Vm.Primitives.Named.{ns}',
            f'OCaml/Vm/Primitives/Named/{ns}.lean', sel, starts=[blk[0] for blk in fblocks],
            chunked=(), flag=FLAG, route=route, render_code=fn != '__umoddi3'))
    return result
