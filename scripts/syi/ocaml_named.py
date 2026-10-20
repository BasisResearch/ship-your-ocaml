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
      # `caml_register_generational_global_root(r)` (`runtime/globroots.c`): a
      # block value is filed in `caml_global_roots_young` (Is_young) or, when the
      # page table says In_heap, `caml_global_roots_old`
      ('caml_register_generational_global_root', 'Caml_register_generational_global_root', 'RegisterRoot',
       {0x8000ca10: 'TF', 0x8000ca20: 'TF', 0x8000ca28: 'TF', 0x8000ca40: 'TF'}, [
        # the root's value; an immediate returns at once
        (0x8000ca04, 'imm', [10], f'[(15, {ld(0)} &&& 1#64), (10, {ld(0)}), (11, R 10)]', True,
         {'mem': [('R 10', 'window')]}),
        (0x8000ca04, 'isBlock', [10], f'[(15, {ld(0)} &&& 1#64), (10, {ld(0)}), (11, R 10)]', False,
         {'mem': [('R 10', 'window')]}),
        # `Caml_state`, then Is_young: below `young_end`, above `young_start`
        (0x8000ca14, 'state', [10, 11], f'[(15, {ld(0)}), {rest([10, 11])}]', False,
         {'mem': [('0x80064d08#64', 'global')]}),
        (0x8000ca1c, 'aboveEnd', [10, 11, 15], f'[(14, {ld(0)}), {rest([10, 11, 15])}]', True,
         {'mem': [('R 15 + 40#64', 'window')]}),
        (0x8000ca1c, 'belowEnd', [10, 11, 15], f'[(14, {ld(0)}), {rest([10, 11, 15])}]', False,
         {'mem': [('R 15 + 40#64', 'window')]}),
        (0x8000ca24, 'young', [10, 11, 15], f'[(15, {ld(0)}), {rest([10, 11])}]', True,
         {'mem': [('R 15 + 32#64', 'window')]}),
        (0x8000ca24, 'notYoung', [10, 11, 15], f'[(15, {ld(0)}), {rest([10, 11])}]', False,
         {'mem': [('R 15 + 32#64', 'window')]}),
        # In_heap by `caml_page_table_lookup(v)`, ra and r saved in a 32-byte frame
        (0x8000ca2c, 'lookup', [1, 2, 10, 11], f'[(2, R 2 + 18446744073709551584#64), {rest([1, 10, 11])}]', False,
         {'mem': [('R 2 - 32#64 + 24#64', 'window'), ('R 2 - 32#64 + 8#64', 'window')],
          'log': '[((R 2 - 32#64 + 24#64).toNat, 8, R 1), ((R 2 - 32#64 + 8#64).toNat, 8, R 11)]'}),
        (0x8000ca3c, 'inHeap', [10], '[(10, R 10 &&& 1#64)]', False, {}),
        (0x8000ca3c, 'notHeap', [10], '[(10, R 10 &&& 1#64)]', True, {}),
        # the tail calls `caml_skiplist_insert(list, r, 0)`
        (0x8000ca44, 'old', [2], f'[(2, R 2 + 32#64), (10, 2147911024#64), (12, 0#64), (1, {ld(1)}), (11, {ld(0)})]', False,
         {'mem': [('R 2 + 8#64', 'window'), ('R 2 + 24#64', 'window')]}),
        (0x8000ca60, 'toYoung', [], '[(10, 2147911168#64), (12, 0#64)]', False, {}),
        # the returns
        (0x8000ca70, 'heapless', [2, 10], f'[(2, R 2 + 32#64), (1, {ld(0)}), {rest([10])}]', False,
         {'mem': [('R 2 + 24#64', 'window')], 'ra': 0}),
        (0x8000ca7c, 'immRet', [1, 10], f'[{rest([1, 10])}]', False, {}),
      ], (0x8000ca1c,)),
      # `caml_modify_generational_global_root(r, v)`: by the classes of `v` and
      # the old `*r` (immediate, young, In_heap, other), remove `r` from the
      # lists it leaves, insert it in the one it joins, then `*r = v`
      ('caml_modify_generational_global_root', 'Caml_modify_generational_global_root', 'ModifyRoot',
       {a: 'TF' for a in (0x8000cb24, 0x8000cb34, 0x8000cb3c, 0x8000cb4c, 0x8000cb58, 0x8000cb68, 0x8000cb70,
                          0x8000cb7c, 0x8000cba0, 0x8000cba4, 0x8000cba8, 0x8000cbb4, 0x8000cbe8, 0x8000cbf8,
                          0x8000cc00, 0x8000cc0c)},
       mod_blocks(ld, rest), (0x8000cb30, 0x8000cb64, 0x8000cbf4)),
    ]


def mod_blocks(ld, rest):
    """The blocks of `caml_modify_generational_global_root`."""
    frame = lambda k: f'R 2 - 32#64 + {k}#64'
    state = lambda keys: (f'[(15, {ld(0)}), {rest(keys)}]', {'mem': [('0x80064d08#64', 'global')]})
    above = lambda reg, keys: (f'[({reg}, {ld(0)}), {rest(keys)}]', {'mem': [('R 15 + 40#64', 'window')]})
    start = lambda keys: (f'[(15, {ld(0)}), {rest(keys)}]', {'mem': [('R 15 + 32#64', 'window')]})
    heap = (f'[(10, R 10 &&& 1#64), {rest([8, 9])}]', {})
    old = lambda src, bit: (f'[({bit}, {ld(0)} &&& 1#64), (10, {ld(0)}), {rest([8, 9] + ([13, 15] if bit == 14 else []))}]',
                            {'mem': [(src, 'window')]})
    store = (f'[(2, R 2 + 32#64), (9, {ld(2)}), (8, {ld(1)}), (1, {ld(0)}), {rest([10])}]',
             {'mem': [('R 9', 'window'), ('R 2 + 24#64', 'window'), ('R 2 + 16#64', 'window'), ('R 2 + 8#64', 'window')],
              'log': '[((R 9).toNat, 8, R 8)]', 'ra': 0})
    lookup = (f'[{rest([1, 8, 9, 10])}]', {})
    OLD, YOUNG = '2147911024#64', '2147911168#64'
    two = lambda a, n1, n2, keys, spec: [(a, n1, keys, spec[0], True, spec[1]), (a, n2, keys, spec[0], False, spec[1])]
    blocks = []
    blocks += two(0x8000cb08, 'newImm', 'newBlock', [1, 2, 8, 9, 10, 11],
                  (f'[(9, R 10), (8, R 11), (15, R 11 &&& 1#64), (2, R 2 + 18446744073709551584#64), {rest([1, 10, 11])}]',
                   {'mem': [(frame(16), 'window'), (frame(8), 'window'), (frame(24), 'window')],
                    'log': f'[(({frame(16)}).toNat, 8, R 8), (({frame(8)}).toNat, 8, R 9), (({frame(24)}).toNat, 8, R 1)]'}))
    blocks += [(0x8000cb28, 'newState', [8, 9, 10, 11]) + state([8, 9, 10, 11]) [:0] + (state([8, 9, 10, 11])[0], False, state([8, 9, 10, 11])[1])]
    blocks += two(0x8000cb30, 'newAboveEnd', 'newBelowEnd', [8, 9, 10, 11, 15], above(13, [8, 9, 10, 11, 15]))
    blocks += two(0x8000cb38, 'newYoung', 'newNotYoung', [8, 9, 10, 11, 13, 15], start([8, 9, 10, 11, 13]))
    blocks += [(0x8000cb40, 'newLookup', [1, 8, 9, 10], f'[(10, R 8), {rest([1, 8, 9])}]', False, {})]
    blocks += two(0x8000cb48, 'newNotHeap', 'newHeap', [8, 9, 10], heap)
    blocks += two(0x8000cb50, 'oldImm', 'oldBlock', [8, 9, 10], old('R 9', 15))
    blocks += [(0x8000cb5c, 'oldState', [8, 9, 10], state([8, 9, 10])[0], False, state([8, 9, 10])[1])]
    blocks += two(0x8000cb64, 'oldAboveEnd', 'oldBelowEnd', [8, 9, 10, 15], above(14, [8, 9, 10, 15]))
    blocks += two(0x8000cb6c, 'oldYoung', 'oldNotYoung', [8, 9, 10, 15], start([8, 9, 10]))
    blocks += [(0x8000cb74, 'oldLookup', [1, 8, 9, 10]) + lookup[:1] + (False, lookup[1])]
    blocks += two(0x8000cb78, 'oldNotHeap', 'oldHeap', [8, 9, 10], heap)
    blocks += [(0x8000cb80, 'store', [2, 8, 9, 10], store[0], False, store[1])]
    # a young `v`
    blocks += two(0x8000cb98, 'yImm', 'yBlock', [8, 9, 10, 13, 15], old('R 10', 14))
    blocks += two(0x8000cba4, 'yAboveEnd', 'yBelowEnd', [8, 9, 10, 13, 15], (f'[{rest([8, 9, 10, 13, 15])}]', {}))
    blocks += two(0x8000cba8, 'yYoung', 'yNotYoung', [8, 9, 10, 15], (f'[{rest([8, 9, 10, 15])}]', {}))
    blocks += [(0x8000cbac, 'yLookup', [1, 8, 9, 10]) + lookup[:1] + (False, lookup[1])]
    blocks += two(0x8000cbb0, 'yNotHeap', 'yHeap', [8, 9, 10], heap)
    blocks += [(0x8000cbb8, 'yRemove', [1, 8, 9], f'[(10, {OLD}), (11, R 9), {rest([1, 8, 9])}]', False, {})]
    blocks += [(0x8000cbc8, 'yInsert', [1, 8, 9], f'[(10, {YOUNG}), (11, R 9), (12, 0#64), {rest([1, 8, 9])}]', False, {})]
    blocks += [(0x8000cbdc, 'yJoin', [10], f'[{rest([10])}]', False, {})]
    # an immediate or unboxed `v`
    blocks += two(0x8000cbe0, 'xImm', 'xBlock', [8, 9, 10], old('R 9', 15))
    blocks += [(0x8000cbec, 'xState', [8, 9, 10], state([8, 9, 10])[0], False, state([8, 9, 10])[1])]
    blocks += two(0x8000cbf4, 'xAboveEnd', 'xBelowEnd', [8, 9, 10, 15], above(14, [8, 9, 10, 15]))
    blocks += two(0x8000cbfc, 'xYoung', 'xNotYoung', [8, 9, 10, 15], start([8, 9, 10]))
    blocks += [(0x8000cc04, 'xLookup', [1, 8, 9, 10]) + lookup[:1] + (False, lookup[1])]
    blocks += two(0x8000cc08, 'xNotHeap', 'xHeap', [8, 9, 10], heap)
    blocks += [(0x8000cc10, 'xRemoveOld', [1, 8, 9], f'[(10, {OLD}), (11, R 9), {rest([1, 8, 9])}]', False, {})]
    blocks += [(0x8000cc20, 'xRemoveYoung', [1, 8, 9], f'[(10, {YOUNG}), (11, R 9), {rest([1, 8, 9])}]', False, {})]
    blocks += [(0x8000cc30, 'xStore', [2, 8, 9, 10], store[0], False, store[1])]
    # an old `v` over an immediate or unboxed `*r`
    blocks += [(0x8000cc48, 'oInsert', [1, 8, 9], f'[(10, {OLD}), (12, 0#64), (11, R 9), {rest([1, 8, 9])}]', False, {})]
    blocks += [(0x8000cc5c, 'oStore', [2, 8, 9, 10], store[0], False, store[1])]
    return blocks


def emit_named(root, functions, decode, code, text_base, lib, build_cfg, literal):
    ld = lambda n, k='ld': f'bytesVal .{k} (loads.getD {n} [])'
    rest = lambda ks: ', '.join(f'({k}, R {k})' for k in ks)
    result = {}
    args = (root, functions, decode, code, text_base, lib, build_cfg, literal)
    for spec in functions_spec(ld, rest):
        fn, stem, ns, route, fblocks = spec[:5]
        splits = spec[5] if len(spec) > 5 else ()
        sel = [(blk[1], blk[2], blk[3], blk[4]) + ((blk[5],) if blk[5] is not None else ()) for blk in fblocks]
        result.update(emit_tuple_blocks(*args, fn, stem, f'OCaml.Vm.Primitives.Named.{ns}',
            f'OCaml/Vm/Primitives/Named/{ns}.lean', sel, starts=[blk[0] for blk in fblocks],
            chunked=(), flag=FLAG, route=route, render_code=fn != '__umoddi3', splits=splits))
    return result
