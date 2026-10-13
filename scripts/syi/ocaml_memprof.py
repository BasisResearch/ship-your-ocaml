"""Generated block certificates of the memprof suspension on the uncaught
path (`caml_fatal_uncaught_exception` calls `caml_memprof_set_suspended(1)`):
`caml_memprof_set_suspended`, `caml_memprof_renew_minor_sample` on the
sampling-off path (`lambda == 0.0`), `__eqdf2` on two zeros, and
`caml_update_young_limit`."""
from ocaml_argv_tuple import emit_tuple_blocks

FLAG = '--ocaml-memprof'
PROBE = None


def functions_spec(ld, rest):
    """(function, stem, namespace, route, render, [(start, name, keys, regs, taken, fast)])."""
    P = PROBE
    fast = lambda f: None if P else f
    reg = lambda r: P or r
    L = lambda n, k='ld': ld(n, k)
    return [
      # caml_memprof_set_suspended(s): local->suspended = s; renew; s != 0 returns
      ('caml_memprof_set_suspended', 'Caml_memprof_set_suspended', 'SetSuspended',
       {0x80029600: 'F', 0x8002961c: 'TF', 0x80029630: 'TF', 0x80029638: 'TF'}, True, [
        (0x800295d8, 'suspend', [1, 2, 8, 10],
         reg(f'[(15, {L(0)}), (8, 2147895512#64), (2, R 2 + 18446744073709551584#64), (1, R 1), (10, R 10)]'), False,
         fast({'mem': [('R 2 - 32#64 + 16#64', 'window'), ('R 2 - 32#64 + 24#64', 'window'),
                       ('2147895512#64', 'global'), ('R 2 - 32#64 + 8#64', 'window'), ('@0', 'window')],
               'log': f'[((R 2 - 32#64 + 16#64).toNat, 8, R 8), ((R 2 - 32#64 + 24#64).toNat, 8, R 1), '
                      f'((R 2 - 32#64 + 8#64).toNat, 8, R 10), (({L(0)}).toNat, 4, R 10)]'})),
        (0x800295fc, 'resumed', [2, 10], reg(f'[(10, {L(0)}), (2, R 2)]'), False,
         fast({'mem': [('R 2 + 8#64', 'window')]})),
        (0x80029604, 'leave', [2, 10], reg(f'[(2, R 2 + 32#64), (8, {L(1)}), (1, {L(0)}), (10, R 10)]'), False,
         fast({'mem': [('R 2 + 24#64', 'window'), ('R 2 + 16#64', 'window')], 'ra': 0})),
      ]),
      # caml_memprof_renew_minor_sample() with lambda == 0.0
      ('caml_memprof_renew_minor_sample', 'Caml_memprof_renew_minor_sample', 'RenewMinorSample',
       {0x80029570: 'T', 0x80029580: 'TF', 0x800295c0: 'TF'}, True, [
        (0x80029558, 'compare', [1, 2, 10],
         reg(f'[(2, R 2 + 18446744073709551600#64), (10, {L(0)}), (11, 0#64), (1, R 1)]'), False,
         fast({'mem': [('2147896560#64', 'global'), ('R 2 - 16#64 + 8#64', 'window')],
               'log': '[((R 2 - 16#64 + 8#64).toNat, 8, R 1)]'})),
        (0x80029570, 'off', [10], reg('[(10, R 10)]'), True, fast({})),
        (0x80029584, 'trigger', [1, 2, 10], reg(f'[(15, {L(1)}), (1, R 1), (2, R 2), (10, R 10)]'), False,
         fast({'mem': [('2147896584#64', 'global'), ('@0 + 48#64', 'window')]})),
        (0x80029590, 'store', [2, 10, 15], reg(f'[(2, R 2 + 16#64), (14, 2147894676#64), (1, {L(0)}), (10, R 10), (15, R 15)]'), False,
         fast({'mem': [('R 2 + 8#64', 'window'), ('2147896520#64', 'global')],
               'log': "[((2147653012#64 + BitVec.signExtend 64 (BitVec.extractLsb' 12 20 243479#32 +++ 0#12) + 1844#64).toNat, 8, R 15)]",
               'logFacts': ['imm20Of']})),
      ]),
      # __eqdf2(a, b) on two zeros: neither is a NaN, exponents, mantissas, signs equal
      ('__eqdf2', '__eqdf2', 'Eqdf2', {0x8003476c: 'T', 0x80034774: 'TF', 0x80034780: 'T', 0x80034788: 'TF',
                                      0x8003478c: 'F', 0x80034790: 'F', 0x80034798: 'T'}, True, [
        (0x80034740, 'unpack', [10, 11],
         reg('[(11, R 11 >>> 63), (15, 4503599627370495#64 &&& R 11), (14, R 10 >>> 63), '
             '(16, 4503599627370495#64 &&& R 10), (12, R 11 >>> 52 &&& 2047#64), '
             '(17, (R 10 >>> 52 &&& 2047#64) + 18446744073709549569#64), (13, R 10 >>> 52 &&& 2047#64), (10, R 10)]'),
         True, fast({})),
        (0x8003477c, 'rhs', [10, 12], reg('[(10, R 12 + 18446744073709549569#64), (12, R 12)]'), True, fast({})),
        (0x8003478c, 'exps', [10, 12, 13], reg('[(10, R 10), (12, R 12), (13, R 13)]'), False, fast({})),
        (0x80034790, 'mants', [10, 15, 16], reg('[(10, R 10), (15, R 15), (16, R 16)]'), False, fast({})),
        (0x80034794, 'signs', [11, 14], reg('[(10, 0#64), (11, R 11), (14, R 14)]'), True, fast({})),
        (0x80034778, 'ret', [1, 10], reg('[(1, R 1), (10, R 10)]'), False, fast({})),
      ]),
      # caml_update_young_limit(): young_limit = max(young_trigger, memprof trigger), or young_alloc_end if pending
      ('caml_update_young_limit', 'Caml_update_young_limit', 'UpdateYoungLimit',
       {0x8000d5a8: 'TF', 0x8000d5bc: 'TF'}, True, [
        (0x8000d590, 'triggerHigh', [10],
         reg(f'[(15, {L(2)}), (12, {L(1)}), (14, {L(0)}), (13, 2147896584#64), (10, R 10)]'), True,
         fast({'mem': [('2147896584#64', 'global'), ('2147896520#64', 'global'), ('@0 + 72#64', 'window')]})),
        (0x8000d590, 'triggerLow', [10],
         reg(f'[(15, {L(2)}), (12, {L(1)}), (14, {L(0)}), (13, 2147896584#64), (10, R 10)]'), False,
         fast({'mem': [('2147896584#64', 'global'), ('2147896520#64', 'global'), ('@0 + 72#64', 'window')]})),
        (0x8000d5ac, 'memprof', [10, 12], reg('[(15, R 12), (10, R 10), (12, R 12)]'), False, fast({})),
        (0x8000d5b0, 'idle', [10, 13, 14, 15], reg(f'[(12, {L(0, "lw")}), (10, R 10), (13, R 13), (14, R 14), (15, R 15)]'),
         True, fast({'mem': [('2147896112#64', 'global'), ('R 14', 'window')],
                     'log': '[((R 14).toNat, 8, R 15)]'})),
        (0x8000d5b0, 'pending', [10, 13, 14, 15], reg(f'[(12, {L(0, "lw")}), (10, R 10), (13, R 13), (14, R 14), (15, R 15)]'),
         False, fast({'mem': [('2147896112#64', 'global'), ('R 14', 'window')],
                      'log': '[((R 14).toNat, 8, R 15)]'})),
        (0x8000d5c0, 'urgent', [10, 13], reg(f'[(14, {L(1)}), (15, {L(0)}), (10, R 10), (13, R 13)]'), False,
         fast({'mem': [('R 13', 'window'), ('@0 + 56#64', 'window'), ('@0', 'window')],
               'log': f'[(({L(0)}).toNat, 8, {L(1)})]'})),
        (0x8000d5cc, 'done', [1, 10], reg('[(1, R 1), (10, R 10)]'), False, fast({})),
      ]),
    ]


def emit_memprof(root, functions, decode, code, text_base, lib, build_cfg, literal):
    ld = lambda n, k='ld': f'bytesVal .{k} (loads.getD {n} [])'
    rest = lambda ks: ', '.join(f'({k}, R {k})' for k in ks)
    result = {}
    args = (root, functions, decode, code, text_base, lib, build_cfg, literal)
    for fn, stem, ns, route, render, fblocks in functions_spec(ld, rest):
        sel = [(b[1], b[2], b[3], b[4]) + ((b[5],) if b[5] is not None else ()) for b in fblocks]
        result.update(emit_tuple_blocks(*args, fn, stem, f'OCaml.Vm.Primitives.Memprof.{ns}',
            f'OCaml/Vm/Primitives/Memprof/{ns}.lean', sel, starts=[b[0] for b in fblocks],
            chunked=(), flag=FLAG, route=route, render_code=render))
    return result
