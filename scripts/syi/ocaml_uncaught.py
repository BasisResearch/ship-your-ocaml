"""Generated block certificates of the uncaught-exception path's C code:
`caml_format_exception` on a constant exception (the name only: the name's
length, its copy into the 256-byte buffer, the terminator, the
`caml_stat_alloc_noexc` result and the copy out)."""
from ocaml_argv_tuple import emit_tuple_blocks

FLAG = '--ocaml-uncaught'
PROBE = None


def functions_spec(ld, rest):
    """(function, stem, namespace, route, render, [(start, name, keys, regs, taken, fast)])."""
    P = PROBE
    L = lambda n, k='ld': ld(n, k)
    fast = lambda f: None if P else f
    reg = lambda r: P or r
    return [
      ('caml_format_exception', 'Caml_format_exception', 'FormatException',
       {0x8000dc20: 'T', 0x8000dda0: 'T', 0x8000de10: 'T', 0x8000dddc: 'F'}, True, [
        # prologue: the 432-byte frame, six saves, the buffer's ptr/end, the tag and Field(exn, 0)
        (0x8000dbec, 'pro', [1, 2, 8, 9, 10, 18, 20, 21],
         reg('[(21, bytesVal .ld (loads.getD 1 [])), (18, R 2 + 18446744073709551535#64), (20, R 2 + 18446744073709551280#64), '
             '(15, bytesVal .lbu (loads.getD 0 [])), (2, R 2 + 18446744073709551184#64), (1, R 1), (8, R 8), (9, R 9), (10, R 10)]'), True,
         fast({'mem': [('R 2 + 18446744073709551184#64 + 400#64', 'window'), ('R 2 + 18446744073709551184#64 + 384#64', 'window'), ('R 2 + 18446744073709551184#64 + 424#64', 'window'), ('R 2 + 18446744073709551184#64 + 416#64', 'window'), ('R 2 + 18446744073709551184#64 + 408#64', 'window'), ('R 2 + 18446744073709551184#64 + 376#64', 'window'),
                       ('R 10 + 18446744073709551608#64', 'window'), ('R 2 + 18446744073709551184#64 + 80#64', 'window'), ('R 2 + 18446744073709551184#64 + 88#64', 'window'), ('R 10', 'window')],
               'addrFacts': ['show BitVec.signExtend 64 400#12 = 400#64 by decide',
                             'show BitVec.signExtend 64 384#12 = 384#64 by decide',
                             'show BitVec.signExtend 64 424#12 = 424#64 by decide',
                             'show BitVec.signExtend 64 416#12 = 416#64 by decide',
                             'show BitVec.signExtend 64 408#12 = 408#64 by decide',
                             'show BitVec.signExtend 64 376#12 = 376#64 by decide',
                             'show BitVec.signExtend 64 80#12 = 80#64 by decide',
                             'show BitVec.signExtend 64 88#12 = 88#64 by decide',
                             'show BitVec.signExtend 64 4088#12 = 18446744073709551608#64 by decide',
                             'show BitVec.signExtend 64 0#12 = 0#64 by decide', 'BitVec.add_zero'],
               'log': '[((R 2 - 432#64 + 400#64).toNat, 8, R 18), ((R 2 - 432#64 + 384#64).toNat, 8, R 20), '
                      '((R 2 - 432#64 + 424#64).toNat, 8, R 1), ((R 2 - 432#64 + 416#64).toNat, 8, R 8), '
                      '((R 2 - 432#64 + 408#64).toNat, 8, R 9), ((R 2 - 432#64 + 376#64).toNat, 8, R 21), '
                      '((R 2 - 432#64 + 80#64).toNat, 8, R 2 - 432#64 + 96#64), '
                      '((R 2 - 432#64 + 88#64).toNat, 8, R 2 - 432#64 + 351#64)]', 'addrSimpOnly': True})),

        # strlen(name)
        (0x8000dd94, 'nameLen', [1, 10, 21], reg('[(10, R 21), (1, R 1), (21, R 21)]'), False, fast({})),
        # the name fits the buffer
        (0x8000dd9c, 'fits', [10, 18, 20], reg('[(8, R 20 + R 10), (10, R 10), (18, R 18), (20, R 20)]'), True, fast({})),
        (0x8000de10, 'nonempty', [10], reg('[(10, R 10)]'), True, fast({})),
        # memmove(buf.data, name, len)
        (0x8000ddac, 'copy', [1, 10, 20, 21],
         reg('[(10, R 20), (11, R 21), (12, R 10), (1, R 1), (20, R 20), (21, R 21)]'), False, fast({})),
        # buf.ptr = data + len
        (0x8000ddbc, 'record', [2, 8, 10], reg('[(2, R 2), (8, R 8), (10, R 10)]'), False,
         fast({'mem': [('R 2 + 80#64', 'window')], 'log': '[((R 2 + 80#64).toNat, 8, R 8)]'})),
        # *buf.ptr = 0; caml_stat_alloc_noexc(len + 1)
        (0x8000ddc0, 'terminate', [1, 2, 8, 10, 20], reg(f'[(10, {L(0)} + (-R 20 + 1#64)), (8, {L(0)} + (-R 20 + 1#64)), (1, R 1), (2, R 2), (20, R 20)]'), False,
         fast({'mem': [('R 8', 'window'), ('R 2 + 80#64', 'window')], 'log': '[((R 8).toNat, 1, 0#64)]'})),
        (0x8000ddd8, 'allocated', [10], reg('[(9, R 10), (10, R 10)]'), False, fast({})),
        # memmove(res, buf.data, len + 1)
        (0x8000dde0, 'copyOut', [1, 8, 10, 20],
         reg('[(11, R 20), (12, R 8), (1, R 1), (8, R 8), (10, R 10), (20, R 20)]'), False, fast({})),
        (0x8000ddec, 'leave', [2, 9],
         reg('[(2, R 2 + 432#64), (9, bytesVal .ld (loads.getD 5 [])), (10, R 9), (21, bytesVal .ld (loads.getD 4 [])), (20, bytesVal .ld (loads.getD 3 [])), (18, bytesVal .ld (loads.getD 2 [])), '
             '(8, bytesVal .ld (loads.getD 1 [])), (1, bytesVal .ld (loads.getD 0 []))]'), False,
         fast({'mem': [('R 2 + 424#64', 'window'), ('R 2 + 416#64', 'window'), ('R 2 + 400#64', 'window'),
                       ('R 2 + 384#64', 'window'), ('R 2 + 376#64', 'window'), ('R 2 + 408#64', 'window')], 'ra': 0})),
      ]),
      ('caml_fatal_uncaught_exception', 'Caml_fatal_uncaught_exception', 'FatalUncaught',
       {0x8000df84: 'T', 0x8000dff4: 'TF', 0x8000e03c: 'T', 0x8000dfac: 'F'}, True, [
        # prologue: the 48-byte frame, four saves; caml_named_value("Printexc.handle_uncaught_exception")
        (0x8000df50, 'pro', [1, 2, 8, 9, 10, 18, 19],
         reg('[(10, 2147837296#64), (9, R 10), (2, R 2 + 18446744073709551568#64), (1, R 1), (8, R 8), (18, R 18), (19, R 19)]'), False,
         fast({'mem': [(f'R 2 + 18446744073709551568#64 + {k}#64', 'window') for k in (24, 32, 40, 16, 8)],
               'addrFacts': [f'show BitVec.signExtend 64 {k}#12 = {k}#64 by decide' for k in (24, 32, 40, 16, 8)]
                            + ['show BitVec.signExtend 64 4048#12 = 18446744073709551568#64 by decide'],
               'log': '[((R 2 - 48#64 + 24#64).toNat, 8, R 9), ((R 2 - 48#64 + 32#64).toNat, 8, R 8), '
                      '((R 2 - 48#64 + 40#64).toNat, 8, R 1), ((R 2 - 48#64 + 16#64).toNat, 8, R 18), '
                      '((R 2 - 48#64 + 8#64).toNat, 8, R 19)]', 'addrSimpOnly': True})),
        # caml_memprof_set_suspended(1)
        (0x8000df78, 'suspend', [1, 10], reg('[(10, 1#64), (8, R 10), (1, R 1)]'), False, fast({})),
        # no handler registered
        (0x8000df84, 'absent', [8, 10], reg('[(8, R 8), (10, R 10)]'), True, fast({})),
        # caml_format_exception(exn)
        (0x8000dfc0, 'format', [1, 9], reg('[(10, R 9), (1, R 1), (9, R 9)]'), False, fast({})),
        # save and clear the backtrace fields; caml_named_value("Pervasives.do_at_exit")
        (0x8000dfc8, 'save', [1, 10],
         reg(f'[(19, {L(1, "lw")}), (9, {L(2, "lw")}), (14, {L(1, "lw")}), (10, 2147833712#64), (18, R 10), (15, {L(0)}), (8, 2147896584#64), (1, R 1)]'), False,
         fast({'mem': [('0x80064d08#64', 'global'), ('@0 + 232#64', 'window'), ('@0 + 232#64', 'window'), ('@0 + 240#64', 'window')],
               'log': '[((bytesVal .ld (loads.getD 0 []) + 232#64).toNat, 8, 0#64)]'})),
        (0x8000dff4, 'atExitNone', [10], reg('[(10, R 10)]'), True, fast({})),
        (0x8000dff4, 'atExitSome', [10], reg('[(10, R 10)]'), False, fast({})),
        # caml_callback_exn(*at_exit, Val_unit)
        (0x8000dff8, 'callback', [1, 10], reg(f'[(11, 1#64), (10, {L(0)}), (1, R 1)]'), False,
         fast({'mem': [('R 10', 'window')]})),
        # restore the backtrace fields; fprintf(stderr, "Fatal error: exception %s\n", msg)
        (0x8000e004, 'report', [1, 8, 9, 18, 19],
         reg(f'[(11, 2147837040#64), (10, {L(2)}), (12, R 18), (14, {L(1)}), (15, {L(0)}), (1, R 1), (8, R 8), (9, R 9), (18, R 18), (19, R 19)]'), False,
         fast({'mem': [('R 8', 'window'), ('0x800648f8#64', 'global'), ('@0 + 232#64', 'window'), ('@0 + 240#64', 'window'), ('@1 + 24#64', 'window')],
               'log': '[((bytesVal .ld (loads.getD 0 []) + 232#64).toNat, 8, R 19), ((bytesVal .ld (loads.getD 0 []) + 240#64).toNat, 8, R 9)]'})),
        # caml_stat_free(msg)
        (0x8000e02c, 'release', [1, 18], reg('[(10, R 18), (1, R 1), (18, R 18)]'), False, fast({})),
        # backtrace inactive
        (0x8000e034, 'trace', [8, 10], reg(f'[(15, {L(1)}), (8, R 8), (10, R 10)]'), True,
         fast({'mem': [('R 8', 'window'), ('@0 + 232#64', 'window')]})),
        # caml_abort_on_uncaught_exn unset
        (0x8000dfa4, 'abortOff', [10], reg(f'[(15, {L(0, "lw")}), (10, R 10)]'), False,
         fast({'mem': [('0x80064b34#64', 'global')]})),
        # exit(2)
        (0x8000dfb0, 'leave', [1], reg('[(10, 2#64), (1, R 1)]'), False, fast({})),
      ]),
    ]


def emit_uncaught(root, functions, decode, code, text_base, lib, build_cfg, literal):
    ld = lambda n, k='ld': f'bytesVal .{k} (loads.getD {n} [])'
    rest = lambda ks: ', '.join(f'({k}, R {k})' for k in ks)
    result = {}
    args = (root, functions, decode, code, text_base, lib, build_cfg, literal)
    for fn, stem, ns, route, render, fblocks in functions_spec(ld, rest):
        sel = [(b[1], b[2], b[3], b[4]) + ((b[5],) if b[5] is not None else ()) for b in fblocks]
        result.update(emit_tuple_blocks(*args, fn, stem, f'OCaml.Vm.Primitives.Uncaught.{ns}',
            f'OCaml/Vm/Primitives/Uncaught/{ns}.lean', sel, starts=[b[0] for b in fblocks],
            chunked=(), flag=FLAG, route=route, render_code=render))
    return result
