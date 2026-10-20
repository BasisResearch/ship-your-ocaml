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


# `exit`'s stdio handler on the fatal path: `stdio_exit_handler` walks
# `__sglue` (`_fwalk_sglue`) and closes stdin, stdout and stderr (`_fclose_r`:
# lock, `__sflush_r`, `__sclose` -> `_close_r` -> `_close`, unlock).
PROBE_STDIO = None
# each block's memory accesses (address, window kind), store log and saved-ra load,
# read off a symbolic pass over the block bodies
STDIO_FAST = {
    'StdioExitHandler.enter':
        {'mem': []},
    'FwalkSglue.pro':
        {'mem': [('R 2 + 18446744073709551536#64 + 48#64', 'window'), ('R 2 + 18446744073709551536#64 + 40#64', 'window'), ('R 2 + 18446744073709551536#64 + 32#64', 'window'), ('R 2 + 18446744073709551536#64 + 24#64', 'window'), ('R 2 + 18446744073709551536#64 + 16#64', 'window'), ('R 2 + 18446744073709551536#64 + 8#64', 'window'), ('R 2 + 18446744073709551536#64 + 72#64', 'window'), ('R 2 + 18446744073709551536#64 + 64#64', 'window'), ('R 2 + 18446744073709551536#64 + 56#64', 'window')], 'log': '[((R 2 - 80#64 + 48#64).toNat, 8, R 18), ((R 2 - 80#64 + 40#64).toNat, 8, R 19), ((R 2 - 80#64 + 32#64).toNat, 8, R 20), ((R 2 - 80#64 + 24#64).toNat, 8, R 21), ((R 2 - 80#64 + 16#64).toNat, 8, R 22), ((R 2 - 80#64 + 8#64).toNat, 8, R 23), ((R 2 - 80#64 + 72#64).toNat, 8, R 1), ((R 2 - 80#64 + 64#64).toNat, 8, R 8), ((R 2 - 80#64 + 56#64).toNat, 8, R 9)]', 'addrSimpOnly': True, 'addrFacts': ['show BitVec.signExtend 64 0#12 = 0#64 by decide', 'show BitVec.signExtend 64 8#12 = 8#64 by decide', 'show BitVec.signExtend 64 16#12 = 16#64 by decide', 'show BitVec.signExtend 64 24#12 = 24#64 by decide', 'show BitVec.signExtend 64 32#12 = 32#64 by decide', 'show BitVec.signExtend 64 40#12 = 40#64 by decide', 'show BitVec.signExtend 64 48#12 = 48#64 by decide', 'show BitVec.signExtend 64 56#12 = 56#64 by decide', 'show BitVec.signExtend 64 64#12 = 64#64 by decide', 'show BitVec.signExtend 64 72#12 = 72#64 by decide']},
    'FwalkSglue.niobs':
        {'mem': [('R 18 + 8#64', 'window')]},
    'FwalkSglue.bound':
        {'mem': [('R 18 + 16#64', 'window')]},
    'FwalkSglue.flagsOk':
        {'mem': [('R 8 + 16#64', 'window')]},
    'FwalkSglue.fileOk':
        {'mem': [('R 8 + 18#64', 'window')]},
    'FwalkSglue.call':
        {'mem': []},
    'FwalkSglue.acc':
        {'mem': []},
    'FwalkSglue.nextMore':
        {'mem': []},
    'FwalkSglue.nextDone':
        {'mem': []},
    'FwalkSglue.glue':
        {'mem': [('R 18', 'window')]},
    'FwalkSglue.leave':
        {'mem': [('R 2 + 72#64', 'window'), ('R 2 + 64#64', 'window'), ('R 2 + 56#64', 'window'), ('R 2 + 48#64', 'window'), ('R 2 + 40#64', 'window'), ('R 2 + 32#64', 'window'), ('R 2 + 24#64', 'window'), ('R 2 + 8#64', 'window'), ('R 2 + 16#64', 'window')], 'ra': 0, 'addrSimpOnly': True, 'addrFacts': ['show BitVec.signExtend 64 0#12 = 0#64 by decide', 'show BitVec.signExtend 64 8#12 = 8#64 by decide', 'show BitVec.signExtend 64 16#12 = 16#64 by decide', 'show BitVec.signExtend 64 24#12 = 24#64 by decide', 'show BitVec.signExtend 64 32#12 = 32#64 by decide', 'show BitVec.signExtend 64 40#12 = 40#64 by decide', 'show BitVec.signExtend 64 48#12 = 48#64 by decide', 'show BitVec.signExtend 64 56#12 = 56#64 by decide', 'show BitVec.signExtend 64 64#12 = 64#64 by decide', 'show BitVec.signExtend 64 72#12 = 72#64 by decide']},
    'Fclose.pro':
        {'mem': [('R 2 + 18446744073709551584#64 + 24#64', 'window'), ('R 2 + 18446744073709551584#64', 'window')], 'log': '[((R 2 - 32#64 + 24#64).toNat, 8, R 1), ((R 2 - 32#64).toNat, 8, R 18)]', 'addrSimpOnly': True, 'addrFacts': ['show BitVec.signExtend 64 0#12 = 0#64 by decide', 'show BitVec.signExtend 64 24#12 = 24#64 by decide']},
    'Fclose.reent':
        {'mem': [('R 2 + 16#64', 'window'), ('R 2 + 8#64', 'window')], 'log': '[((R 2 + 16#64).toNat, 8, R 8), ((R 2 + 8#64).toNat, 8, R 9)]'},
    'Fclose.cleanup':
        {'mem': [('R 10 + 72#64', 'window')]},
    'Fclose.flags2':
        {'mem': [('R 8 + 176#64', 'window'), ('R 8 + 16#64', 'window')]},
    'Fclose.sstr':
        {'mem': []},
    'Fclose.lock':
        {'mem': [('R 8 + 160#64', 'window')]},
    'Fclose.live':
        {'mem': [('R 8 + 16#64', 'window')]},
    'Fclose.flush':
        {'mem': []},
    'Fclose.closeFn':
        {'mem': [('R 8 + 80#64', 'window')]},
    'Fclose.close':
        {'mem': [('R 8 + 48#64', 'window')]},
    'Fclose.closed':
        {'mem': []},
    'Fclose.smbf':
        {'mem': [('R 8 + 16#64', 'window')]},
    'Fclose.ub':
        {'mem': [('R 8 + 88#64', 'window')]},
    'Fclose.lb':
        {'mem': [('R 8 + 120#64', 'window')]},
    'Fclose.sfpLock':
        {'mem': []},
    'Fclose.clear':
        {'mem': [('R 8 + 176#64', 'window'), ('R 8 + 16#64', 'window')], 'log': '[((R 8 + 16#64).toNat, 2, 0#64)]'},
    'Fclose.unlock':
        {'mem': [('R 8 + 160#64', 'window')]},
    'Fclose.toClose':
        {'mem': []},
    'Fclose.closeLock':
        {'mem': [('R 8 + 160#64', 'window')]},
    'Fclose.sfpUnlock':
        {'mem': []},
    'Fclose.leave':
        {'mem': [('R 2 + 24#64', 'window'), ('R 2 + 16#64', 'window'), ('R 2 + 8#64', 'window'), ('R 2', 'window')], 'ra': 0, 'addrSimpOnly': True, 'addrFacts': ['show BitVec.signExtend 64 0#12 = 0#64 by decide', 'show BitVec.signExtend 64 8#12 = 8#64 by decide', 'show BitVec.signExtend 64 16#12 = 16#64 by decide', 'show BitVec.signExtend 64 24#12 = 24#64 by decide']},
    'Sflush.proWrite':
        {'mem': [('R 11 + 16#64', 'window'), ('R 2 + 18446744073709551568#64 + 32#64', 'window'), ('R 2 + 18446744073709551568#64 + 8#64', 'window'), ('R 2 + 18446744073709551568#64 + 40#64', 'window')], 'log': '[((R 2 - 48#64 + 32#64).toNat, 8, R 8), ((R 2 - 48#64 + 8#64).toNat, 8, R 19), ((R 2 - 48#64 + 40#64).toNat, 8, R 1)]', 'addrSimpOnly': True, 'addrFacts': ['show BitVec.signExtend 64 0#12 = 0#64 by decide', 'show BitVec.signExtend 64 8#12 = 8#64 by decide', 'show BitVec.signExtend 64 16#12 = 16#64 by decide', 'show BitVec.signExtend 64 32#12 = 32#64 by decide', 'show BitVec.signExtend 64 40#12 = 40#64 by decide']},
    'Sflush.proRead':
        {'mem': [('R 11 + 16#64', 'window'), ('R 2 + 18446744073709551568#64 + 32#64', 'window'), ('R 2 + 18446744073709551568#64 + 8#64', 'window'), ('R 2 + 18446744073709551568#64 + 40#64', 'window')], 'log': '[((R 2 - 48#64 + 32#64).toNat, 8, R 8), ((R 2 - 48#64 + 8#64).toNat, 8, R 19), ((R 2 - 48#64 + 40#64).toNat, 8, R 1)]', 'addrSimpOnly': True, 'addrFacts': ['show BitVec.signExtend 64 0#12 = 0#64 by decide', 'show BitVec.signExtend 64 8#12 = 8#64 by decide', 'show BitVec.signExtend 64 16#12 = 16#64 by decide', 'show BitVec.signExtend 64 32#12 = 32#64 by decide', 'show BitVec.signExtend 64 40#12 = 40#64 by decide']},
    'Sflush.ur':
        {'mem': [('R 11 + 112#64', 'window')]},
    'Sflush.toEnd':
        {'mem': []},
    'Sflush.noBase':
        {'mem': [('R 2 + 16#64', 'window'), ('R 11 + 24#64', 'window')], 'log': '[((R 2 + 16#64).toNat, 8, R 18)]'},
    'Sflush.base':
        {'mem': [('R 2 + 16#64', 'window'), ('R 11 + 24#64', 'window')], 'log': '[((R 2 + 16#64).toNat, 8, R 18)]'},
    'Sflush.noBaseEnd':
        {'mem': [('R 2 + 16#64', 'window')]},
    'Sflush.unbuf':
        {'mem': [('R 2 + 24#64', 'window'), ('R 11', 'window'), ('R 11', 'window')], 'log': '[((R 2 + 24#64).toNat, 8, R 9), ((R 11).toNat, 8, R 18)]'},
    'Sflush.w':
        {'mem': [('R 8 + 12#64', 'window')], 'log': '[((R 8 + 12#64).toNat, 4, R 15)]'},
    'Sflush.toDone':
        {'mem': []},
    'Sflush.done':
        {'mem': [('R 2 + 24#64', 'window')]},
    'Sflush.leave':
        {'mem': [('R 2 + 40#64', 'window'), ('R 2 + 32#64', 'window'), ('R 2 + 8#64', 'window')], 'ra': 0, 'addrSimpOnly': True, 'addrFacts': ['show BitVec.signExtend 64 0#12 = 0#64 by decide', 'show BitVec.signExtend 64 8#12 = 8#64 by decide', 'show BitVec.signExtend 64 32#12 = 32#64 by decide', 'show BitVec.signExtend 64 40#12 = 40#64 by decide']},
    'Sclose.enter':
        {'mem': [('R 11 + 18#64', 'window')]},
    'CloseR.pro':
        {'mem': [('R 2 + 18446744073709551600#64', 'window'), ('0x80064d48#64', 'global'), ('R 2 + 18446744073709551600#64 + 8#64', 'window')], 'log': '[((R 2 - 16#64).toNat, 8, R 8), ((0x80064d48#64).toNat, 4, 0#64), ((R 2 - 16#64 + 8#64).toNat, 8, R 1)]', 'logFacts': ['imm20Of', 'BitVec.reduceAdd', 'BitVec.reduceSub', "show BitVec.signExtend 64 (BitVec.extractLsb' 12 20 145303#32 ++ 0#12) = 143360#64 by decide"]},
    'CloseR.back':
        {'mem': []},
    'CloseR.leave':
        {'mem': [('R 2 + 8#64', 'window'), ('R 2', 'window')], 'ra': 0, 'addrSimpOnly': True, 'addrFacts': ['show BitVec.signExtend 64 0#12 = 0#64 by decide', 'show BitVec.signExtend 64 8#12 = 8#64 by decide']},
    'Close.pro':
        {'mem': [('0x80064918#64', 'global'), ('R 2 + 18446744073709551584#64 + 24#64', 'window')], 'log': '[((R 2 - 32#64 + 24#64).toNat, 8, R 1)]'},
    'Close.range':
        {'mem': []},
    'Close.file':
        {'mem': []},
    'Close.leave':
        {'mem': [('R 2 + 24#64', 'window')], 'ra': 0, 'addrSimpOnly': True, 'addrFacts': ['show BitVec.signExtend 64 0#12 = 0#64 by decide', 'show BitVec.signExtend 64 24#12 = 24#64 by decide']},
    'SfpLockAcquire.enter':
        {'mem': []},
    'SfpLockRelease.enter':
        {'mem': []},
    'RetargetLockClose.leaf':
        {'mem': []},
    'Sflush.read':
        {'mem': [('R 11 + 8#64', 'window'), ('R 11 + 16#64', 'window')], 'log': '[((R 11 + 16#64).toNat, 2, R 14 ||| 2048#64)]', 'logFacts': ['imm20Of', 'BitVec.reduceAdd', 'BitVec.reduceSub', "show BitVec.signExtend 64 (BitVec.extractLsb' 12 20 6071#32 ++ 0#12) = 4096#64 by decide"]},
    'Close.kind':
        {'mem': [('2147896728#64 + (R 13 <<< 1 + R 13) <<< 3', 'window')], 'addrSimpOnly': True, 'addrFacts': ['imm20Of', 'BitVec.reduceAdd', 'BitVec.reduceSub', "show BitVec.signExtend 64 (BitVec.extractLsb' 12 20 411159#32 ++ 0#12) = 409600#64 by decide"]},
    'Close.clear':
        {'mem': [('R 12 + (R 15 + R 13) <<< 3', 'window')], 'log': '[((R 12 + Sail.shift_bits_left (R 15 + R 13) 3#6).toNat, 4, 0#64)]', 'addrSimpOnly': True, 'addrFacts': []},
}
# each block's register interface, as `runGM` evaluates it (read off a probe run)
STDIO_REGS = {
    'StdioExitHandler.enter':
        '[(10, 2147894888#64), (11, 2147798632#64), (12, 2147894176#64), (1, R 1)]',
    'FwalkSglue.pro':
        '[(19, 18446744073709551615#64), (23, 1#64), (22, 0#64), (21, R 11), (20, R 10), (18, R 12), (2, R 2 + 18446744073709551536#64), (1, R 1), (8, R 8), (9, R 9), (10, R 10), (11, R 11), (12, R 12)]',
    'FwalkSglue.niobs':
        '[(15, bytesVal .lw (loads.getD 0 [])), (10, R 10), (18, R 18)]',
    'FwalkSglue.bound':
        '[(9, bytesVal .ld (loads.getD 0 []) + (R 15 <<< 32 >>> 32 <<< 7 + (R 15 <<< 32 >>> 32 <<< 6 + (-R 15 <<< 32 >>> 32) <<< 3))), (8, bytesVal .ld (loads.getD 0 [])), (15, R 15 <<< 32 >>> 32), (10, R 10), (18, R 18)]',
    'FwalkSglue.flagsOk':
        '[(15, bytesVal .lhu (loads.getD 0 [])), (8, R 8), (10, R 10), (23, R 23)]',
    'FwalkSglue.fileOk':
        '[(10, R 20), (11, R 8), (15, bytesVal .lh (loads.getD 0 [])), (8, R 8), (19, R 19), (20, R 20)]',
    'FwalkSglue.call':
        '[(1, R 1), (10, R 10), (11, R 11), (21, R 21)]',
    'FwalkSglue.acc':
        '[(22, BitVec.signExtend 64 (Sail.BitVec.extractLsb (R 10 ||| R 22) 31 0)), (10, R 10)]',
    'FwalkSglue.nextMore':
        '[(8, R 8 + 184#64), (9, R 9), (10, R 10)]',
    'FwalkSglue.nextDone':
        '[(8, R 8 + 184#64), (9, R 9), (10, R 10)]',
    'FwalkSglue.glue':
        '[(18, bytesVal .ld (loads.getD 0 [])), (10, R 10)]',
    'FwalkSglue.leave':
        '[(2, R 2 + 80#64), (22, bytesVal .ld (loads.getD 8 [])), (10, R 22), (23, bytesVal .ld (loads.getD 7 [])), (21, bytesVal .ld (loads.getD 6 [])), (20, bytesVal .ld (loads.getD 5 [])), (19, bytesVal .ld (loads.getD 4 [])), (18, bytesVal .ld (loads.getD 3 [])), (9, bytesVal .ld (loads.getD 2 [])), (8, bytesVal .ld (loads.getD 1 [])), (1, bytesVal .ld (loads.getD 0 []))]',
    'Fclose.pro':
        '[(2, R 2 + 18446744073709551584#64), (1, R 1), (10, R 10), (11, R 11), (18, R 18)]',
    'Fclose.reent':
        '[(9, R 10), (8, R 11), (2, R 2), (10, R 10), (11, R 11)]',
    'Fclose.cleanup':
        '[(15, bytesVal .ld (loads.getD 0 [])), (10, R 10)]',
    'Fclose.flags2':
        '[(15, bytesVal .lw (loads.getD 0 []) &&& 1#64), (14, bytesVal .lh (loads.getD 1 [])), (8, R 8), (10, R 10)]',
    'Fclose.sstr':
        '[(14, R 14 &&& 512#64), (10, R 10)]',
    'Fclose.lock':
        '[(10, bytesVal .ld (loads.getD 0 [])), (1, R 1), (8, R 8)]',
    'Fclose.live':
        '[(15, bytesVal .lh (loads.getD 0 [])), (8, R 8), (10, R 10)]',
    'Fclose.flush':
        '[(10, R 9), (11, R 8), (1, R 1), (8, R 8), (9, R 9)]',
    'Fclose.closeFn':
        '[(18, R 10), (15, bytesVal .ld (loads.getD 0 [])), (8, R 8), (10, R 10)]',
    'Fclose.close':
        '[(10, R 9), (11, bytesVal .ld (loads.getD 0 [])), (1, R 1), (8, R 8), (9, R 9), (15, R 15)]',
    'Fclose.closed':
        '[(10, R 10)]',
    'Fclose.smbf':
        '[(15, bytesVal .lhu (loads.getD 0 []) &&& 128#64), (8, R 8), (10, R 10)]',
    'Fclose.ub':
        '[(11, bytesVal .ld (loads.getD 0 [])), (8, R 8), (10, R 10)]',
    'Fclose.lb':
        '[(11, bytesVal .ld (loads.getD 0 [])), (8, R 8), (10, R 10)]',
    'Fclose.sfpLock':
        '[(1, R 1), (10, R 10)]',
    'Fclose.clear':
        '[(15, bytesVal .lw (loads.getD 0 []) &&& 1#64), (8, R 8), (10, R 10)]',
    'Fclose.unlock':
        '[(10, bytesVal .ld (loads.getD 0 [])), (1, R 1), (8, R 8)]',
    'Fclose.toClose':
        '[(10, R 10)]',
    'Fclose.closeLock':
        '[(10, bytesVal .ld (loads.getD 0 [])), (1, R 1), (8, R 8)]',
    'Fclose.sfpUnlock':
        '[(1, R 1), (10, R 10)]',
    'Fclose.leave':
        '[(2, R 2 + 32#64), (18, bytesVal .ld (loads.getD 3 [])), (10, R 18), (9, bytesVal .ld (loads.getD 2 [])), (8, bytesVal .ld (loads.getD 1 [])), (1, bytesVal .ld (loads.getD 0 []))]',
    'Sflush.proWrite':
        '[(19, R 10), (8, R 11), (15, bytesVal .lh (loads.getD 0 []) &&& 8#64), (2, R 2 + 18446744073709551568#64), (14, bytesVal .lh (loads.getD 0 [])), (1, R 1), (10, R 10), (11, R 11)]',
    'Sflush.proRead':
        '[(19, R 10), (8, R 11), (15, bytesVal .lh (loads.getD 0 []) &&& 8#64), (2, R 2 + 18446744073709551568#64), (14, bytesVal .lh (loads.getD 0 [])), (1, R 1), (10, R 10), (11, R 11)]',
    'Sflush.read':
        '[(15, R 14 ||| 2048#64), (13, bytesVal .lw (loads.getD 0 [])), (10, R 10), (11, R 11), (14, R 14)]',
    'Sflush.ur':
        '[(13, bytesVal .lw (loads.getD 0 [])), (10, R 10), (11, R 11)]',
    'Sflush.toEnd':
        '[(10, R 10)]',
    'Sflush.noBase':
        '[(18, bytesVal .ld (loads.getD 0 [])), (2, R 2), (10, R 10), (11, R 11)]',
    'Sflush.base':
        '[(18, bytesVal .ld (loads.getD 0 [])), (2, R 2), (10, R 10), (11, R 11)]',
    'Sflush.noBaseEnd':
        '[(18, bytesVal .ld (loads.getD 0 [])), (2, R 2), (10, R 10)]',
    'Sflush.unbuf':
        '[(15, 0#64), (9, BitVec.signExtend 64 (Sail.BitVec.extractLsb (bytesVal .ld (loads.getD 0 [])) 31 0 + -Sail.BitVec.extractLsb (R 18) 31 0)), (14, R 14 &&& 3#64), (2, R 2), (10, R 10), (11, R 11), (18, R 18)]',
    'Sflush.w':
        '[(8, R 8), (9, R 9), (10, R 10), (15, R 15)]',
    'Sflush.toDone':
        '[(10, R 10)]',
    'Sflush.done':
        '[(9, bytesVal .ld (loads.getD 0 [])), (2, R 2), (10, R 10)]',
    'Sflush.leave':
        '[(2, R 2 + 48#64), (10, 0#64), (19, bytesVal .ld (loads.getD 2 [])), (8, bytesVal .ld (loads.getD 1 [])), (1, bytesVal .ld (loads.getD 0 []))]',
    'Sclose.enter':
        '[(11, bytesVal .lh (loads.getD 0 [])), (10, R 10)]',
    'CloseR.pro':
        '[(15, 2147897752#64), (10, R 11), (8, R 10), (2, R 2 + 18446744073709551600#64), (1, R 1), (11, R 11)]',
    'CloseR.back':
        '[(15, 18446744073709551615#64), (10, R 10)]',
    'CloseR.leave':
        '[(2, R 2 + 16#64), (8, bytesVal .ld (loads.getD 1 [])), (1, bytesVal .ld (loads.getD 0 [])), (10, R 10)]',
    'Close.pro':
        '[(13, R 10), (2, R 2 + 18446744073709551584#64), (15, bytesVal .lw (loads.getD 0 [])), (1, R 1), (10, R 10)]',
    'Close.range':
        '[(15, 31#64), (10, R 10), (13, R 13)]',
    'Close.kind':
        '[(11, bytesVal .lw (loads.getD 0 [])), (14, 2147896728#64 + (R 13 <<< 4 + R 13 <<< 3)), (12, 2147896728#64), (15, R 13 <<< 1), (10, R 10), (13, R 13)]',
    'Close.file':
        '[(10, 4#64), (11, R 11)]',
    'Close.clear':
        '[(10, 0#64), (12, R 12 + (R 15 <<< 3 + R 13 <<< 3)), (15, R 15 <<< 3 + R 13 <<< 3), (13, R 13)]',
    'Close.leave':
        '[(2, R 2 + 32#64), (1, bytesVal .ld (loads.getD 0 [])), (10, R 10)]',
    'SfpLockAcquire.enter':
        '[(10, 2147896712#64), (1, R 1)]',
    'SfpLockRelease.enter':
        '[(10, 2147896712#64), (1, R 1)]',
    'RetargetLockClose.leaf':
        '[(1, R 1), (10, R 10)]',
}


def stdio_exit_spec():
    """Same tuples as `functions_spec`; `PROBE_STDIO` stands in for the register lists."""
    P = PROBE_STDIO
    reg = lambda r: r
    fast = lambda f: None if P else f
    def fn(fname, stem, ns, route, blocks):
        return (fname, stem, ns, route, True,
                [(a, n, k, reg(STDIO_REGS[f'{ns}.{n}']), t, fast(STDIO_FAST[f'{ns}.{n}'])) for (a, n, k, t, f) in blocks])
    blk = lambda a, n, k, t=False, f=None: (a, n, k, t, f if f is not None else {})
    return [
      fn('stdio_exit_handler', 'Stdio_exit_handler', 'StdioExitHandler', None, [
        blk(0x8003e900, 'enter', [1, 10])]),
      fn('_fwalk_sglue', '_fwalk_sglue', 'FwalkSglue', {0x8003f6a0: 'F', 0x8003f6cc: 'F', 0x8003f6dc: 'F',
        0x8003f6f0: 'TF', 0x8003f6f8: 'F'}, [
        blk(0x8003f65c, 'pro', [1, 2, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23]),
        blk(0x8003f69c, 'niobs', [10, 18]),
        blk(0x8003f6a4, 'bound', [10, 15, 18]),
        blk(0x8003f6c8, 'flagsOk', [8, 10, 23]),
        blk(0x8003f6d0, 'fileOk', [8, 10, 19, 20]),
        blk(0x8003f6e0, 'call', [1, 10, 11, 21]),
        blk(0x8003f6e4, 'acc', [10, 22]),
        blk(0x8003f6ec, 'nextMore', [8, 9, 10], t=True),
        blk(0x8003f6ec, 'nextDone', [8, 9, 10]),
        blk(0x8003f6f4, 'glue', [10, 18]),
        blk(0x8003f6fc, 'leave', [2, 10, 22])]),
      fn('_fclose_r', '_fclose_r', 'Fclose', {0x8004ce74: 'F', 0x8004ce88: 'F', 0x8004ce90: 'F', 0x8004cea0: 'F',
        0x8004cea8: 'T', 0x8004cfa4: 'T', 0x8004cec0: 'F', 0x8004ced0: 'F', 0x8004cedc: 'F', 0x8004cee4: 'T',
        0x8004cf00: 'T', 0x8004cf20: 'T'}, [
        blk(0x8004ce68, 'pro', [1, 2, 10, 11, 18]),
        blk(0x8004ce78, 'reent', [2, 8, 9, 10, 11]),
        blk(0x8004ce8c, 'cleanup', [10]),
        blk(0x8004ce94, 'flags2', [8, 10]),
        blk(0x8004cea4, 'sstr', [10, 14], t=True),
        blk(0x8004cf98, 'lock', [1, 8, 10]),
        blk(0x8004cfa0, 'live', [8, 10], t=True),
        blk(0x8004ceac, 'flush', [1, 8, 9, 10]),
        blk(0x8004ceb8, 'closeFn', [8, 10]),
        blk(0x8004cec4, 'close', [1, 8, 9, 10, 15]),
        blk(0x8004ced0, 'closed', [10]),
        blk(0x8004ced4, 'smbf', [8, 10]),
        blk(0x8004cee0, 'ub', [8, 10], t=True),
        blk(0x8004cefc, 'lb', [8, 10], t=True),
        blk(0x8004cf10, 'sfpLock', [1, 10]),
        blk(0x8004cf14, 'clear', [8, 10], t=True),
        blk(0x8004cfc8, 'unlock', [1, 8, 10]),
        blk(0x8004cfd0, 'toClose', [10]),
        blk(0x8004cf24, 'closeLock', [1, 8, 10]),
        blk(0x8004cf2c, 'sfpUnlock', [1, 10]),
        blk(0x8004cf30, 'leave', [2, 10, 18])]),
      fn('__sflush_r', '__sflush_r', 'Sflush', {0x8003e514: 'TF', 0x8003e52c: 'T', 0x8003e6c8: 'F',
        0x8003e640: 'TF', 0x8003e65c: 'T', 0x8003e668: 'F'}, [
        blk(0x8003e4f4, 'proWrite', [1, 2, 8, 10, 11, 19], t=True),
        blk(0x8003e4f4, 'proRead', [1, 2, 8, 10, 11, 19]),
        blk(0x8003e518, 'read', [10, 11, 14], t=True),
        blk(0x8003e6c4, 'ur', [10, 11]),
        blk(0x8003e6cc, 'toEnd', [10]),
        blk(0x8003e638, 'noBase', [2, 10, 11, 18], t=True),
        blk(0x8003e638, 'base', [2, 10, 11, 18]),
        blk(0x8003e6d4, 'noBaseEnd', [2, 10]),
        blk(0x8003e644, 'unbuf', [2, 9, 10, 11, 14, 18], t=True),
        blk(0x8003e664, 'w', [8, 9, 10, 15]),
        blk(0x8003e66c, 'toDone', [10]),
        blk(0x8003e6d0, 'done', [2, 10]),
        blk(0x8003e620, 'leave', [2, 10])]),
      fn('__sclose', '__sclose', 'Sclose', None, [
        blk(0x80040184, 'enter', [10, 11])]),
      fn('_close_r', '_close_r', 'CloseR', {0x800421ac: 'F'}, [
        blk(0x80042188, 'pro', [1, 2, 8, 10, 11]),
        blk(0x800421a8, 'back', [10]),
        blk(0x800421b0, 'leave', [2, 10])]),
      fn('_close', '_close', 'Close', {0x80000b3c: 'T', 0x80000b50: 'F', 0x80000b70: 'F', 0x80000b78: 'F'}, [
        blk(0x80000b28, 'pro', [1, 2, 10], t=True),
        blk(0x80000b4c, 'range', [10, 13]),
        blk(0x80000b54, 'kind', [10, 13]),
        blk(0x80000b74, 'file', [10, 11]),
        blk(0x80000b7c, 'clear', [10, 12, 13, 15]),
        blk(0x80000b90, 'leave', [2, 10])]),
      fn('__sfp_lock_acquire', '__sfp_lock_acquire', 'SfpLockAcquire', None, [
        blk(0x8003ed68, 'enter', [1, 10])]),
      fn('__sfp_lock_release', '__sfp_lock_release', 'SfpLockRelease', None, [
        blk(0x8003ed74, 'enter', [1, 10])]),
      fn('__retarget_lock_close_recursive', '__retarget_lock_close_recursive', 'RetargetLockClose', None, [
        blk(0x80042530, 'leaf', [1, 10])]),
    ]


def emit_uncaught(root, functions, decode, code, text_base, lib, build_cfg, literal):
    ld = lambda n, k='ld': f'bytesVal .{k} (loads.getD {n} [])'
    rest = lambda ks: ', '.join(f'({k}, R {k})' for k in ks)
    result = {}
    args = (root, functions, decode, code, text_base, lib, build_cfg, literal)
    for fn, stem, ns, route, render, fblocks in functions_spec(ld, rest) + stdio_exit_spec():
        sel = [(b[1], b[2], b[3], b[4]) + ((b[5],) if b[5] is not None else ()) for b in fblocks]
        result.update(emit_tuple_blocks(*args, fn, stem, f'OCaml.Vm.Primitives.Uncaught.{ns}',
            f'OCaml/Vm/Primitives/Uncaught/{ns}.lean', sel, starts=[b[0] for b in fblocks],
            chunked=(), flag=FLAG, route=route, render_code=render))
    return result
