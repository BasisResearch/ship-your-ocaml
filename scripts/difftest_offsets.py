#!/usr/bin/env python3
"""Check both OFFSET arms against OCaml 4.14.4 at signed word boundaries."""
import json
import os
from pathlib import Path
import struct
import subprocess
import tempfile
from census import ROOT
from gen_opcodes import opcodes
from probe_offset_width import sections


def main():
    compiler = Path(os.environ.get('OCAMLC', str(Path.home() / 'toolchains/ocaml-4.14.4/bin/ocamlc')))
    assert subprocess.check_output([compiler, '-version'], text=True).strip() == '4.14.4'
    stdlib = subprocess.check_output([compiler, '-where'], text=True).strip()
    common = '''external size : unit -> int = "caml_sys_const_word_size"
external exit : int -> 'a = "caml_sys_exit"
external ( + ) : int -> int -> int = "%addint"
external ( > ) : int -> int -> bool = "%greaterthan"
type 'a ref = { mutable contents : 'a }
external ref : 'a -> 'a ref = "%makemutable"
external (!) : 'a ref -> 'a = "%field0"
external opaque : 'a -> 'a = "%opaque"
external incr : int ref -> unit = "%incr"
'''
    rows = []
    with tempfile.TemporaryDirectory(prefix='bc-offsets-') as tmp:
        src, exe = Path(tmp)/'probe.ml', Path(tmp)/'probe.byte'
        for arm, body in [('OFFSETINT', 'size () + 1'),
                          ('OFFSETREF', 'let r = opaque (ref (size ())) in incr r; !r')]:
            src.write_text(common + f'let () = exit (if ({body}) > 0 then 1 else 2)\n')
            subprocess.run([compiler, '-nopervasives', '-nostdlib', '-I', stdlib,
                            '-o', exe, src], check=True)
            original = exe.read_bytes()
            start, length = sections(original)[b'CODE']
            code = struct.unpack('<'+'i'*(length//4), original[start:start+length])
            sites = [i for i, word in enumerate(code[:-1]) if word == opcodes().index(arm) and code[i+1] == 1]
            assert len(sites) == 1, (arm, sites)
            for operand in [1, -1, -65, 0x3fffffff, 0x40000000, 0x7fffffff, -0x40000000, -0x80000000]:
                changed = bytearray(original)
                struct.pack_into('<i', changed, start+4*(sites[0]+1), operand)
                exe.write_bytes(changed)
                h = subprocess.run([compiler.with_name('ocamlrun'), exe], capture_output=True)
                m = subprocess.run([ROOT/'.lake/build/bin/runbc', exe, '1000'], capture_output=True)
                passed = h.returncode == m.returncode and h.stdout == m.stdout and not h.stderr
                rows.append(dict(arm=arm, operand=operand, host_exit=h.returncode,
                                 model_exit=m.returncode, passed=passed))
                assert passed, (rows[-1], m.stderr)
    (ROOT/'results/bc-offsets.json').write_text(json.dumps(rows, indent=2)+'\n')
    print(f'{len(rows)} OFFSET boundary differentials passed')


if __name__ == '__main__':
    main()
