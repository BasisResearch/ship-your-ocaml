#!/usr/bin/env python3
"""Reproduce the OFFSETINT width discrepancy, or validate its semantics repair.

The unmodified program exits 1. Changing only OFFSETINT's operand to 2^30
makes OCaml 4.14.4 exit 2; the former 64-bit-shift runbc model exits 1.
Use --expect-model 2 once stepI matches the pinned runtime's 32-bit shift.
"""
import argparse
import os
from pathlib import Path
import re
import struct
import subprocess
import tempfile
from census import ROOT
from gen_opcodes import opcodes


def sections(raw):
    count = struct.unpack('>I', raw[-16:-12])[0]
    table = len(raw) - 16 - 8*count
    entries = [(bytes(raw[i:i+4]), struct.unpack('>I', raw[i+4:i+8])[0])
               for i in range(table, len(raw)-16, 8)]
    position = table - sum(size for _, size in entries)
    result = {}
    for name, size in entries:
        result[name] = (position, size)
        position += size
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--expect-model', type=int, choices=[1, 2])
    args = ap.parse_args()
    compiler = Path(os.environ.get('OCAMLC', str(Path.home() / 'toolchains/ocaml-4.14.4/bin/ocamlc')))
    host = compiler.with_name('ocamlrun')
    runbc = ROOT / '.lake/build/bin/runbc'
    version = subprocess.check_output([str(compiler), '-version'], text=True).strip()
    if version != '4.14.4':
        raise ValueError('probe requires OCaml 4.14.4')
    stdlib = subprocess.check_output([str(compiler), '-where'], text=True).strip()
    with tempfile.TemporaryDirectory(prefix='a1-offset-width-') as directory:
        directory = Path(directory)
        source, executable = directory/'probe.ml', directory/'probe.byte'
        source.write_text('external size : unit -> int = "caml_sys_const_word_size"\n'
                          'external exit : int -> \'a = "caml_sys_exit"\n'
                          'external ( + ) : int -> int -> int = "%addint"\n'
                          'external ( > ) : int -> int -> bool = "%greaterthan"\n'
                          'let () = exit (if size () + 1 > 0 then 1 else 2)\n')
        subprocess.run([str(compiler), '-nopervasives', '-nostdlib', '-I', stdlib,
                        '-o', str(executable), str(source)], check=True, capture_output=True)
        original = executable.read_bytes()
        sec = sections(original)
        start, size = sec[b'CODE']
        pstart, psize = sec[b'PRIM']
        names = original[pstart:pstart+psize].split(b'\0')
        code = struct.unpack('<'+'i'*(size//4), original[start:start+size])
        ops = opcodes()
        prefix = [ops.index('CONST0'), ops.index('C_CALL1'),
                  names.index(b'caml_sys_const_word_size'), ops.index('OFFSETINT'), 1]
        if list(code[:len(prefix)]) != prefix:
            raise ValueError('compiler changed the probe prefix')
        changed = bytearray(original)
        struct.pack_into('<i', changed, start + 4*(len(prefix)-1), 1 << 30)
        for label, raw, expected in [('baseline', original, 1), ('wide operand', changed, 2)]:
            executable.write_bytes(raw)
            h = subprocess.run([str(host), str(executable)], capture_output=True, text=True)
            r = subprocess.run([str(runbc), str(executable), '100'], capture_output=True, text=True)
            observed = re.search(r'halt exit \(some (\d+)\)', r.stderr)
            if h.returncode != expected or h.stdout or h.stderr or r.stdout or not observed:
                raise ValueError(f'unexpected probe behaviour: {label}')
            model = int(observed[1])
            if (label == 'baseline' and model != 1) or model not in (1, 2):
                raise ValueError('unexpected runbc result')
            if label == 'wide operand' and args.expect_model is not None and model != args.expect_model:
                raise ValueError(f'runbc exit {model}, expected {args.expect_model}')
            print(f'{label}: host exit {expected}; runbc exit {model}')


if __name__ == '__main__':
    main()
