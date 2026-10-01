#!/usr/bin/env python3
"""Measure the opcode/primitive set executed by boot/ocamlc compiling hello.ml.
Uses the vendored-version debug runtime's -t trace, never a static PRIM count.
"""
import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
SOURCE = 'let () = print_endline "hello"\n'


def main():
    p = argparse.ArgumentParser(__doc__)
    p.add_argument('--output', type=Path, default=ROOT / 'results/ocamlc-executed.json')
    a = p.parse_args()
    ocaml = Path(os.environ.get('OCAMLBIN', str(Path.home() / 'toolchains/ocaml-4.14.4/bin')))
    compiler = ROOT / 'vendor/ocaml-4.14.4/boot/ocamlc'
    ops, prims = collections.Counter(), collections.Counter()
    with tempfile.TemporaryDirectory(prefix='ocamlc-census-') as d:
        tmp = Path(d)
        (tmp / 'hello.ml').write_text(SOURCE)
        with (tmp / 'trace').open('w') as trace:
            subprocess.run([ocaml / 'ocamlrund', '-t', compiler, '-I', ocaml.parent / 'lib/ocaml',
                            '-c', 'hello.ml'], cwd=tmp, stdout=trace, stderr=subprocess.STDOUT,
                           check=True, timeout=120)
        assert (tmp / 'hello.cmo').is_file()
        with (tmp / 'trace').open() as trace:
            for line in trace:
                m = re.match(r'^\s*\d+\s+([A-Z][A-Z0-9_]*)\b(?:\s+(caml_\w+))?', line)
                if m:
                    ops[m[1]] += 1
                    if m[2]:
                        prims[m[2]] += 1
    result = dict(source=SOURCE, compiler_sha256=hashlib.sha256(compiler.read_bytes()).hexdigest(),
                  command='ocamlrund -t boot/ocamlc -I <4.14.4-stdlib> -c hello.ml',
                  compiler_exit=0, opcode_count=len(ops), primitive_count=len(prims),
                  opcodes=dict(sorted(ops.items())), primitives=dict(sorted(prims.items())))
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(f'{len(ops)} opcodes, {len(prims)} primitives; compiler exit 0')


if __name__ == '__main__':
    main()
