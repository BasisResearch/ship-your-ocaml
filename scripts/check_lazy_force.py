#!/usr/bin/env python3
"""Differential validation of the real stdlib force path, separate from its proof."""
from pathlib import Path
import os
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
HOST = Path(os.environ.get('HOST_OCAML', Path.home()/'toolchains/ocaml-4.14.4/bin'))
assert subprocess.check_output([str(HOST/'ocamlc'), '-version'], text=True).strip() == '4.14.4'
with tempfile.TemporaryDirectory() as td:
    tmp = Path(td)
    (tmp/'force.ml').write_bytes((ROOT/'c/tests/gc/lazy_force.ml').read_bytes())
    subprocess.run([str(HOST/'ocamlc'), '-o', 'force.byte', 'force.ml'], cwd=tmp, check=True)
    host = subprocess.run([str(HOST/'ocamlrun'), str(tmp/'force.byte')], capture_output=True, check=True)
    bc = subprocess.run([str(ROOT/'.lake/build/bin/runbc'), str(tmp/'force.byte')], capture_output=True, check=True)
    assert host.stdout == bc.stdout == b'42\n42\n42\nforced\nforced\n16\n'
    assert b'halt exit (some 0)' in bc.stderr, bc.stderr
    print('CamlinternalLazy.force host/BcSem: identical; ' + bc.stderr.decode().strip())
