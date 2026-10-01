#!/usr/bin/env python3
"""Host-runtime evidence of Forward transparency, not a machine proof."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
HOST = Path(os.environ.get('HOST_OCAML', Path.home() / 'toolchains/ocaml-4.14.4/bin'))
assert subprocess.check_output([str(HOST / 'ocamlc'), '-version'], text=True).strip() == '4.14.4'
with tempfile.TemporaryDirectory() as tmp:
    source = Path(tmp) / 'forward_isint.ml'
    output = Path(tmp) / 'forward.byte'
    shutil.copyfile(ROOT / 'c/tests/gc/forward_isint.ml', source)
    subprocess.run([str(HOST / 'ocamlc'), '-o', str(output), str(source)], check=True)
    observed = subprocess.check_output([str(HOST / 'ocamlrun'), str(output)], text=True)
    assert observed == 'false true\n', observed
    print('OCaml 4.14.4 Forward_tag ISINT across Gc.minor: ' + observed.strip())
