#!/usr/bin/env python3
"""Observe replacement and C-string key semantics in the host OCaml runtime."""
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def main():
    ocaml = Path(os.environ.get('OCAMLBIN', str(Path.home() / 'toolchains/ocaml-4.14.4/bin')))
    with tempfile.TemporaryDirectory(prefix='ocaml-named-') as tmp:
        work = Path(tmp)
        for filename in ('lookup.c', 'check.ml'):
            (work / filename).write_bytes((ROOT / 'c/tests/named-value' / filename).read_bytes())
        subprocess.run([ocaml / 'ocamlc', '-custom', '-o', 'check.byte', 'lookup.c', 'check.ml'],
                       cwd=work, check=True)
        result = subprocess.run([work / 'check.byte'], cwd=work, check=True, capture_output=True, text=True)
        assert result.stdout == '22 44\n', repr(result.stdout)
        print('named values: replacement and first-NUL key semantics verified (22 44)')


if __name__ == '__main__':
    main()
