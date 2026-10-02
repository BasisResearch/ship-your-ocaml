#!/usr/bin/env python3
"""Generate captured-token lexer tables and compare their model execution."""
import os
from pathlib import Path
import subprocess
import tempfile
from census import ROOT

ocaml = Path(os.environ.get('OCAMLBIN', str(Path.home()/'toolchains/ocaml-4.14.4/bin')))
with tempfile.TemporaryDirectory(prefix='bc-lexer-') as tmp:
    src = Path(tmp)/'lexer.mll'
    src.write_bytes((ROOT/'c/tests/bc/lexer.mll').read_bytes())
    subprocess.run([ocaml/'ocamllex', src], check=True)
    subprocess.run(['python3', ROOT/'scripts/difftest_bc.py', src.with_suffix('.ml'),
                    '--timeout', '300', '--json', ROOT/'results/bc-lexer.json'], check=True)
