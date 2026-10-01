#!/usr/bin/env python3
"""Compare executable BcSem with vendored-version host ocamlrun (no Sail rebuild)."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def main():
    p = argparse.ArgumentParser(__doc__)
    p.add_argument('files', nargs='*', type=Path)
    p.add_argument('--json', type=Path)
    p.add_argument('--timeout', type=int, default=300)
    a = p.parse_args()
    ocaml = Path(os.environ.get('OCAMLBIN', str(Path.home() / 'toolchains/ocaml-4.14.4/bin')))
    rows = []
    with tempfile.TemporaryDirectory(prefix='bc-difftest-') as tmp:
        for source in a.files or sorted((ROOT / 'c/tests/difftest').glob('*.ml')):
            # Compile copies: ocamlc writes .cmi/.cmo beside its input.
            src = Path(tmp) / source.name
            src.write_bytes(source.read_bytes())
            exe = src.with_suffix('.byte')
            subprocess.run([ocaml / 'ocamlc', '-o', exe, src], check=True)
            host = subprocess.run([ocaml / 'ocamlrun', exe], capture_output=True, timeout=a.timeout, cwd=tmp)
            try:
                model = subprocess.run([ROOT / '.lake/build/bin/runbc', exe], capture_output=True, timeout=a.timeout, cwd=tmp)
                row = dict(test=source.stem, passed=host.returncode == model.returncode and host.stdout == model.stdout,
                           host_exit=host.returncode, model_exit=model.returncode,
                           status=model.stderr.decode(errors='replace').strip())
            except subprocess.TimeoutExpired:
                row = dict(test=source.stem, passed=False, status='timeout')
            rows.append(row)
            print(json.dumps(row), flush=True)
    if a.json:
        a.json.parent.mkdir(parents=True, exist_ok=True)
        a.json.write_text(json.dumps(rows, indent=2) + '\n')
    return 0 if all(r['passed'] for r in rows) else 1


if __name__ == '__main__':
    raise SystemExit(main())
