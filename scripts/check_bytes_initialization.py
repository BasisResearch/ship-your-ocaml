#!/usr/bin/env python3
"""Check the model's defined-read boundary (not a host value for undefined data)."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
from census import ROOT


def main():
    compiler = Path(os.environ.get('OCAMLC', str(Path.home() / 'toolchains/ocaml-4.14.4/bin/ocamlc')))
    cases = {
        'fresh': ('let b = Bytes.create 16 in Bytes.get b 0', False),
        'copied_unknown': ('let b = Bytes.create 16 in let c = Bytes.copy b in Bytes.get c 0', False),
        'string_alias_unknown': ('let b = Bytes.create 16 in String.get (Bytes.unsafe_to_string b) 0', False),
        'known_cell': ("let b = Bytes.create 16 in Bytes.set b 0 'A'; Bytes.get b 0", True),
        'copied_known_cell': ("let b = Bytes.create 16 in Bytes.set b 0 'A'; let c = Bytes.copy b in Bytes.get c 0", True),
    }
    rows = []
    with tempfile.TemporaryDirectory(prefix='bc-initialization-') as tmp:
        source, exe = Path(tmp)/'probe.ml', Path(tmp)/'probe.byte'
        for name, (expr, defined) in cases.items():
            source.write_text(f'let () = print_char ({expr})\n')
            subprocess.run([compiler, '-o', exe, source], check=True)
            result = subprocess.run([ROOT/'.lake/build/bin/runbc', exe], capture_output=True, timeout=30)
            passed = (result.returncode == 0 and result.stdout == b'A') if defined else (
                result.returncode == 3 and not result.stdout and
                (b'wrong at pc' in result.stderr or b'unsupported at pc' in result.stderr))
            rows.append(dict(test=name, defined=defined, passed=passed,
                             status=result.stderr.decode().strip()))
            assert passed, rows[-1]
    (ROOT/'results/bc-initialization-boundary.json').write_text(json.dumps(rows, indent=2)+'\n')
    print(f'{len(rows)} initialization-boundary cases passed')


if __name__ == '__main__':
    main()
