#!/usr/bin/env python3
"""Audit every generated block theorem, accepting only standard Lean axioms."""
import json
import re
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def wait_memory():
    while True:
        report = subprocess.check_output(['free', '-g'], text=True)
        available = int(next(line for line in report.splitlines() if line.startswith('Mem:')).split()[-1])
        print(report, end='', flush=True)
        if available >= 25:
            return
        print('bytecode audit: waiting for 25 GiB available', flush=True)
        time.sleep(30)


def main():
    wait_memory()
    result = subprocess.run(['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=24G',
                             'lake', 'env', 'lean', 'OCaml/Programs/Generated/Audit.lean'],
                            cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    audited = set()
    for line in result.stdout.splitlines():
        m = re.fullmatch(r"'([^']+)' depends on axioms: \[([^]]*)\]", line)
        n = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
        if m:
            if not set(m[2].split(', ')).issubset(ALLOWED):
                raise SystemExit('unexpected axioms: ' + line)
            audited.add(m[1])
        elif n:
            audited.add(n[1])
        else:
            raise SystemExit('unexpected audit output: ' + line)
    manifest = json.loads((ROOT/'OCaml/Programs/Generated/manifest.json').read_text())
    expected = {f'OCaml.Programs.Generated.{name}.f{fn["entry"]}_b{b["pc"]}_run'
                for name, stats in manifest['modules'].items()
                for fn in stats['functions'] for b in fn['blocks']}
    if audited != expected:
        raise SystemExit(f'audit coverage mismatch: missing {expected-audited}; extra {audited-expected}')
    print(f'bytecode axioms: OK ({len(audited)} generated block rules)')


if __name__ == '__main__':
    main()
