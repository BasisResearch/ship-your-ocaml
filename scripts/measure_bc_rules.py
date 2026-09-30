#!/usr/bin/env python3
"""Rebuild each generated backend module sequentially under a 24 GiB cap.

Only the selected modules' generated build-cache .olean files are removed.
The resulting JSON records GNU time's wall/CPU/RSS measurements and source
hashes. Dependency builds are cached; no heartbeat limit is changed.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from check_bc_audit import ROOT, wait_memory
from gen_bc_rules import MODULES


def parse_time(text):
    def number(label):
        return float(next(line.split(': ', 1)[1] for line in text.splitlines() if label in line))
    wall = next(line.split(': ', 1)[1] for line in text.splitlines() if 'Elapsed (wall clock)' in line)
    seconds = 0.
    for part in wall.split(':'):
        seconds = seconds * 60 + float(part)
    return {'wall_seconds': seconds, 'user_seconds': number('User time (seconds)'),
            'system_seconds': number('System time (seconds)'),
            'max_rss_kib': int(number('Maximum resident set size (kbytes)')),
            'exit_status': int(number('Exit status:'))}


def report(logs):
    manifest = json.loads((ROOT/'OCaml/Programs/Generated/manifest.json').read_text())
    result = {'memory_cap_gib': 24, 'heartbeat_budget': 'Lean default (200000)',
              'executable_sha256': manifest['executable_sha256'], 'modules': {}}
    for name, log in logs.items():
        item = parse_time(log)
        if item['exit_status'] != 0 or 'Build completed successfully' not in log:
            raise ValueError(f'{name} did not build successfully')
        source = ROOT/f'OCaml/Programs/Generated/{name}.lean'
        item.update(source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                    instructions=manifest['modules'][name]['instructions'],
                    blocks=manifest['modules'][name]['blocks'])
        result['modules'][name] = item
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--modules', nargs='+', default=MODULES, choices=MODULES)
    parser.add_argument('--output', type=Path, default=ROOT/'results/bprime_build.json')
    args = parser.parse_args()
    logs = {}
    for name in args.modules:
        wait_memory()
        module = f'OCaml.Programs.Generated.{name}'
        (ROOT/f'.lake/build/lib/lean/OCaml/Programs/Generated/{name}.olean').unlink(missing_ok=True)
        result = subprocess.run(['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=24G',
                                 '/usr/bin/time', '-v', 'lake', 'build', module],
                                cwd=ROOT, text=True, capture_output=True)
        print(result.stdout + result.stderr, flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
        logs[name] = result.stdout + result.stderr
    args.output.write_text(json.dumps(report(logs), indent=2) + '\n')


if __name__ == '__main__':
    main()
