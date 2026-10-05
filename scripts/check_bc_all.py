#!/usr/bin/env python3
"""Build and audit compiler shards sequentially, recording per-shard resources.

--measure invalidates only each selected shard's own .olean before building.
Results are checkpointed after every shard; --resume skips successful source
hashes already measured. The normal gate always builds/audits every shard.
"""
import argparse
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path
from check_bc_audit import ROOT, ALLOWED, wait_memory
from measure_bc_rules import parse_time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--measure', action='store_true')
    parser.add_argument('--family', choices=['All', 'Functions'], default='All')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--shards', nargs='+')
    parser.add_argument('--pause-file', type=Path)
    args = parser.parse_args()
    manifest = json.loads((ROOT/f'OCaml/Programs/Generated/{args.family}/manifest.json').read_text())
    destination = ROOT/f'results/bprime_{args.family.lower()}_build.json'
    report = (json.loads(destination.read_text()) if args.resume and destination.exists() else
              {'memory_cap_gib': 24, 'heartbeat_budget': 'Lean default (200000)',
               'executable_sha256': manifest['executable_sha256'], 'shards': {}})
    total = 0
    for name, stats in manifest['shards'].items():
        if args.shards and name not in args.shards:
            continue
        old = report['shards'].get(name)
        if args.measure and args.resume and old and old['source_sha256'] == stats['source_sha256']:
            total += stats['blocks']
            continue
        while args.pause_file and args.pause_file.exists():
            print('shard runner paused between builds', flush=True)
            time.sleep(5)
        wait_memory()
        if args.measure:
            (ROOT/f'.lake/build/lib/lean/OCaml/Programs/Generated/{args.family}/{name}.olean').unlink(missing_ok=True)
        result = subprocess.run(['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=24G',
                                 '/usr/bin/time', '-v', 'lake', 'build',
                                 f'OCaml.Programs.Generated.{args.family}.{name}'],
                                cwd=ROOT, capture_output=True, text=True)
        if result.returncode:
            raise SystemExit(result.stdout + result.stderr)
        timing = parse_time(result.stderr)
        wait_memory()
        audit = subprocess.run(['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=24G',
                                'lake', 'env', 'lean', f'OCaml/Programs/Generated/{args.family}/{name}Audit.lean'],
                               cwd=ROOT, capture_output=True, text=True)
        if audit.returncode:
            raise SystemExit(audit.stdout + audit.stderr)
        seen = set()
        pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)"
        for match in re.finditer(pattern, audit.stdout):
            axioms = set((match[2] or '').replace('\n', ' ').replace(' ', '').split(',')) - {''}
            if not axioms <= ALLOWED:
                raise SystemExit(f'{name}: nonstandard axioms {axioms}')
            seen.add(match[1])
        if seen != set(stats['theorems']):
            raise SystemExit(f'{name}: audit coverage mismatch')
        if re.sub(pattern, '', audit.stdout).strip():
            raise SystemExit(f'{name}: unexpected audit output: {audit.stdout}')
        total += len(seen)
        print(f'{name}: {stats["instructions"]} instructions, {len(seen)} rules; '
              f'{timing["wall_seconds"]} s; {timing["max_rss_kib"]} KiB', flush=True)
        if args.measure:
            report['shards'][name] = dict(timing, source_sha256=stats['source_sha256'],
                                         instructions=stats['instructions'], blocks=stats['blocks'],
                                         audited=len(seen))
            destination.write_text(json.dumps(report, indent=2) + '\n')
    print(f'compiler shard axioms: OK ({total} generated block rules)')


if __name__ == '__main__':
    main()
