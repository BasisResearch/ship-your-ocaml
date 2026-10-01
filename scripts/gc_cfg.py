#!/usr/bin/env python3
"""Inspect the pinned collector through gen_fn's real CFG/budget checks.
No generator limits are overridden and no generated proofs are hand edited.
The report distinguishes CFG coverage from unavailable proof dependencies.
"""
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from census import ROOT, TOOLS

sys.path.insert(0, str(ROOT / 'scripts/syi'))
import gen_fn


def report():
    with tempfile.NamedTemporaryFile(mode='w+', suffix='.txt') as f:
        subprocess.run([TOOLS + 'objdump', '-d', str(ROOT / 'c/ocamlrun-riscv-htif.elf')],
                       stdout=f, check=True)
        f.flush()
        di = gen_fn.lib.parse_disasm(f.name)
        extents = gen_fn.function_extents(f.name)
        result = {'elf_sha256': hashlib.sha256((ROOT / 'c/ocamlrun-riscv-htif.elf').read_bytes()).hexdigest(),
                  'missing_generator_imports': [p for p in ['Vsa/Sim/DeriveCaseRow.lean']
                                                if not (ROOT / p).exists()], 'functions': {}}
        for name in ['caml_oldify_one', 'caml_oldify_mopup', 'caml_empty_minor_heap']:
            entry, end = extents[name]
            words = [di[a].word for a in sorted(di) if entry <= a < end]
            # CFG shape alone misses gp/auipc-immediate changes when text
            # addresses are stable. Hash the real little-endian instructions.
            digest = hashlib.sha256(b''.join(w.to_bytes(4, 'little') for w in words)).hexdigest()
            item = {'entry': hex(entry), 'instructions': len(words), 'instruction_sha256': digest}
            try:
                body, blocks = gen_fn.build_cfg(name, entry, di, extents)
                item['blocks'] = [str(b) for b in blocks]
                item['counted_loop_template'] = gen_fn.classify_loop(blocks) is not None
            except SystemExit as error:
                item['generator_rejection'] = str(error)
            result['functions'][name] = item
        return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    text = json.dumps(report(), indent=2) + '\n'
    if args.check:
        if text != (ROOT / 'results/gc-cfg.json').read_text():
            raise SystemExit('collector CFG report drift: run scripts/gc_cfg.py')
        print('collector CFG report: current')
    else:
        print(text, end='')
