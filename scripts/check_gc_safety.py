#!/usr/bin/env python3
"""Conservative bytecode scan + host validation; does not prove GcSafe boot/ocamlc."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
from gen_bc_rules import inputs, DEFAULT_DUMP, ROOT

HOST = Path(os.environ.get('HOST_OCAML', Path.home() / 'toolchains/ocaml-4.14.4/bin'))
BOOT = ROOT / 'vendor/ocaml-4.14.4/boot/ocamlc'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def validate():
    version = subprocess.check_output([str(HOST/'ocamlc'), '-version'], text=True).strip()
    assert version == '4.14.4', version
    lib = subprocess.check_output([str(HOST/'ocamlc'), '-where'], text=True).strip()
    words, decoded, units, entries, targets = inputs(BOOT, DEFAULT_DUMP)
    dump = subprocess.check_output([str(DEFAULT_DUMP), str(BOOT)], text=True)
    names = {int(m[1]): m[2] for line in dump.splitlines()
             if (m := re.match(r'^\s*(\d+)\s+C_CALL\d+\s+(\S+)', line))}
    sites = []
    # Soundly overapproximate lazy flow: without a proved type/alias analysis,
    # every tag/identity/structural observation is potentially lazy-reachable.
    observations = {'ISINT', 'SWITCH', 'EQ', 'NEQ', 'BEQ', 'BNEQ'}
    prim_prefixes = ('caml_obj_', 'caml_compare', 'caml_equal', 'caml_notequal',
                     'caml_hash', 'caml_output_value', 'caml_marshal')
    for pc, (op, args, size) in decoded.items():
        prim = names.get(pc, '')
        if op in observations or prim.startswith(prim_prefixes):
            unit = next((n for n, (a,b) in units.items() if a <= pc < b), '<unassigned>')
            sites.append({'pc': pc, 'unit': unit, 'opcode': op, 'primitive': prim or None,
                          'lazy_reachability': 'unresolved (conservative may-alias)'})
    runs = []
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        (tmp/'hello.ml').write_bytes((ROOT/'c/tests/compile/hello.ml').read_bytes())
        command = [str(HOST/'ocamlrun'), str(BOOT), '-nostdlib', '-I', lib, '-c', 'hello.ml']
        baseline = None
        for param in ['', 's=4096', 's=8192', 's=16384']:
            env = {**os.environ, 'OCAMLRUNPARAM': param}
            r = subprocess.run(command, cwd=tmp, env=env, capture_output=True, check=True)
            cmo = (tmp/'hello.cmo').read_bytes()
            result = (r.stdout, r.stderr, cmo)
            if baseline is None:
                baseline = result
            assert result == baseline, f'compile differs at {param}'
            measured = subprocess.run(command, cwd=tmp,
                env={**env, 'OCAMLRUNPARAM': param + ',v=0x400'}, capture_output=True, check=True)
            assert measured.stdout == r.stdout and (tmp/'hello.cmo').read_bytes() == cmo
            stats = {m[1]: int(m[2]) for line in measured.stderr.decode().splitlines()
                     if (m := re.fullmatch(r'(\w+): (\d+)', line))}
            assert stats.get('minor_collections', 0) > 0
            runs.append({'runtime_param': param or '(default)', 'exit': r.returncode,
                         'stdout_sha256': digest(r.stdout), 'stderr_sha256': digest(r.stderr),
                         'cmo_sha256': digest(cmo), 'statistics': stats})
        (tmp/'typed.ml').write_bytes((ROOT/'c/tests/gc/lazy_physical_equality.ml').read_bytes())
        subprocess.run([str(HOST/'ocamlc'), '-o', 'typed.byte', 'typed.ml'], cwd=tmp, check=True)
        typed = subprocess.check_output([str(HOST/'ocamlrun'), str(tmp/'typed.byte')], text=True)
        assert typed == 'false true\n', typed
    return {'host_version': version, 'boot_sha256': digest(BOOT.read_bytes()),
            'source_sha256': digest((ROOT/'c/tests/compile/hello.ml').read_bytes()),
            'compiled_code_words': len(words), 'closure_entries': len(entries),
            'scan_scope': 'all instructions, including unreachable ones; no lazy-flow discharge claimed',
            'observation_sites': sites, 'hello_compiles': runs,
            'typed_physical_equality_counterexample': typed.strip(),
            'GcSafe_boot_ocamlc': 'OPEN: static may-alias sites unresolved; differential runs are evidence only'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = validate()
    text = json.dumps(result, separators=(',', ':')) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(json.dumps({'sites': len(result['observation_sites']),
        'minor_collections': [r['statistics']['minor_collections'] for r in result['hello_compiles']],
        'identical_compiles': True, 'GcSafe_boot_ocamlc': result['GcSafe_boot_ocamlc']}))
