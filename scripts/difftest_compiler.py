#!/usr/bin/env python3
"""Compare boot/ocamlc's hello.cmo and console output under host and BcSem."""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import tempfile
from census import ROOT


def run(directory, timeout):
    ocaml = Path(os.environ.get('OCAMLBIN', str(Path.home()/'toolchains/ocaml-4.14.4/bin')))
    compiler = ROOT/'vendor/ocaml-4.14.4/boot/ocamlc'
    for kind in ['host', 'model']:
        work = directory/kind
        (work/'stdlib').mkdir(parents=True, exist_ok=True)
        (work/'hello.ml').write_text('let () = print_endline "hello"\n')
        for name in ['stdlib.cmi', 'camlinternalFormatBasics.cmi']:
            shutil.copyfile(ocaml.parent/'lib/ocaml'/name, work/'stdlib'/name)
        for name in ['hello.cmo', 'hello.cmi']:
            (work/name).unlink(missing_ok=True)
    args = ['-nostdlib', '-I', 'stdlib', '-c', 'hello.ml']
    host = subprocess.run([ocaml/'ocamlrun', compiler, *args], cwd=directory/'host',
                          capture_output=True, timeout=timeout)
    # GC counters are explicit runtime observations, not guessed from the
    # abstract heap. Capture them without changing the returned OCaml values.
    reference = {name: (directory/'host'/name).read_bytes() for name in ['hello.cmo', 'hello.cmi']}
    shutil.copyfile(ROOT/'c/tests/bc/gc_snapshot.c', directory/'gc_snapshot.c')
    (directory/'empty.ml').write_text('let () = ()\n')
    subprocess.run([ocaml/'ocamlc', '-make-runtime', '-o', directory/'statsrun',
                    '-ccopt', '-Wl,--wrap=caml_gc_quick_stat', directory/'gc_snapshot.c',
                    directory/'empty.ml'], check=True, cwd=directory, capture_output=True)
    stats = directory/'gc.csv'
    stats.unlink(missing_ok=True)
    observed = subprocess.run([directory/'statsrun', compiler, *args], cwd=directory/'host',
                              env={**os.environ, 'BC_GC_SNAPSHOTS': str(stats)},
                              capture_output=True, timeout=timeout)
    assert observed.returncode == host.returncode and observed.stdout == host.stdout and observed.stderr == host.stderr
    assert all((directory/'host'/name).read_bytes() == data for name, data in reference.items())
    model = subprocess.run([ROOT/'.lake/build/bin/runbc', '--fs', directory/'model',
                            compiler, '100000000', '--gc-stats', stats, '--', *args], capture_output=True, timeout=timeout)
    (directory/'host.stdout').write_bytes(host.stdout)
    (directory/'host.stderr').write_bytes(host.stderr)
    (directory/'model.stdout').write_bytes(model.stdout)
    (directory/'model.stderr').write_bytes(model.stderr)
    artifacts = {}
    for name in ['hello.cmo', 'hello.cmi']:
        paths = [directory/kind/name for kind in ['host', 'model']]
        artifacts[name] = dict(zip(['host_sha256', 'model_sha256'],
                                  [hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None for p in paths]))
        artifacts[name]['equal'] = all(p.exists() for p in paths) and paths[0].read_bytes() == paths[1].read_bytes()
    used = re.search(rb'halt primitives (\[.*\]) exit', model.stderr, re.S)
    primitive_names = json.loads(used[1]) if used else []
    ledgered = set(primitive_names) == set(json.loads((ROOT/'results/ocamlc-executed.json').read_text())['primitives'])
    passed = ledgered and b'gc_remaining 0' in model.stderr and host.returncode == model.returncode == 0 and host.stdout == model.stdout and not host.stderr and all(a['equal'] for a in artifacts.values())
    result = dict(passed=passed, compiler_sha256=hashlib.sha256(compiler.read_bytes()).hexdigest(),
                  gc_observation_source='host quick_stat linker wrapper; machine correspondence remains a premise',
                  gc_snapshot_count=len(stats.read_text().splitlines()),
                  model_primitive_names=primitive_names, model_primitive_count=len(primitive_names), measured_primitive_set_equal=ledgered, argv=args, host_exit=host.returncode, model_exit=model.returncode,
                  output_equal=host.stdout == model.stdout, artifacts=artifacts,
                  model_status=model.stderr.decode(errors='replace').strip())
    (ROOT/'results/bc-compiler.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result), flush=True)
    return 0 if passed else 1


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--workdir', type=Path)
    parser.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()
    if args.workdir:
        return run(args.workdir.resolve(), args.timeout)
    with tempfile.TemporaryDirectory(prefix='bc-compiler-') as directory:
        return run(Path(directory), args.timeout)


if __name__ == '__main__':
    raise SystemExit(main())
