#!/usr/bin/env python3
"""Exercise nested runtime callbacks and fatal-exception processing."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
from census import ROOT


def main():
    ocaml = Path(os.environ.get('OCAMLBIN', str(Path.home()/'toolchains/ocaml-4.14.4/bin')))
    cases = {
        'callbacks': (ROOT/'c/tests/bc/callbacks.ml').read_text(),
        'uncaught_fallback': 'let () = at_exit (fun () -> print_endline "cleanup"); failwith "boom"\n',
        'uncaught_printer': 'let () = Printexc.register_printer (function Failure s -> Some ("custom:" ^ s) | _ -> None); at_exit (fun () -> print_endline "cleanup"); failwith "boom"\n',
        'uncaught_handler': 'let () = Printexc.set_uncaught_exception_handler (fun e _ -> prerr_endline ("handler:" ^ Printexc.to_string e)); failwith "boom"\n',
        'uncaught_at_exit_raises': 'let () = at_exit (fun () -> failwith "cleanup failed"); failwith "original"\n',
        'uncaught_callback': 'external cb : (unit -> unit) -> unit -> unit = "caml_callback"\nlet () = cb (fun () -> raise Not_found) ()\n',
    }
    rows = []
    with tempfile.TemporaryDirectory(prefix='bc-callbacks-') as directory:
        d = Path(directory)
        for name, source in cases.items():
            src, exe = d/(name+'.ml'), d/(name+'.byte')
            src.write_text(source)
            subprocess.run([ocaml/'ocamlc', '-custom', '-o', exe, src], check=True)
            # The custom runtime exposes the real C caml_callback functions.
            host = subprocess.run([exe], capture_output=True, timeout=60, cwd=d)
            model = subprocess.run([ROOT/'.lake/build/bin/runbc', exe], capture_output=True, timeout=60, cwd=d)
            passed = host.returncode == model.returncode and host.stdout + host.stderr == model.stdout
            row = dict(test=name, passed=passed, host_exit=host.returncode,
                       model_exit=model.returncode, status=model.stderr.decode().strip())
            if not passed:
                row.update(host_output=(host.stdout+host.stderr).decode(), model_output=model.stdout.decode())
            rows.append(row)
            print(json.dumps(row), flush=True)
        # The exception-returning C API is called from a real C main, after
        # a Stdlib-free bytecode initializer registers its closures.
        for suffix in ['ml', 'c']:
            (d/('callback_api.'+suffix)).write_bytes((ROOT/('c/tests/bc/callback_api.'+suffix)).read_bytes())
        exe = d/'callback_api.byte'
        subprocess.run([ocaml/'ocamlc', '-custom', '-nopervasives', '-nostdlib',
                        '-I', ocaml.parent/'lib/ocaml', '-o', exe,
                        d/'callback_api.ml', d/'callback_api.c'], check=True, cwd=d)
        host = subprocess.run([exe], capture_output=True, timeout=60)
        model = subprocess.run([ROOT/'.lake/build/bin/runbc', '--callbacks', exe,
                                'one:41', 'two:40,2', 'three:10,12,20', 'five:1,2,3,4,5',
                                'raise1:7', 'raise2:7,8', 'raise3:7,8,9'], capture_output=True, timeout=60)
        row = dict(test='callback_exn_api', passed=host.returncode == model.returncode == 0 and host.stdout == model.stdout,
                   host_exit=host.returncode, model_exit=model.returncode, status=model.stderr.decode().strip())
        if not row['passed']:
            row.update(host_output=host.stdout.decode(), model_output=model.stdout.decode())
        rows.append(row)
        print(json.dumps(row), flush=True)
    (ROOT/'results/bc-callbacks.json').write_text(json.dumps(rows, indent=2)+'\n')
    return 0 if all(r['passed'] for r in rows) else 1


if __name__ == '__main__':
    raise SystemExit(main())
