#!/usr/bin/env python3
"""Reproduce HTIF's omitted long directory name and require checker rejection."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
from census import ROOT


def main():
    with tempfile.TemporaryDirectory(prefix='htif-long-name-') as tmp:
        d = Path(tmp)
        script = '## long-directory-name\nopen "/' + 'x'*256 + '" O_WRONLY|O_CREAT\nclose 3\nopendir "/"\nreaddir 1\nreaddir 1\nreaddir 1\nclosedir 1\n'
        (d/'probe.scripts').write_text(script)
        subprocess.run(['gcc', '-O1', '-w', '-DMEMFS', '-Ic/src/config', '-o', d/'driver',
                        'tcb/validation/driver.c'], cwd=ROOT, check=True)
        subprocess.run([d/'driver', d/'probe.scripts', d/'probe.trace'], cwd=ROOT,
                       stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, check=True)
        checked = subprocess.run([ROOT/'.lake/build/bin/tcbcheck', d/'probe.trace'],
                                 capture_output=True, text=True)
        assert checked.returncode == 1 and '\trejected\t5\treaddir 1\tnone\tbytes ' in checked.stdout
        result = dict(scope='native HTIF counterexample; specification side kernel-checked in DirectoryObstruction.lean',
                      name_bytes=256, summary=checked.stderr.strip(), rejection=checked.stdout.strip(),
                      htif_sha256=hashlib.sha256((ROOT/'c/src/htif.c').read_bytes()).hexdigest())
        (ROOT/'results/htif-directory-obstruction.trace').write_text((d/'probe.trace').read_text())
        (ROOT/'results/htif-directory-obstruction.json').write_text(json.dumps(result, indent=2)+'\n')
        print(result['summary'])


if __name__ == '__main__':
    main()
