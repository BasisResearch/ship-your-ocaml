#!/usr/bin/env python3
"""Reproduce native-C MEMFS trace evidence with the already built tcbcheck."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parent.parent

def main():
    with tempfile.TemporaryDirectory(prefix='htif-fs-') as tmp:
        d = Path(tmp)
        subprocess.run(['gcc', '-O1', '-w', '-DMEMFS', '-Ic/src/config', '-o', d/'driver',
                        'tcb/validation/driver.c'], cwd=ROOT, check=True)
        subprocess.run(['python3', 'tcb/validation/gen.py', d/'all.scripts'], cwd=ROOT, check=True)
        subprocess.run([d/'driver', d/'all.scripts', d/'memfs.trace'], stdin=subprocess.DEVNULL,
                       stdout=subprocess.DEVNULL, cwd=ROOT, check=True)
        r = subprocess.run([ROOT/'.lake/build/bin/tcbcheck', d/'memfs.trace'],
                           capture_output=True, text=True, check=True)
        paths = ['c/src/htif.c', 'tcb/validation/driver.c', 'tcb/validation/gen.py', 'tcb/TCB/Os/Syscall.lean']
        result = dict(scope='native C MEMFS traces; not an ELF machine proof',
                      summary=r.stderr.strip(),
                      sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths})
        (ROOT/'results/htif-fs.json').write_text(json.dumps(result, indent=2)+'\n')
        print(result['summary'])
if __name__ == '__main__':
    main()
