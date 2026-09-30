#!/usr/bin/env python3
"""Retarget same-layout A0 library proofs, checking every changed word.

Sources are the preserved WHILE-only copies; code predicates are regenerated
separately by gen_library_pins.py. Addresses map by ELF symbols. Only JAL,
AUIPC and load immediates may differ. Proofs are subsequently kernel checked.
"""
import argparse
import json
import re
from pathlib import Path
from census import ROOT, disasm
from retarget_syi import NEW_ELF, funcs, symbol

SITES = {'strcmp': 'StrcmpSites', '__ssputs_r': 'SsputsSites', '__ssprint_r': 'SsprintSites'}


def jimm(w):
    return ((w >> 31) << 20) | (((w >> 12) & 255) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 1023) << 1)


def outputs():
    layout = json.loads((ROOT / 'experiments/syi/while-elf-only/library_layout.json').read_text())
    old, new = layout['functions'], disasm(NEW_ELF)
    syms_old, syms_new = layout['symbols'], funcs(NEW_ELF, 'TtDdRrBb')
    starts = {a: syms_new[n][0] for n, (a, _) in syms_old.items() if n in syms_new}
    starts[layout['tohost']] = symbol(NEW_ELF, 'tohost')
    for v in json.loads((ROOT / 'results/retarget.json').read_text())['ported_functions'].values():
        a,b = int(v['old'],16), int(v['new'],16)
        starts.update({a+i:b+i for i in range(v['size']+1)})
    for offset in (0, 8, 16, 32, 64, 80):
        starts[layout['tohost']+offset] = symbol(NEW_ELF, 'tohost')+offset
    for fn in old:
        oi,ni = old[fn]['insts'],new[fn]['insts']
        assert len(oi)==len(ni)
        starts.update({a:b for (a,_,_,_), (b,_,_,_) in zip(oi,ni)})
        starts[oi[-1][0]+4] = ni[-1][0]+4
    result = {}
    modules = list(SITES.items()) + [('strcmp', 'StrcmpSpec' + suffix) for suffix in ('', 'W', 'W2', 'W3', 'W4', 'Cond')]
    modules += [('memmove','SnprintfSpec18'), ('__ssputs_r','SnprintfSpec19'), ('__ssprint_r','SsprintCodeFrame'), ('__ssprint_r','SnprintfSpec20')]
    for name, module in modules:
        src = ROOT / f'experiments/syi/while-elf-only/Vsa/Sim/{module}.lean'
        text = src.read_text()
        if module in ('SnprintfSpec18','SnprintfSpec19','SnprintfSpec20'):
            kept = {'SnprintfSpec18':['Vsa.Sim.LibraryFacts','Vsa.Sim.Code.Memmove'], 'SnprintfSpec19':['Vsa.Sim.SsputsSites','Vsa.Sim.SnprintfSpec18'], 'SnprintfSpec20':['Vsa.Sim.SsprintCodeFrame','Vsa.Sim.SsprintSites','Vsa.Sim.SnprintfSpec19','Vsa.Sim.RegPins','Vsa.Sim.PtrArith']}[module]
            text = ''.join('import '+m+'\n' for m in kept) + re.sub(r'^import \S+\n','',text,flags=re.M)
        oi, ni = old[name]['insts'], new[name]['insts']
        assert len(oi) == len(ni), name
        amap = starts | {a: b for (a, _, _, _), (b, _, _, _) in zip(oi, ni)}
        amap[oi[-1][0]+4] = ni[-1][0]+4
        if name == 'strcmp':
            # The mask symbol has no nm size; derive both materialized addresses
            # directly from the adjacent AUIPC/LD words, not from guessed offsets.
            sext = lambda x, bits: x - (1 << bits) if x & (1 << (bits-1)) else x
            for i, ((a,w,_,_), (b,v,_,_)) in enumerate(zip(oi,ni)):
                if w & 127 == 0x17:
                    oa, na = a + sext(w & 0xfffff000,32), b + sext(v & 0xfffff000,32)
                    amap[oa] = na
                    assert oi[i+1][1] & 127 == ni[i+1][1] & 127 == 3
                    amap[oa + sext(oi[i+1][1] >> 20,12)] = na + sext(ni[i+1][1] >> 20,12)
        changes = {}
        for (_, w, _, _), (_, v, _, _) in zip(oi, ni):
            if w == v:
                continue
            op = w & 127
            if op == 0x6f:
                mask, width, u, z = 0xfff, 21, jimm(w), jimm(v)
            elif op == 0x17:
                mask, width, u, z = 0xfff, 20, w >> 12, v >> 12
            elif op == 3:
                mask, width, u, z = 0xfffff, 12, w >> 20, v >> 20
            else:
                raise ValueError(f'{name}: changed non-relocation instruction {w:08x}')
            assert w & mask == v & mask
            digits = (width + 3)//4
            changes[f'0x{u:0{digits}x}#{width}'] = f'0x{z:0{digits}x}#{width}'
            changes[f'0x{w:08x}#32'] = f'0x{v:08x}#32'
            changes[f'decode_{w:08x}'] = f'decode_{v:08x}'
            wb = [f'(0x{(w >> (8*k)) & 255:02x}#8)' for k in range(4)]
            vb = [f'(0x{(v >> (8*k)) & 255:02x}#8)' for k in range(4)]
            # Literal argument lists and byte reassembly equalities use both forms.
            pat = r'\s+'.join(re.escape(x) for x in wb)
            text = re.sub(pat, ' '.join(vb), text)
            def append(bs):
                return f'(({bs[3]}.append {bs[2]}).append {bs[1]}).append {bs[0]}'
            text = text.replace(append(wb), append(vb))
        pat = '|'.join(re.escape(s) for s in sorted(changes, key=len, reverse=True))
        text = re.sub(pat, lambda m: changes[m[0]], text) if changes else text
        text = re.sub(r'0x(8[0-9a-f]{7})\b', lambda m: f'0x{amap.get(int(m[1],16),int(m[1],16)):08x}', text)
        text = re.sub(r'(?<=_)(8[0-9a-f]{7})\b', lambda m: f'{amap.get(int(m[1],16),int(m[1],16)):08x}', text)
        # Short site names are historical names, retained for source compatibility.
        text = re.sub(r'^import Vsa.Sim.DecodeTable\S*\n', '', text, flags=re.M)
        text = text.replace('Vsa.Sim.DecodeTable', 'Vsa.Sim.ElfDecode')
        text = 'import Vsa.Sim.ElfDecode\n' + text
        text = '-- GENERATED by scripts/retarget_library_sites.py from the preserved WHILE site proofs.\n' + text
        text = '-- discipline: allow(R5-stepobs-volume) mechanically retargeted source battery; no new hand steps\n-- discipline: allow(R7-conj-tower-def) preserved source statements; no new post predicates\n' + text
        text = re.sub(r'^(theorem site_[0-9a-f]{8})', r'-- discipline: allow(R1-site-battery) mechanically retargeted source theorem\n\1', text, flags=re.M)
        text = '\n'.join(('-- discipline: allow(R6-anon-projection-tower) mechanically retargeted source projection\n' if '.2.2.2.2' in line else '') + line for line in text.split('\n'))
        if module == 'SnprintfSpec20':
            # Keep imported proof objects between stages instead of retaining
            # every elaboration metavariable in one large process.
            ns = text.index('namespace Vsa.Sim\n') + len('namespace Vsa.Sim\n')
            end = text.rindex('end Vsa.Sim')
            cuts = [ns] + [text.index('theorem '+n) for n in
                ('tr_ssprint_entry', 'tr_ssprint_iter1', 'tr_ssprint_iter2', 'tr_ssprint_tail')] + [end]
            for i, (lo, hi) in enumerate(zip(cuts,cuts[1:])):
                imports = '' if i == 0 else f'import Vsa.Sim.SnprintfSpec20Part{i-1}\n'
                # A doc comment immediately before a cut belongs to the next
                # theorem; make such retained comments ordinary comments.
                body = text[lo:hi].replace('/--', '/-')
                result[ROOT / f'Vsa/Sim/{module}Part{i}.lean'] = imports + text[:ns] + body + 'end Vsa.Sim\n'
            text = '-- GENERATED by scripts/retarget_library_sites.py\nimport Vsa.Sim.SnprintfSpec20Part4\n'
        result[ROOT / f'Vsa/Sim/{module}.lean'] = text
    return result


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    for p,s in outputs().items():
        if args.check:
            if not p.exists() or p.read_text() != s:
                raise SystemExit(f'library site drift: {p.relative_to(ROOT)}')
        elif not p.exists() or p.read_text() != s:
            p.write_text(s)
    print('A0 library sites: same-layout library sites and functional specifications current')
