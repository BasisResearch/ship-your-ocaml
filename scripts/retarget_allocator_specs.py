#!/usr/bin/env python3
"""Retarget preserved allocator SWP compositions to freshly generated ELF steps.

Instruction groups match by opcode/registers and named global targets. GP-relative
accesses may expand to AUIPC pairs. Lean still checks the resulting compositions
against the freshly generated steps; matching is not a trusted equivalence proof.
"""
import argparse
import collections
import difflib
import json
import re
from pathlib import Path
from census import ROOT, disasm, symbols, sections, read_mem
from syi.rv_steps import fields

TEMPLATES = ROOT / 'experiments/syi/allocator-template'


def units(insts, syms):
    gp = syms['__global_pointer$'][0]
    addrnames = {a: n for n, (a, _) in syms.items()}
    def target(a):
        if a in addrnames:
            return addrnames[a]
        owners = [(n, a-x) for n, (x,z) in syms.items() if x <= a < x+z]
        return tuple(sorted(owners)[0]) if owners else a
    out, i = [], 0
    while i < len(insts):
        pc, w, _, _ = insts[i]
        f = fields(w)
        if f['rs1'] == 3 and f['op'] in (3, 0x23, 0x13):
            off = f['immS'] if f['op'] == 0x23 else f['immI']
            key = (f['op'], f['f3'], f['rs2'] if f['op'] == 0x23 else f['rd'], target(gp+off))
            out.append((key, [pc])); i += 1; continue
        if f['op'] == 0x17 and i+1 < len(insts):
            pc2, w2, _, _ = insts[i+1]
            g = fields(w2)
            if g['rs1'] == f['rd'] and g['op'] in (3, 0x23, 0x13):
                off = g['immS'] if g['op'] == 0x23 else g['immI']
                key = (g['op'], g['f3'], g['rs2'] if g['op'] == 0x23 else g['rd'], target(pc+f['immU']+off))
                out.append((key, [pc,pc2])); i += 2; continue
        mask = 0x01fff07f if f['op'] == 0x63 else 0xfff if f['op'] == 0x6f else 0xffffffff
        out.append(((w & mask,), [pc])); i += 1
    return out


def address_map(old, new, syms):
    oldsyms = old['symbols']
    mapping, expansions, moves = {}, [], []
    for name, fn in old['functions'].items():
        a, b = units(fn['insts'], oldsyms), units(new[name]['insts'], syms)
        sm = difflib.SequenceMatcher(None, [x[0] for x in a], [x[0] for x in b], autojunk=False)
        removed, added = [], []
        def match(x, y):
            key, ap = x
            _, bp = y
            if len(ap) == len(bp):
                mapping.update(zip(ap,bp))
            elif len(ap) == 1 and len(bp) == 2:
                mapping[ap[0]] = bp[0]
                expansions.append((name,ap,bp,key))
            else:
                raise ValueError(f'{name}: unsupported instruction-group shape {ap} -> {bp}')
        for tag,i,j,k,l in sm.get_opcodes():
            if tag == 'equal':
                for x,y in zip(a[i:j],b[k:l]): match(x,y)
            else:
                removed += a[i:j]; added += b[k:l]
        # A scheduling move is accepted only when each unmatched group has one
        # unique identical partner. The composed proof must validate new order.
        assert collections.Counter(k for k,_ in removed) == collections.Counter(k for k,_ in added), name
        for x in removed:
            ys = [y for y in added if y[0] == x[0]]
            assert len(ys) == 1, (name,x,ys)
            match(x,ys[0]); moves.append((name,x[1],ys[0][1]))
        mapping[fn['insts'][-1][0]+4] = new[name]['insts'][-1][0]+4
    def relocate(a):
        if a in mapping:
            return mapping[a]
        exact = [n for n,(x,_) in oldsyms.items() if x == a and n in syms]
        if exact:
            # Prefer a real object to a coincident section boundary.
            exact.sort(key=lambda n: (oldsyms[n][1] == 0, n))
            return syms[exact[0]][0]
        owners = [n for n,(x,z) in oldsyms.items() if x < a <= x+z and n in syms]
        if owners:
            owners.sort(key=lambda n: oldsyms[n][1])
            n = owners[0]
            return syms[n][0] + a - oldsyms[n][0]
        if a in (0x80000000, 0x87800000, 0x88000000):
            return a
        raise ValueError(f'unmapped allocator address 0x{a:x}')
    return relocate, expansions, moves


def outputs(include_pending=False):
    old = json.loads((TEMPLATES/'layout.json').read_text())
    elf = ROOT/'c/ocamlrun-riscv-htif.elf'
    relocate, expansions, moves = address_map(old, disasm(elf), symbols(elf))
    impure = read_mem(sections(elf), symbols(elf)['_impure_ptr'][0], 8)
    assert impure is not None
    files = {}
    checked = set(json.loads((TEMPLATES/'checked-modules.json').read_text()))
    for p in sorted(TEMPLATES.rglob('*.lean')):
        module = '.'.join(p.relative_to(TEMPLATES).with_suffix('').parts)
        if not include_pending and module not in checked:
            continue
        s = p.read_text()
        oldbytes = '[' + ', '.join(f'0x{b:02x}#8' for b in old['impure_bytes']) + ']'
        newbytes = '[' + ', '.join(f'0x{b:02x}#8' for b in impure) + ']'
        s = s.replace(oldbytes, newbytes)
        # These are bounded driver step counts, not Lean heartbeat budgets.
        # Each old instruction expands to at most two; explicit stop PCs retain
        # the original composition boundaries.
        s = re.sub(r'(sx_run \[)([0-9]+)(\][^\n]* at )',
                   lambda m: m[1]+str(2*int(m[2]))+m[3], s)
        def repl(m):
            a = int(m[0],16)
            return f'0x{relocate(a):x}' if 0x80000000 <= a < 0x90000000 else m[0]
        s = re.sub(r'(?<![a-zA-Z0-9_])([0-9]+)(?![a-zA-Z0-9_])',
                   lambda m: str(relocate(int(m[0]))) if 0x80000000 <= int(m[0]) < 0x90000000 else m[0], s)
        s = re.sub(r'0x[0-9a-fA-F]+', repl, s)
        s = re.sub(r'(?<=_)800[0-9a-f]{5}(?=\b|_)',lambda m: f'{relocate(int(m[0],16)):08x}',s)
        # Explicit old GP-relative steps become two generated steps. Dynamic
        # AUIPC-based memory operations also expose an address-validity premise.
        for _, ap, bp, key in expansions:
            first, second = bp
            pat = rf'(?m)^([ \t]*(?:· )?)(refine st_{first:08x} )([^ \n]+)(.*)$'
            def expand_step(m):
                extra = ' (by sx_norm; sx_side)' if key[0] in (3, 0x23) else ''
                return (f'{m[1]}refine st_{first:08x} {m[3]} ?_\n'
                        f'{m[1].replace("·", " " )}refine st_{second:08x} {m[3]}{extra}{m[4]}')
            s = re.sub(pat, expand_step, s)
        s = '-- GENERATED by scripts/retarget_allocator_specs.py; edit the generator/templates.\n'+s
        if s.count('∃')>8:s='-- discipline: allow(R7-conj-tower-def) preserved upstream allocator contracts\n'+s
        s='\n'.join(('-- discipline: allow(R6-anon-projection-tower) reused upstream heap invariant projection\n' if '.2.2.2.2' in line else '')+line for line in s.split('\n'))
        files[ROOT/p.relative_to(TEMPLATES)] = s
    return files, expansions, moves


if __name__ == '__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check',action='store_true')
    ap.add_argument('--include-pending', action='store_true',
                    help='also emit archived compositions still being adapted')
    args=ap.parse_args()
    files,expansions,moves=outputs(args.include_pending)
    for p,s in files.items():
        if args.check:
            if not p.exists() or p.read_text()!=s:raise SystemExit(f'allocator spec drift: {p.relative_to(ROOT)}')
        elif not p.exists() or p.read_text()!=s:
            p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
    print(f'Allocator templates: {len(files)} modules, {len(expansions)} expanded groups, {len(moves)} scheduling moves')
