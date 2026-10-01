#!/usr/bin/env python3
"""Inventory precisely primsF1 and their ELF entry/call structure."""
import argparse
import json
import re
from census import ROOT, disasm


def primitive_names():
    source = (ROOT / 'OCaml/Bytecode/Semantics.lean').read_text()
    declaration = source.split('def primsF1 : List String :=', 1)[1].split('/--', 1)[0]
    names = re.findall(r'"([^"]+)"', declaration)
    assert len(names) == len(set(names)) == 30
    return names


def inventory():
    functions = disasm(ROOT / 'c/ocamlrun-riscv-htif.elf')
    result = []
    for name in primitive_names():
        ins = functions[name]['insts']
        start, end = ins[0][0], ins[-1][0] + 4
        transfers = []
        for a, word, op, operands in ins:
            if op not in ('jal', 'jalr', 'j'):
                continue
            target = re.search(r'<([^+>]+)', operands)
            if target and target[1] == name:
                continue
            transfers.append(dict(pc=hex(a), op=op, target=target[1] if target else operands))
        result.append(dict(name=name, entry=hex(start), end=hex(end), instructions=len(ins), transfers=transfers))
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = ROOT / 'results/primitives-f1.json'
    text = json.dumps(inventory(), indent=2) + '\n'
    if args.check:
        if not path.exists() or path.read_text() != text:
            raise SystemExit('F1 primitive census drift')
    else:
        path.write_text(text)
    print('F1 primitive census: 30 functions')
