#!/usr/bin/env python3
"""Conservative call-graph census and generated application summaries.

Normal/over-application summaries are generated for projection, constant and
single-field functions. Every GRAB entry has a complete under-application
summary. Dynamic call edges remain explicitly unresolved, never guessed.
"""
import argparse
import hashlib
import json
from collections import Counter
from gen_bc_rules import ROOT, OUT, DEFAULT_DUMP, inputs, TRANSFER

DEST = OUT/'Functions'


def certificate(entry, words, decoded, pcs):
    end = pcs[-1] + decoded[pcs[-1]][2]
    raw = words[entry:end+1]
    sites = []
    for pc in pcs:
        op, args, size = decoded[pc]
        operands = ', '.join(str(a) if a >= 0 else f'({a})' for a in args)
        sites.append(f'⟨{pc-entry}, ⟨.{op}, [{operands}]⟩, {size}, by decide, rfl, rfl, rfl⟩')
    name = f'f{entry}'
    text = (f'def {name}_code : Code := #[{", ".join(str(w)+"#32" for w in raw)}]\n'
            f'def {name} : CertifiedBlock := ⟨{entry}, {name}_code, [\n  '+',\n  '.join(sites)+']⟩\n')
    return name, text, f'P.code.extract {entry} {entry+len(raw)} = {name}_code'


def shape(entry, decoded):
    pc = entry
    req = 0
    pcs = []
    if decoded[pc][0] == 'GRAB':
        req = decoded[pc][1][0]
        pcs.append(pc)
        pc += 2
    if not 0 <= req <= 7:
        return None
    op, operands, size = decoded[pc]
    if op.startswith('ACC') and op != 'ACC':
        arg = int(op[3:])
        if arg > req: return None
        value = f'v{arg}'
    elif op in {'CONST0', 'CONST1', 'CONST2', 'CONST3', 'CONSTINT'}:
        value = f'Val.ofInt ({operands[0] if operands else int(op[-1])})'
    else:
        return None
    pcs.append(pc)
    pc += size
    field = None
    if decoded[pc][0].startswith('GETFIELD'):
        op, a, size = decoded[pc]
        field = (value, a[0] if a else int(op[-1]))
        value = 'value'
        pcs.append(pc)
        pc += size
    if decoded[pc][:2] != ('RETURN', [req+1]):
        return None
    pcs.append(pc)
    return req, value, field, pcs


def normal(entry, words, decoded, spec):
    req, value, field, pcs = spec
    name, text, pin = certificate(entry, words, decoded, pcs)
    values = ' '.join(f'v{i}' for i in range(req+1))
    args = ' :: '.join(f'v{i}' for i in range(req+1))
    field_params = (f' (value : Val) (read : field? h {field[0]} {field[1]} = some value)' if field else '')
    proofs = []
    for mode in ['normal', 'over']:
        extra = str(req) if mode == 'normal' else f'extra + {req} + 1'
        suffix = '.code ret :: caller :: .int saved :: tail' if mode == 'normal' else 'tail'
        params = '(ret trap : Nat) (caller : Val) (saved : BitVec 63)' if mode == 'normal' else '(dest extra trap : Nat)'
        result = (f'⟨ret, {value}, tail, caller, saved.toNat, trap, h, w⟩' if mode == 'normal' else
                  f'⟨dest, {value}, tail, {value}, extra, trap, h, w⟩')
        enter = '' if mode == 'normal' else f' (code : field? h ({value}) 0 = some (.code dest))'
        initial = f'⟨{entry}, a, {args} :: {suffix}, env, {extra}, trap, h, w⟩'
        theorem = f'{name}_{mode}'
        after_extra = '0' if mode == 'normal' else 'extra + 1'
        retstate = f'⟨{pcs[-1]}, {value}, {args} :: {suffix}, env, {after_extra}, trap, h, w⟩'
        proof = '  rfl'
        if field:
            getpc = pcs[-2]
            op, operands, _ = decoded[getpc]
            instr = f'⟨.{op}, [{", ".join(map(str,operands))}]⟩'
            before = f'⟨{getpc}, {field[0]}, {args} :: {suffix}, env, {after_extra}, trap, h, w⟩'
            proof = (f'  change OCaml.Run.iter (decodedK P {name}.decode) 2 {before} = .ok {result}\n'
                     f'  have hs : stepI P {before} {instr} = .next {retstate} := by\n'
                     f'    change opt (field? h {field[0]} {field[1]}) _ = _\n'
                     '    rw [read]\n    rfl\n'
                     f'  rw [decoded_sym_step (decode := {name}.decode) (n := 1) rfl hs]\n'
                     '  rfl')
        if mode == 'over':
            last = (f'  change OCaml.Run.iter (decodedK P {name}.decode) 1 {retstate} = .ok {result}\n'
                    f'  have hr : stepI P {retstate} ⟨.RETURN, [{req+1}]⟩ = .next {result} := by\n'
                    f'    change enter {retstate} tail extra = _\n'
                    '    simp only [enter, code, opt]\n'
                    f'  rw [decoded_sym_step (decode := {name}.decode) (n := 0) rfl hr]\n'
                    '  rfl')
            proof = proof[:-5] + last if field else last
        text += f'''
theorem {theorem} (P : Prog) (pin : {pin})
    (a env {values} : Val) {params} (h : Heap) (w : World) (tail : List Val){field_params}{enter} :
    ApplicationSummary P {entry} (EntryShape {initial})
      (fun _ t => t = {result}) := by
  apply application_of_run (initial := {initial}) (final := {result}) (n := {len(pcs)})
  apply {name}.run P pin
{proof}
'''
        proofs.append(theorem)
    return text, proofs


def under(entry, words, decoded):
    req = decoded[entry][1][0]
    name, text, pin = certificate(entry, words, decoded, [entry])
    text += f'''
theorem {name}_under (P : Prog) (pin : {pin})
    (ret : Nat) (a env caller : Val) (extra trap : Nat) (saved : BitVec 63)
    (h : Heap) (w : World) (args tail : List Val)
    (arity : extra < {req}) (count : args.length = 1 + extra) :
    ApplicationSummary P {entry}
      (EntryShape ⟨{entry}, a, args ++ .code ret :: caller :: .int saved :: tail,
        env, extra, trap, h, w⟩)
      (fun _ t => t = ⟨ret, .ptr h.objs.length 0, tail, caller, saved.toNat, trap,
        (h.alloc (.block closureTag (.code {entry-1} :: Val.ofInt 2 :: env :: args))).1, w⟩) :=
  certified_under P {name} pin {entry} {req} ret a env caller extra trap saved h w args tail
    rfl arity count (by decide)
'''
    return text, [f'{name}_under']


def graph(entry, decoded):
    todo, seen, calls, loops = [entry], set(), [], []
    while todo:
        pc = todo.pop()
        if pc in seen: continue
        seen.add(pc)
        op, args, size = decoded[pc]
        edges = []
        if op.startswith(('APPLY', 'APPTERM')):
            # Source bytecode is higher-order; no unsound direct-call guesses.
            calls.append({'pc': pc, 'kind': 'tail' if op.startswith('APPTERM') else 'call',
                          'target': None})
            if op.startswith('APPLY'): edges.append(pc+size)
        elif op in {'RETURN', 'STOP', 'RAISE', 'RERAISE', 'RAISE_NOTRACE'}:
            pass
        elif op == 'BRANCH': edges.append(pc+1+args[0])
        elif op in {'BRANCHIF', 'BRANCHIFNOT', 'PUSHTRAP'}:
            edges.extend([pc+size, pc+1+args[0]])
        elif op in {'BEQ','BNEQ','BLTINT','BLEINT','BGTINT','BGEINT','BULTINT','BUGEINT'}:
            edges.extend([pc+size, pc+2+args[1]])
        elif op == 'SWITCH': edges.extend(pc+2+off for off in args[1:])
        else: edges.append(pc+size)
        for target in edges:
            if target <= pc: loops.append({'from': pc, 'to': target})
            if target in decoded: todo.append(target)
    return {'reachable_instructions': len(seen), 'calls': calls, 'back_edges': loops}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    exe = ROOT/'vendor/ocaml-4.14.4/boot/ocamlc'
    words, decoded, units, entries, targets = inputs(exe, DEFAULT_DUMP)
    artifacts, shards, functions, counts = {}, {}, {}, Counter()
    groups = []
    for entry in sorted(entries):
        spec = shape(entry, decoded)
        info = graph(entry, decoded)
        info['arity'] = 1 + (decoded[entry][1][0] if decoded[entry][0]=='GRAB' else 0)
        info['normal_generated'] = spec is not None
        info['over_generated'] = spec is not None
        info['under_generated'] = decoded[entry][0] == 'GRAB'
        functions[str(entry)] = info
        counts['functions'] += 1
        for kind in ['normal', 'over', 'under']:
            counts[kind] += info[f'{kind}_generated']
        if spec:
            text, proofs = normal(entry, words, decoded, spec)
            # The arity prefix uses the same certificate as the normal body;
            # under generation below gets a separate namespace to avoid names.
            groups.append((entry, 'Full', text, proofs))
        if info['under_generated']:
            text, proofs = under(entry, words, decoded)
            groups.append((entry, 'Partial', text, proofs))
    for i in range(0, len(groups), 128):
        name = f'F{i//128:03d}'
        lines = ['-- GENERATED by scripts/gen_bc_functions.py. Do not edit.',
                 'import OCaml.Logic.Function', f'namespace OCaml.Programs.Generated.Functions.{name}',
                 'open OCaml.Bytecode']
        proofs = []
        for entry, space, text, names in groups[i:i+128]:
            lines += [f'namespace {space}', text, f'end {space}']
            proofs.extend(f'OCaml.Programs.Generated.Functions.{name}.{space}.{n}' for n in names)
        lines += [f'end OCaml.Programs.Generated.Functions.{name}', '']
        text = '\n'.join(lines)
        artifacts[DEST/f'{name}.lean'] = text
        artifacts[DEST/f'{name}Audit.lean'] = '\n'.join([
            '-- GENERATED by scripts/gen_bc_functions.py. Do not edit.',
            f'import OCaml.Programs.Generated.Functions.{name}',
            *[f'#print axioms {n}' for n in proofs], ''])
        shards[name] = {'instructions': 0, 'blocks': len(proofs), 'theorems': proofs, 'source_sha256': hashlib.sha256(text.encode()).hexdigest()}
    manifest = {'generator':'scripts/gen_bc_functions.py', 'counts':dict(counts),
                'executable_sha256': hashlib.sha256(exe.read_bytes()).hexdigest(),
                'functions': functions, 'shards': shards,
                'scope': 'All closure entries. Normal/over: projection, constant, single field. '
                         'Under: all GRAB entries. Higher-order call edges unresolved; '
                         'normal summary gaps have no generated proof.'}
    artifacts[DEST/'manifest.json'] = json.dumps(manifest, indent=2)+'\n'
    for path, text in artifacts.items():
        if args.check:
            if not path.exists() or path.read_text()!=text: raise SystemExit(f'drift: {path}')
        else:
            path.parent.mkdir(parents=True,exist_ok=True)
            if not path.exists() or path.read_text()!=text: path.write_text(text)
    print(dict(counts))

if __name__=='__main__': main()
