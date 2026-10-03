"""Shared compact byte-view emitter with sparse packed pages and balanced lookup."""


def emit_packed_bytes(out, name, body):
    pages = [int.from_bytes(body[i:i+256], 'little') for i in range(0, len(body), 256)]
    assert pages
    for i, value in enumerate(pages):
        if value:
            out.append(f'def {name}Page{i} : Nat := {value:#x}')

    def tree(lo, hi):
        if hi-lo == 1:
            return f'{name}Page{lo}' if pages[lo] else '0'
        mid = (lo+hi)//2
        left, right = tree(lo, mid), tree(mid, hi)
        return left if left == right else f'(if page < {mid} then {left} else {right})'

    out += [f'def {name}Byte (off : Nat) : BitVec 8 :=',
            '  let page := off / 256', f'  let packed := {tree(0, len(pages))}',
            '  BitVec.ofNat 8 (packed >>> (8 * (off % 256)))', '']
