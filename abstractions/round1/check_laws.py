#!/usr/bin/env python3
"""Cheap counterexample search for the round-1 laws (ROUND-1.md §2).
L1: facts about the n-step closure of a deterministic step function, over
    random finite systems. L3: relocation invariance of the representation,
    over a Python mirror of valWord/ObjAt(block)/StackRepr/HeapRepr on random
    small heaps and random relocations (injective, and not)."""
import random
random.seed(20260930)

# ---------- L1 ----------
def l1_trial():
    n = random.randint(1, 8)
    # step: state -> ('next', s') | ('halt', r) | ('stuck',)
    f = {}
    for s in range(n):
        k = random.random()
        f[s] = ('next', random.randrange(n)) if k < .6 else (('halt', random.randrange(3)) if k < .85 else ('stuck',))
    def reachN(k, a):                      # the iterate (the law's right side)
        for _ in range(k):
            if f[a][0] != 'next': return None
            a = f[a][1]
        return a
    # relational n-step closure, computed independently as a set
    R = {(0, a, a) for a in range(n)}
    for k in range(1, 12):
        R |= {(k, a, f[b][1]) for (j, a, b) in list(R) if j == k-1 and f[b][0] == 'next'}
    bad = []
    for k in range(12):
        for a in range(n):
            succ = {b for (j, x, b) in R if j == k and x == a}
            it = reachN(k, a)
            if succ != ({it} if it is not None else set()): bad.append(('graph', k, a))
            # prefix: a (k+m)-run has a k-run
            for m in range(3):
                if any(j == k+m and x == a for (j, x, _) in R) and it is None: bad.append(('prefix', k, a))
    for a in range(n):
        halts = {(f[b][1]) for (j, x, b) in R if x == a and f[b][0] == 'halt'}
        if len(halts) > 1: bad.append(('halt-unique', a))
        diverges = all(reachN(k, a) is not None for k in range(n+2))
        if diverges and halts: bad.append(('halt-excludes-div', a))
        stuck = any(f[b][0] == 'stuck' for (j, x, b) in R if x == a)
        if not (diverges or halts or stuck): bad.append(('trichotomy', a))
    return bad

l1 = [b for _ in range(20000) for b in l1_trial()]
assert not l1, l1[:3]
print(f"L1: 20000 random systems, {len(l1)} counterexamples {l1[:3]}")

# ---------- L3 ----------
def val_word(phi, v):                     # valWord: ('int', n) | ('ptr', l, k) | ('code', pc)
    if v[0] == 'int': return ('w', 2*v[1]+1)
    if v[0] == 'code': return ('w', 10**6 + 4*v[1])
    a = phi.get(v[1]); return None if a is None else ('w', a + 8*v[2])

def trial(injective=True):
    L = random.randint(1, 5)
    heap = {l: [random.choice([('int', random.randint(0, 9)), ('ptr', random.randrange(L), 0), ('code', 3)])
                for _ in range(random.randint(1, 4))] for l in range(L)}
    addrs = random.sample(range(1, 50), L)
    phi = {l: 1000 + 64*addrs[l] for l in range(L)}
    mem = {}
    for l, fs in heap.items():
        mem[phi[l]-8] = ('hdr', len(fs))
        for i, v in enumerate(fs): mem[phi[l] + 8*i] = val_word(phi, v)
    # relocation μ on block addresses (copying collector)
    targets = random.sample(range(1, 50), L) if injective else [random.randint(1, 3) for _ in range(L)]
    mu = {phi[l]: 5000 + 64*targets[l] for l in range(L)}
    phi2 = {l: mu[a] for l, a in phi.items()}
    mem2 = {}
    for l, fs in heap.items():                            # the collector's copy
        mem2[mu[phi[l]]-8] = mem[phi[l]-8]
        for i, v in enumerate(fs): mem2[mu[phi[l]] + 8*i] = val_word(phi2, v)
    def heap_repr(ph, m):
        ok = all(m.get(ph[l]-8) == ('hdr', len(fs)) and
                 all(m.get(ph[l]+8*i) == val_word(ph, v) for i, v in enumerate(fs)) for l, fs in heap.items())
        disjoint = all(ph[l]+8*len(heap[l]) <= ph[l2]-8 or ph[l2]+8*len(heap[l2]) <= ph[l]-8
                       for l in heap for l2 in heap if l != l2)
        return ok and disjoint
    return heap_repr(phi, mem), heap_repr(phi2, mem2)

inj = [trial(True) for _ in range(20000)]
non = [trial(False) for _ in range(20000)]
assert all(not a or b for a, b in inj)
assert any(a and not b for a, b in non)
print(f"L3 (injective relocation): {sum(1 for a,b in inj if a and not b)} counterexamples in {sum(a for a,_ in inj)} valid starts")
print(f"L3 (relocation not injective): {sum(1 for a,b in non if a and not b)} counterexamples in {sum(a for a,_ in non)} valid starts  <- the law needs disjoint targets")

# ---------- L3' (round 2): the collector's real classifier and traversal ----------
# Round-2 agents R2-1 B/E and R2-4 #2 objected that L3 above relocates by VM
# sort over every pointer, while the minor GC (minor_gc.c) rewrites a word
# iff it is even and inside the young range (Is_block && Is_young), and
# visits only roots, the ref table and copied blocks. Mirror that here.
Y0, Y1 = 10000, 20000                      # young range; old space 1000..9999, copies go to 30000+
def gc_trial(forge, ref_complete):
    L = random.randint(1, 5)
    young = {l: random.random() < .6 for l in range(L)}
    def rnd_val():
        k = random.random()
        if k < .3: return ('int', random.randint(0, 9))
        if k < .6: return ('ptr', random.randrange(L), 0)
        if k < .8: return ('code', 3)
        # a raw word: forged => may be an even young-range word, else odd (an infix header 3072k+249)
        return ('raw', random.choice([Y0 + 8*random.randrange(40), 3072*random.randint(1, 3) + 249]) if forge
                       else 3072*random.randint(1, 3) + 249)
    heap = {l: [rnd_val() for _ in range(random.randint(1, 4))] for l in range(L)}
    stack = [rnd_val() for _ in range(random.randint(0, 3))]
    slots = random.sample(range(1, 40), L)
    phi = {l: (Y0 if young[l] else 1000) + 128*slots[l] for l in range(L)}
    def word(ph, v):
        if v[0] == 'int': return 2*v[1]+1
        if v[0] == 'code': return 10**6 + 4*v[1]
        if v[0] == 'raw': return v[1]
        return ph[v[1]] + 8*v[2]
    mem = {}
    for l, fs in heap.items():
        for i, v in enumerate(fs): mem[phi[l] + 8*i] = word(phi, v)
    stk = [word(phi, v) for v in stack]
    ref = {phi[l] + 8*i for l, fs in heap.items() if not young[l] for i, v in enumerate(fs)
           if v[0] == 'ptr' and young[v[1]] and (ref_complete or random.random() < .5)}
    # the collector: forward young blocks (live = all here), rewrite scanned even young words
    tgt = {phi[l]: 30000 + 128*i for i, l in enumerate(sorted(l for l in heap if young[l]))}
    def fwd(w):
        if w % 2 == 0 and Y0 <= w < Y1:
            base = max((b for b in tgt if b <= w), default=None)
            return tgt[base] + (w - base) if base is not None and w - base < 8*4 else w + 7  # dangling: garbage
        return w
    mem2 = dict(mem)
    for l, fs in heap.items():
        if young[l]:
            for i in range(len(fs)): mem2[tgt[phi[l]] + 8*i] = fwd(mem[phi[l] + 8*i])
        else:
            for i in range(len(fs)):
                a = phi[l] + 8*i
                if a in ref: mem2[a] = fwd(mem[a])
    stk2 = [fwd(w) for w in stk]
    phi2 = {l: tgt[phi[l]] if young[l] else phi[l] for l in heap}
    ok = all(mem2.get(phi2[l] + 8*i) == word(phi2, v) for l, fs in heap.items() for i, v in enumerate(fs)) \
        and stk2 == [word(phi2, v) for v in stack]
    return ok

for forge, refc, name in [(False, True, "no forged raw words, complete ref table"),
                          (True, True, "raw words may look young (no NoForgery)"),
                          (False, False, "incomplete ref table (no RememberedComplete)")]:
    r = [gc_trial(forge, refc) for _ in range(20000)]
    assert all(r) if not forge and refc else not all(r)
    print(f"L3' bit-true GC, {name}: {r.count(False)} counterexamples / 20000")

# ---------- L3' special tags: minor_gc.c:caml_oldify_one ----------
# A small executable transcription, including the zero-header forwarding
# marker, deferred field scanning, Forward_tag exceptions, and Infix_tag.
INFIX, FORWARD, LAZY, DOUBLE, NO_SCAN = 249, 250, 246, 253, 251

def oldify_special(memory, roots, flat_float=True, value_area=None):
    mem = dict(memory)
    todo = []
    next_addr = 30000
    def young(w):
        return w % 2 == 0 and Y0 <= w < Y1
    def tag(w):
        return mem[w - 8] % 256
    def alloc(size, kind):
        nonlocal next_addr
        a = next_addr
        next_addr += 8 * (size + 1)
        mem[a - 8] = size * 1024 + kind
        return a
    def oldify(v):
        if not young(v):
            return v
        hd = mem[v - 8]
        if hd == 0:
            return mem[v]
        kind, size = hd % 256, hd // 1024
        if kind == INFIX:
            offset = size * 8
            return oldify(v - offset) + offset
        if kind == FORWARD:
            f = mem[v]
            ft, vv = 0, True
            if f % 2 == 0:
                if young(f):
                    ft = tag(mem[f] if mem[f - 8] == 0 else f)
                else:
                    vv = f in value_area if value_area is not None else f - 8 in mem
                    if vv:
                        ft = tag(f)
            if vv and ft not in ({FORWARD, LAZY, DOUBLE} if flat_float else {FORWARD, LAZY}):
                return oldify(f)
        a = alloc(size, kind)
        fields = [mem[v + 8*i] for i in range(size)]
        mem[v - 8], mem[v] = 0, a
        if kind >= NO_SCAN:
            for i, f in enumerate(fields):
                mem[a + 8*i] = f
        elif size == 1:
            mem[a] = oldify(fields[0])
        else:
            # Deferred scanning is observationally the mopup queue; the C
            # stores the queue links in field 1 rather than a Python list.
            todo.append((a, fields))
        return a
    result = [oldify(v) for v in roots]
    while todo:
        a, fields = todo.pop()
        for i, f in enumerate(fields):
            mem[a + 8*i] = oldify(f)
    return result, mem

# Every listed exception is checked both before and after its target has
# already acquired the collector's zero-header forwarding marker.
special_cases = 0
for flat in (False, True):
    for target_tag in (0, LAZY, FORWARD, DOUBLE, NO_SCAN):
        for target_young in (False, True):
            for already in (False, True):
                a, b = Y0 + 8, (Y0 + 136 if target_young else 1032)
                mem = {a-8: 1024+FORWARD, a: b, b-8: 1024+target_tag, b: 85}
                rs, after = oldify_special(mem, ([b] if already else []) + [a], flat)
                copied = target_tag in ({FORWARD, LAZY, DOUBLE} if flat else {FORWARD, LAZY})
                if copied:
                    assert after[rs[-1]-8] % 256 == FORWARD
                else:
                    assert rs[-1] != a
                    assert after.get(rs[-1]-8, 0) % 256 != FORWARD
                special_cases += 1
# Immediate payload: a strict placement would still demand a Forward header
# immediately before the new address. The real short-circuit returns 85.
a = Y0 + 8
rs, after = oldify_special({a-8: 1024+FORWARD, a: 85}, [a])
assert rs == [85] and after.get(85-8, 0) != 1024+FORWARD
# Outside the value area: preserve the Forward block, even though f is even.
rs, after = oldify_special({a-8: 1024+FORWARD, a: 2000000}, [a])
assert after[rs[0]-8] % 256 == FORWARD and after[rs[0]] == 2000000
print(f"L3' Forward_tag: {special_cases + 2} cases pass; strict ObjAt preservation has a counterexample (Forward -> int 42)")

# Interior closure pointers require a real Infix header at v[-1]. Include
# both root orders, so the base may already have a zero header.
for offset in range(2, 8):
    a = Y0 + 8
    fs = [1000000, 3] + [1] * offset
    fs[offset-1] = offset * 1024 + INFIX
    mem = {a-8: len(fs)*1024 + 247, **{a+8*i: f for i, f in enumerate(fs)}}
    for roots in ([a, a+8*offset], [a+8*offset, a]):
        rs, after = oldify_special(mem, roots)
        base = rs[0] if roots[0] == a else rs[1]
        interior = rs[1] if roots[0] == a else rs[0]
        assert interior == base + 8*offset
        assert after[interior-8] == offset*1024 + INFIX
# Without Infix_tag a payload word is misread as an ordinary block header.
mem = {a-8: 3*1024+247, a: 1000000, a+8: 1024, a+16: 85}
rs, after = oldify_special(mem, [a, a+16])
assert rs[1] != rs[0] + 16
print("L3' Infix_tag: 12 affine cases pass; missing Infix header has a counterexample")
