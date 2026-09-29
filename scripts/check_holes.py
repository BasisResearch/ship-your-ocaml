#!/usr/bin/env python3
"""No holes in the Lean sources of this repository's own tree (OCaml/,
OCaml.lean, RunBc.lean): after stripping comments and string literals, no
`sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `ofReduceBool` or
`trustCompiler` token. Exit 1 on any hit."""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BAD = re.compile(r"\b(sorry|admit|native_decide|ofReduceBool|trustCompiler)\b|^\s*(axiom|opaque)\s", re.M)


def strip(src: str) -> str:
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""'); i = j + 1; continue
        out.append(src[i]); i += 1
    return "".join(out)


files = (sorted((ROOT / "OCaml").rglob("*.lean")) + sorted((ROOT / "tcb").rglob("*.lean"))
         + [ROOT / "OCaml.lean", ROOT / "RunBc.lean"])
hits = []
for f in files:
    code = strip(f.read_text())
    for m in BAD.finditer(code):
        line = code.count("\n", 0, m.start()) + 1
        hits.append(f"{f.relative_to(ROOT)}:{line}: {m.group(0).strip()}")
if hits:
    print("\n".join(hits)); sys.exit(1)
print(f"no holes ({len(files)} files)")
