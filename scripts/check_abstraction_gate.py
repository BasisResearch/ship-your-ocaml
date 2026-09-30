#!/usr/bin/env python3
"""The abstraction-discovery gate (the /abstraction-discovery skill's gate).

    python3 scripts/check_abstraction_gate.py

Reads abstractions/clusters.tsv (regenerated from abstractions/clusters.def
by scripts/abstraction_census.py; both are checked to agree) and, for each
cluster, the hand proofs dated after the cluster's last adoption (an
`adopted <iso-date> <round-file>` line under the cluster in clusters.def).
A cluster FAILS when it has at least N = 8 such proofs and the mean cost of
the last quarter is more than two thirds of the mean cost of the first
quarter (its per-case cost did not fall by a third). Exit 1 with
"run /abstraction-discovery" on any failure.
"""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
N = 8


def adoptions():
    out, cluster = {}, None
    for l in (ROOT / "abstractions/clusters.def").read_text().splitlines():
        l = l.split("#", 1)[0].strip()
        if l.startswith("cluster "):
            cluster = l.split()[1]
        elif l.startswith("adopted ") and cluster:
            out[cluster] = max(out.get(cluster, ""), l.split()[1])
    return out


def main():
    fresh = subprocess.run([sys.executable, str(ROOT / "scripts/abstraction_census.py")],
                           capture_output=True, text=True, check=True).stdout
    tsv = (ROOT / "abstractions/clusters.tsv").read_text()
    if fresh != tsv:
        print("gate: abstractions/clusters.tsv is stale — regenerate it with "
              "scripts/abstraction_census.py > abstractions/clusters.tsv")
        sys.exit(1)
    rows = [l.split("\t") for l in tsv.splitlines() if l and not l.startswith("#")]
    adopted = adoptions()
    failed = []
    for c in sorted({r[0] for r in rows}):
        costs = [int(r[2]) for r in rows if r[0] == c and r[1] > adopted.get(c, "")]
        if len(costs) < N:
            print(f"{c}: {len(costs)} hand proofs since last adoption (< {N}): ok")
            continue
        q = max(1, len(costs) // 4)
        first, last = sum(costs[:q]) / q, sum(costs[-q:]) / q
        ok = last <= first * 2 / 3
        print(f"{c}: {len(costs)} hand proofs, first-quarter mean {first:.1f} lines, "
              f"last-quarter mean {last:.1f}: {'ok (fell by a third)' if ok else 'FLAT'}")
        if not ok:
            failed.append(c)
    if failed:
        print(f"gate: cluster(s) {', '.join(failed)} reached {N} hand proofs without the per-case "
              f"cost falling by a third — run /abstraction-discovery")
        sys.exit(1)
    print("gate: OK")


if __name__ == "__main__":
    main()
