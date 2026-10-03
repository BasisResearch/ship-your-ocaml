"""Shared emission of total-read certificates from a checked packed store log."""

def emit_read(out, name, expr, value, width=8):
    op = {1: 'byte', 4: 'word32', 8: 'word'}[width]
    out.extend([
        f'theorem read_{name} (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem initial log)) :',
        f'    {op} c ({expr}) = {value:#x}#{width*8} := by',
        f'  unfold {op}',
        f'  rw [bytesT_memEqv memory, observedMem_bytes_stored logOk (a := {expr}) (w := {width}) (by decide +kernel)]',
        '  decide +kernel', '',
    ])
    return f'read_{name} memory'


def finite_cases(terms):
    """A dependent finite-index proof, without tactic case enumeration."""
    term = 'fun i => Fin.elim0 i'
    for proof in reversed(terms):
        term = f'Fin.cases ({proof}) ({term})'
    return term


def emit_finite_family(out, name, proofs, goal, start=0, chunk=24, upper=None):
    """Bound the depth of a dependent finite family, then assemble its range theorem.

    goal(index_expression) is a Lean proposition; each proof supplies that
    proposition at its literal index. No larger Lean recursion budget is needed.
    """
    end = start + len(proofs)
    for lo in range(start, end, chunk):
        hi = min(lo + chunk, end)
        out.extend([f'theorem {name}_{lo}_{hi} :',
                    f'    ∀ j : Fin {hi-lo}, {goal(f"({lo} + j.val)")} :=',
                    '  ' + finite_cases(proofs[lo-start:hi-start]), ''])
    out.extend([f'theorem {name} (i : Nat) (lo : {start} ≤ i) (hi : i < {upper or end}) :',
                f'    {goal("i")} := by', f'  have bound : i < {end} := hi'])
    for lo in range(start, end, chunk):
        hi = min(lo + chunk, end)
        out.extend([f'  by_cases h{hi} : i < {hi}',
                    f'  · have low : {lo} ≤ i := by omega',
                    f'    have index : i - {lo} < {hi-lo} := by omega',
                    f"    simpa only [Nat.add_sub_cancel' low] using {name}_{lo}_{hi} ⟨i - {lo}, index⟩"])
    out.extend(['  omega', ''])
