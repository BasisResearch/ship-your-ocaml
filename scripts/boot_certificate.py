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
