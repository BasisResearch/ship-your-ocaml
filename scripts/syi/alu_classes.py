"""Shared descriptors for additional RV64I ALU site classes.

The classifier, site emitter, and segment def-use/value emitter share these
operand shapes. Execute helpers are the existing ExecuteAlu characterizations;
generated Lean checks both the decoded instruction and the computed value.
"""
SHIFT = {'slli': 'shift_bits_left', 'srli': 'shift_bits_right',
         'srai': 'shift_bits_right_arith', 'slliw': 'shift_bits_left',
         'srliw': 'shift_bits_right', 'sraiw': 'shift_bits_right_arith'}
IMM = {'andi': '&&&', 'ori': '|||', 'xori': '^^^'}
REG = {'alu_and': '&&&', 'alu_or': '|||', 'alu_xor': '^^^',
       'sll': 'shift_bits_left', 'srl': 'shift_bits_right', 'sra': 'shift_bits_right_arith'}
UPPER = {'lui', 'auipc'}
CLASSES = set(SHIFT) | set(IMM) | set(REG) | {'addw'} | UPPER


def classify(word):
    """Return a new supported class and operands, or None (including reserved encodings)."""
    op, f3, f7, f6 = word & 127, (word >> 12) & 7, word >> 25, word >> 26
    rd, r1, r2 = ((word >> n) & 31 for n in (7, 15, 20))
    if rd == 0:
        return None
    if op in (0x17, 0x37):
        return ('auipc' if op == 0x17 else 'lui'), [rd, f'{word >> 12:05x}']
    if op == 0x13 and f3 in (4, 6, 7):
        return {4: 'xori', 6: 'ori', 7: 'andi'}[f3], [rd, r1, f'{word >> 20:03x}']
    if op in (0x13, 0x1b) and f3 in (1, 5):
        wide = op == 0x13
        top = f6 if wide else f7
        arithmetic = 0x10 if wide else 0x20
        if (f3 == 1 and top != 0) or (f3 == 5 and top not in (0, arithmetic)):
            return None
        name = 'slli' if f3 == 1 else ('srai' if top else 'srli')
        name += '' if wide else 'w'
        return name, [rd, r1, f'{(word >> 20) & (63 if wide else 31):02x}']
    if op == 0x33:
        name = {(7, 0): 'alu_and', (6, 0): 'alu_or', (4, 0): 'alu_xor',
                (1, 0): 'sll', (5, 0): 'srl', (5, 32): 'sra'}.get((f3, f7))
        if name:
            return name, [rd, r1, r2]
    if op == 0x3b and (f3, f7) == (0, 0):
        return 'addw', [rd, r1, r2]
    return None


def reads(cls, fields):
    if cls in UPPER:
        return []
    return list(dict.fromkeys(int(r) for r in fields[1:3 if cls in REG or cls == 'addw' else 2]
                              if int(r) != 0))


def value(cls, fields, var=lambda r: f'v{r}' if int(r) else '(0#64)', pc=None):
    if cls in UPPER:
        offset = f'(sign_extend (m := 64) ((0x{int(fields[1], 16):05x}#20) +++ 0x000#12))'
        if cls == 'lui':
            return offset
        if pc is None:
            raise ValueError('AUIPC needs the actual instruction PC')
        return f'({pc} + {offset})'
    left = var(fields[1])
    if cls in SHIFT:
        width = 5 if cls.endswith('w') else 6
        shamt = f'(0x{int(fields[2], 16):02x}#{width})'
        if width == 5:
            return f'(sign_extend (m := 64) ({SHIFT[cls]} (Sail.BitVec.extractLsb {left} 31 0) {shamt}))'
        return f'({SHIFT[cls]} {left} (Sail.BitVec.extractLsb {shamt} 5 0))'
    if cls in IMM:
        return f'({left} {IMM[cls]} sign_extend (m := 64) (0x{int(fields[2], 16):03x}#12))'
    right = var(fields[2])
    if cls == 'addw':
        return f'(sign_extend (m := 64) ((Sail.BitVec.extractLsb {left} 31 0) + (Sail.BitVec.extractLsb {right} 31 0)))'
    if cls in ('sll', 'srl', 'sra'):
        return f'({REG[cls]} {left} (Sail.BitVec.extractLsb {right} 5 0))'
    return f'({left} {REG[cls]} {right})'


def shape(cls, fields):
    if cls in UPPER:
        rd, imm = int(fields[0]), int(fields[1], 16)
        operand, reg = f'(0x{imm:05x}#20)', f'(regidx.Regidx 0x{rd:02x}#5)'
        return (f'instruction.UTYPE ({operand}, {reg}, uop.{cls.upper()})',
                f'execute_utype_{cls}_char', f'{operand} {reg}')
    rd, r1 = map(int, fields[:2])
    ri = lambda r: f'(regidx.Regidx 0x{r:02x}#5)'
    if cls in SHIFT or cls in IMM:
        width = 12 if cls in IMM else 5 if cls.endswith('w') else 6
        operand = f'(0x{int(fields[2], 16):03x}#{width})'
        kind = 'ITYPE' if cls in IMM else 'SHIFTIWOP' if width == 5 else 'SHIFTIOP'
        enum = 'iop' if cls in IMM else 'sopw' if width == 5 else 'sop'
        args = f'{operand} {ri(r1)} {ri(rd)}'
        instr_args = f'{operand}, {ri(r1)}, {ri(rd)}'
    else:
        r2 = int(fields[2])
        kind, enum = ('RTYPEW', 'ropw') if cls == 'addw' else ('RTYPE', 'rop')
        args = f'{ri(r2)} {ri(r1)} {ri(rd)}'
        instr_args = f'{ri(r2)}, {ri(r1)}, {ri(rd)}'
    name = cls.removeprefix('alu_')
    return f'instruction.{kind} ({instr_args}, {enum}.{name.upper()})', f'execute_{kind.lower()}_{name}_char', args
