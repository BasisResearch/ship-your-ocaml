"""Bounded certificates for symbolic store logs, checked against instruction records."""

def emit_log_chunks(E, name, instrs, keys, literal, lib, chunk_size=5, register_certificate=False):
    regs = {k:f'R {k}' for k in keys}
    order = list(keys)
    consumed = 0
    chunks = []
    def lit(n):
        return f'{n % (1 << 64)}#64'
    def val(k):
        return '0#64' if k == 0 else regs[k]
    def add(x,n):
        return f'({x} + {lit(n)})'
    def write(k,v):
        if k == 0: return
        regs[k] = v
        if k in order: order.remove(k)
        order.insert(0,k)
    def render_regs():
        return '['+', '.join(f'({k}, {regs[k]})' for k in order)+']'
    def remaining(n):
        return 'loads'+'.tail'*n
    simp = ('runGM, wlogM, ldsRunM, wentryM, widthOfM, stepGM, stepLdsM, '
            'wvalM, eaddrM, srcVal, lookupG, eraseG, imm20Of, '
            'Functions.sign_extend, Sail.BitVec.signExtend, List.head?_eq_getElem?')
    if any(ins.word & 127 == 0x13 and (ins.word >> 12) & 7 in (1,5) for ins in instrs):
        simp += ', shamtOf, Sail.BitVec.extractLsb, Sail.shift_bits_left, Sail.shift_bits_right'
    for idx,start in enumerate(range(0,len(instrs),chunk_size)):
        body=instrs[start:start+chunk_size]
        part=f'{name}_piece{idx}'
        initial=render_regs()
        load_start=consumed
        log=[]
        for ins in body:
            w=ins.word; op=w&127; rd=(w>>7)&31; rs1=(w>>15)&31; rs2=(w>>20)&31
            if op==0x13 and ((w>>12)&7)==0:
                write(rd,add(val(rs1),lib.sext(w>>20,12)))
            elif op==0x13 and ((w>>12)&7) in (1,5):
                kind = 'left' if ((w>>12)&7)==1 else 'right'
                assert w >> 26 == 0
                write(rd,f'Sail.shift_bits_{kind} ({val(rs1)}) ({(w >> 20) & 63}#6)')
            elif op==0x33 and ((w>>12)&7)==0 and w >> 25 in (0,0x20):
                op_symbol = '+' if w >> 25 == 0 else '-'
                write(rd,f'({val(rs1)} {op_symbol} {val(rs2)})')
            elif op==0x17:
                write(rd,add(lit(ins.addr),lib.sext(w & 0xfffff000,32)))
            elif op==3 and ((w>>12)&7)==3:
                write(rd,f'bytesVal .ld (loads.getD {consumed} [])')
                consumed+=1
            elif op==0x23 and ((w>>12)&7)==3:
                imm=lib.sext(((w>>25)<<5)|((w>>7)&31),12)
                log.append(f'(({add(val(rs1),imm)}).toNat, 8, {val(rs2)})')
            else:
                raise ValueError(f'unsupported symbolic chunk instruction {ins}')
        final=render_regs()
        E(f'def {part} : List MInstr := [', ',\n'.join('  '+literal(i.addr,i.word) for i in body), ']',
          f'def {part}_input (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) : GRegs := {initial}',
          f'def {part}_output (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) : GRegs := {final}',
          f'def {part}_log (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) : List WEntry := ['+', '.join(log)+']')
        for what,lhs,rhs in [
            ('regs',f'runGM {part} ({part}_input R loads) ({remaining(load_start)})',f'{part}_output R loads'),
            ('loads',f'ldsRunM {part} ({remaining(load_start)})',remaining(consumed)),
            ('stores',f'wlogM {part} ({part}_input R loads) ({remaining(load_start)})',f'{part}_log R loads')]:
            E(f'theorem {part}_{what} (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) :',
              f'    {lhs} = {rhs} := by',
              (('  simp only ['+part+', '+part+'_input, '+part+'_log, wlogM, wentryM, widthOfM, stepGM, stepLdsM, wvalM, eaddrM, srcVal, lookupG, eraseG, Nat.reduceEqDiff, ite_true, ite_false, Option.getD_some, List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_tail, List.getD_eq_getElem?_getD, Nat.reduceAdd]\n  all_goals rfl') if what == 'stores' and name == 'finish' else '  rfl' if what == 'stores' else f'  simp [{part}, {part}_input, {part}_output, {part}_log, {simp}]'))
        E('')
        chunks.append(part)
    def app(parts):
        return parts[0] if len(parts)==1 else '('+parts[0]+' ++ '+app(parts[1:])+')'
    E(f'theorem {name}_log_chunks (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) :',
      f'    wlogM {name}_body ({name}_input R) loads = '+app([f'{p}_log R loads' for p in chunks])+' := by',
      '  change wlogM '+app(chunks)+f' ({chunks[0]}_input R loads) loads = _')
    for i,p in enumerate(chunks[:-1]):
        E(f'  rw [wlogM_append, {p}_regs R loads, {p}_loads R loads, {p}_stores R loads]')
        rest = 'wlogM '+app(chunks[i+1:])+f' ({chunks[i+1]}_input R loads) ({remaining(sum(1 for ins in instrs[:(i+1)*chunk_size] if ins.word&127==3))})'
        E('  change '+app([q+'_log R loads' for q in chunks[:i+1]]+[rest])+' = _')
    E(f'  rw [{chunks[-1]}_stores R loads]', '')

    if register_certificate:
        E(f'theorem {name}_registers_chunks (R : Nat → BitVec 64) (loads : List (List (BitVec 8))) :',
          f'    runGM {name}_body ({name}_input R) loads = {chunks[-1]}_output R loads := by',
          '  change runGM '+app(chunks)+f' ({chunks[0]}_input R loads) loads = _')
        for i,p in enumerate(chunks[:-1]):
            E(f'  rw [runGM_append, {p}_regs R loads, {p}_loads R loads]')
            consumed_before = sum(1 for ins in instrs[:(i+1)*chunk_size] if ins.word&127==3)
            E('  change runGM '+app(chunks[i+1:])+f' ({chunks[i+1]}_input R loads) ({remaining(consumed_before)}) = _')
        E(f'  rw [{chunks[-1]}_regs R loads]', '')
    return chunks
