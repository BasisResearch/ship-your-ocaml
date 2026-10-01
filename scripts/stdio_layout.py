"""Validated instruction and literal relocation for the preserved stdio templates."""
import json
from census import ROOT, disasm, symbols, sections, read_mem
from retarget_allocator_specs import units


def layout():
    old = json.loads((ROOT/'experiments/syi/stdio-template/layout.json').read_text())
    elf = ROOT/'c/ocamlrun-riscv-htif.elf'
    new, syms, secs = disasm(elf), symbols(elf), sections(elf)
    oldsecs = {n: (a, bytes.fromhex(b)) for n, (a,b) in old['sections'].items()}
    pcs, literals, expansions = {}, {}, {}
    def put(a,b):
        assert a not in literals or literals[a] == b, (hex(a),hex(b),literals.get(a))
        literals[a] = b
    def canon(k):
        return (*k[:3], 'literal') if len(k)==4 and isinstance(k[3],int) else k
    for name, fn in old['functions'].items():
        aa, bb = units(fn['insts'],old['symbols']), units(new[name]['insts'],syms)
        assert len(aa)==len(bb), name
        for (ak,ap),(bk,bp) in zip(aa,bb):
            assert canon(ak)==canon(bk), (name,ap,bp,ak,bk)
            if len(ak)==4 and isinstance(ak[3],int): put(ak[3],bk[3])
            if len(ap)==len(bp): pcs.update(zip(ap,bp))
            else:
                assert len(ap)==1 and len(bp)==2
                pcs[ap[0]]=bp[0]; expansions[ap[0]]=bp
        pcs[fn['insts'][-1][0]+4]=new[name]['insts'][-1][0]+4
    # Initialized object pointer fields expose literals such as the locale decimal point.
    for name,(a,z) in old['symbols'].items():
        if name not in syms or z==0 or syms[name][1]!=z: continue
        b=syms[name][0]
        x,y=read_mem(oldsecs,a,z),read_mem(secs,b,z)
        if x is None or y is None: continue
        for i in range(0,z-7,8):
            u,v=int.from_bytes(x[i:i+8],'little'),int.from_bytes(y[i:i+8],'little')
            if 0x80000000<=u<0x90000000 and 0x80000000<=v<0x90000000: put(u,v)
    def relocate(a):
        if a in pcs:return pcs[a]
        if a-a%4 in pcs:return pcs[a-a%4]+a%4
        if a in literals:return literals[a]
        exact=[n for n,(x,z) in old['symbols'].items() if x==a and n in syms]
        if exact:
            exact.sort(key=lambda n:(old['symbols'][n][1]==0,n))
            return syms[exact[0]][0]
        owners=[n for n,(x,z) in old['symbols'].items() if x<a<=x+z and n in syms]
        if owners:
            owners.sort(key=lambda n:old['symbols'][n][1])
            n=owners[0];return syms[n][0]+a-old['symbols'][n][0]
        for x,y in literals.items():
            if x<a<x+256:
                u,v=read_mem(oldsecs,x,a-x+1),read_mem(secs,y,a-x+1)
                if u is not None and u==v:return y+a-x
        if a in (0x80000000,0x87800000,0x88000000):return a
        raise ValueError(f'unmapped stdio address {a:#x}')
    base,size=old['conversion_table']; fresh=relocate(base)
    table_old,table_new=read_mem(oldsecs,base,size),read_mem(secs,fresh,size)
    offsets={}
    for i in range(0,size,4):
        u=int.from_bytes(table_old[i:i+4],'little',signed=True)
        v=int.from_bytes(table_new[i:i+4],'little',signed=True)
        assert relocate(base+u)==fresh+v,(i,u,v)
        offsets[u%(1<<64)]=v%(1<<64)
        for j in range(4):put(base+i+j,fresh+i+j)
    return old,new,syms,secs,relocate,expansions,offsets

if __name__=='__main__':
    old,new,syms,secs,relocate,expansions,offsets=layout()
    print(f'Stdio: {len(old["functions"])} functions, {len(expansions)} GP expansions; all 91 conversion-table targets validated')
