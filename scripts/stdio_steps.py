"""Re-emit symbolic step templates using freshly decoded instruction fields."""
import re
from syi.rv_steps import fields


def retarget_steps(source, old,new,syms,relocate,expansions):
    ow={i[0]:i[1] for f in old['functions'].values() for i in f['insts']}
    nw={i[0]:i[1] for f in new.values() for i in f['insts']}
    def site(s,pc):
        w=ow[pc]; q=relocate(pc); v=nw[q]
        a,b=fields(w),fields(v)
        if pc in expansions:
            q2=expansions[pc][1]; b2=fields(nw[q2])
            assert b['rd']==b2['rd'] and b2['rs1']==b['rd']
            target=q+b['immU']+b2['immI']
            # The composite segment consumes the AUIPC temporary internally.
            gp=old['symbols']['__global_pointer$'][0]
            pat=rf'\(0x{gp:x}#64\) \+ sign_extend \(m := 64\) \(0x{a["immI"]%4096:03x}#12\)'
            expr=f'((FRESHx{q:x}#64) + (sign_extend (m := 64) ((0x{v>>12:05x}#20) +++ (0x000#12)))) + sign_extend (m := 64) (0x{b2["immI"]%4096:03x}#12)'
            s=re.sub(pat, expr,s)
            s=s.replace(f'mkLine 0x{pc:x}#64 0x{w:08x}#32',
                        f'mkLine 0x{q:x}#64 0x{v:08x}#32, mkLine 0x{q2:x}#64 0x{nw[q2]:08x}#32')
            s=s.replace('[] 0 rfl', '[] 1 rfl')
            # These literals are fresh already; keep them out of relocation below.
            s=s.replace(f'0x{q:x}',f'FRESHx{q:x}').replace(f'0x{q2:x}',f'FRESHx{q2:x}').replace(f'0x{target:x}',f'FRESHx{target:x}')
        else:
            replacements={(w,32):v}
            for width,key in [(12,'immI'),(13,'immB'),(21,'immJ')]:
                if (width==12 and a['op'] in (3,0x13,0x67)) or (width==13 and a['op']==0x63) or (width==21 and a['op']==0x6f):
                    replacements[(a[key]%(1<<width),width)]=b[key]%(1<<width)
            if a['op']==0x17:replacements[(w>>12,20)]=v>>12
            # Bytes only appear in explicit observation lemmas and branch encodings.
            oldbs=[(w>>(8*i))&255 for i in range(4)];newbs=[(v>>(8*i))&255 for i in range(4)]
            for i in range(4):
                s=s.replace(f'(0x{pc+i:x}, .discard, 0x{oldbs[i]:02x}#8)',f'(0x{pc+i:x}, .discard, 0x{newbs[i]:02x}#8)')
            for sep in [', ',') (']:
                x=sep.join(f'0x{c:02x}#8' for c in oldbs);y=sep.join(f'0x{c:02x}#8' for c in newbs)
                s=s.replace(x,y)
            def lit(m):
                x,k=int(m[1],16),int(m[2]);y=replacements.get((x,k),x)
                return f'0x{y:0{len(m[1])}x}#{k}'
            s=re.sub(r'0x([0-9a-f]+)#(12|13|20|21|32)\b',lit,s)
        def addr(m):
            x=int(m[1],16)
            if m[2] and m[2]!='#64':return m[0]
            return f'0x{relocate(x):x}' + (m[2] or '') if 0x80000000<=x<0x90000000 else m[0]
        s=re.sub(r'(0x[0-9a-f]+)(#[0-9]+)?',addr,s)
        s=re.sub(r'(?<=_)800[0-9a-f]{5}(?=\b|_)',lambda m:f'{relocate(int(m[0],16)):08x}',s)
        s=re.sub(r'FRESHx([0-9a-f]+)',r'0x\1',s)
        return s
    # Every definition/theorem refers to one machine site; retain generic prose.
    pattern=r'(?m)^(?:def nx[TF]?_|theorem (?:nt[A-Z]?_|jalxn_))([0-9a-f]{8})\b'
    matches=list(re.finditer(pattern,source));out=source[:matches[0].start()]
    for i,m in enumerate(matches):
        end=matches[i+1].start() if i+1<len(matches) else len(source)
        out+=site(source[m.start():end],int(m[1],16))
    return 'import Vsa.Sim.ChainFactsTac\n' + out
