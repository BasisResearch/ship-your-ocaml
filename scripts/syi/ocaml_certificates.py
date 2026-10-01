"""Shared fixed-image projections for generated OCaml function certificates."""

def emit_loaded(E, fn, ins, pred, text_base, theorem='loaded'):
    E(f'theorem {theorem} {{c : Config}} (h : ExecutableImage c) : {pred} c.σ.mem := by',
      '  unfold '+pred+' '+ ' '.join('Vsa.Sim.Code.'+fn+'Chunk'+str(i) for i in range((len(ins)+15)//16)),
      "  repeat' apply And.intro")
    for a,w,_,_ in ins:
        for k in range(4):
            off=a+k-text_base
            E(f'  · have hb := h.text {off} (by decide)',
              f'    have he : Image.textByte {off} = 0x{(w>>(8*k))&255:02x}#8 := by decide +kernel',
              '    rw [he] at hb','    exact hb')
