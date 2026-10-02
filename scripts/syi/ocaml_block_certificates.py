"""Common generated block certificates with scalar access plans."""

def emit_block(E, fn, b, name, keys, lib, literal):
    term = None if b.kind == 'jal' else lib.decode_terminator(b.term, taken=False)['record']
    term_expr = 'none' if term is None else 'some ' + name + '_term'
    keylist = str(keys)
    E(f'def {name}_body : List MInstr := [', ',\n'.join('  ' + literal(i.addr, i.word) for i in b.instrs), ']',
      *([f'def {name}_term : TInstr := {term}'] if term else []),
      f'def {name}_blocks : List BBlock := [{{ body := {name}_body, term := {term_expr} }}]',
      f'def {name}_input (R : Nat → BitVec 64) : GRegs := [' + ', '.join(f'({k}, R {k})' for k in keys) + ']', '')
    E(f'theorem {name}_code {{c : Config}} (image : ExecutableImage c) : CodeFacts c.σ.mem {name}_body := by',
      '  have hc := loaded image', f'  simp only [CodeFacts, {name}_body]',
      f'  chain_facts hc with "Vsa.Sim.Code.{fn}_at_"', '',
      f'theorem {name}_shape : ChainOK 0x{b.start:08x}#64 {keylist} {name}_blocks := by',
      f'  simp only [ChainOK, BBlockOK, {name}_blocks, {name}_body, '+(name+'_term, ' if term else '')+'BlockOKM]',
      "  repeat' apply And.intro", '  all_goals decide', '',
      f'theorem {name}_summary (c : Config) (ra : BitVec 64) (R : Nat → BitVec 64)',
      '    (loads : List (List (BitVec 8))) (h : LeafInput ra c)',
      f'    (regs : GHolds c.σ ({name}_input R))',
      f'    (access : AccessPlan c.σ.mem ({name}_input R) loads {name}_body)',
      f'    (control : TermFactsO (runGM {name}_body ({name}_input R) loads) ({term_expr})) :',
      f'    FnSummary 0x{b.start:08x}#64 (fun d => d = c)',
      f'      (BlockPost {name}_blocks 0x{b.start:08x}#64 ({name}_input R) loads c) := by',
      f'  apply block_summary {name}_blocks _ _ _ c',
      f'  refine ⟨h.good, h.minstret, regs, ?_, ?_, {name}_shape, h.tick⟩',
      f'  · change KeysOK {keylist}; decide',
      f'  · apply singleton_chain_facts (accessPlan_facts ({name}_code h.image) access) ?_ control',
      *(['    have hc := loaded h.image', f'    chain_facts hc with "Vsa.Sim.Code.{fn}_at_"'] if term else ['    trivial']), '')
