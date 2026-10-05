#!/usr/bin/env python3
"""Report generated compiler proof coverage without counting open contracts."""
import argparse
import json
from gen_bc_rules import ROOT, OUT


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    blocks=json.loads((OUT/'All/manifest.json').read_text())
    functions=json.loads((OUT/'Functions/manifest.json').read_text())
    loops=json.loads((OUT/'loops.json').read_text())
    helper=json.loads((OUT/'abs.json').read_text())
    total=functions['counts']['functions']
    normal={int(e) for e,f in functions['functions'].items() if f['normal_generated']}
    normal.update(loops['recognized_length_loops'])
    normal.add(helper['source_entry'])
    calls={c['pc']:c for f in functions['functions'].values() for c in f['calls']}
    backedges={(e['from'],e['to']) for f in functions['functions'].values() for e in f['back_edges']}
    result={
      'instructions':blocks['instructions'],'code_words':blocks['code_words'],
      'instruction_shards':len(blocks['shards']),
      'certified_block_rules':sum(s['blocks'] for s in blocks['shards'].values()),
      'closure_entries':total,'fully_generated_normal_entries':len(normal),
      'normal_share':len(normal)/total,
      'generated_over_application_entries':functions['counts']['over'],
      'over_share':functions['counts']['over']/total,
      'grab_entries':functions['counts']['under'],
      'generated_under_application_entries':functions['counts']['under'],
      'under_share_of_all_entries':functions['counts']['under']/total,
      'under_share_of_grab_entries':1.0,
      'generated_ranked_list_loops':loops['recognized_length_loops'],
      'explicit_cfg_back_edges':len(backedges),
      'unique_higher_order_call_sites':len(calls),
      'call_sites':sum(c['kind']=='call' for c in calls.values()),
      'tail_call_sites':sum(c['kind']=='tail' for c in calls.values()),
      'statically_resolved_general_callee_edges':0,
      'limitations':[
        'A block rule requires its code pin and local symbolic evaluation; it is not a function termination proof.',
        'Normal summaries have generated structural calling/field/list preconditions, never a full-run premise.',
        'Under-application returns a partial closure; it does not prove the eventual saturated body.',
        'Call and tail composition use Application.call_summary/tail_summary. Unknown higher-order callees remain open.',
        'The two recognized tail-recursive list loops use loop_rule; other loops and counting shapes remain open.',
        'CFG back edges exclude dynamic tail calls, so they are not a denominator for the recognized tail-recursive loops.',
        'The adequacy harness invokes an unchanged compiler helper copy; it is not a proof that boot/ocamlc terminates.'
      ]}
    path=ROOT/'results/bprime_coverage.json';text=json.dumps(result,indent=2)+'\n'
    if args.check:
        if not path.exists() or path.read_text()!=text:raise SystemExit('bytecode coverage report drift')
    else:path.write_text(text)
    print(f'normal summaries: {len(normal)}/{total} ({len(normal)/total:.2%}); '
          f'under: {functions["counts"]["under"]}/{total}; list loops: {len(loops["recognized_length_loops"])}')
if __name__=='__main__':main()
