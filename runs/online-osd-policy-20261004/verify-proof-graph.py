"""Check actual compiled proof-value edges; teaching links are not substitutes."""
from pathlib import Path
import hashlib, json, re

run=Path(__file__).parent
export=Path('tmp/online-osd-policy-full-graph.json')
raw=export.read_bytes(); graph=json.loads(raw)
ns='BanditRL.OnlineSubgradientPolicy.'
ogd='BanditRL.OnlineGradientDescent.'
osd='BanditRL.OnlineSubgradientDescent.'
scope={ns+n for n in re.findall(r'^(?:theorem|def|abbrev) (\w+)',
    Path('BanditRLProof/OnlineSubgradientPolicy.lean').read_text(encoding='utf-8'),re.M)}
nodes={n['name']:n for n in graph['nodes']}
assert scope<=set(nodes),scope-set(nodes)
edges=[e for e in graph['edges'] if e['source'] in scope]
required=[
 (ns+'history_mem',ogd+'project_spec'),
 (ns+'output_mem',ns+'history_mem'),
 (ns+'history_prefix',ns+'history_succ'),
 (ns+'output_prefix',ns+'history_prefix'),
 (ns+'oracle_feedback',ns+'output_mem'),
 (ns+'trajectory_finite_loss',osd+'finite_loss'),
 (ns+'trajectory_finite_loss',ns+'output_mem'),
 (ns+'one_step_chain',osd+'lemma_2_31'),
 (ns+'one_step_chain',ns+'output_succ'),
 (ns+'one_step',ns+'one_step_chain'),
 (ns+'regret_fixed',ns+'one_step_chain'),
 (ns+'regret_fixed_coarse',ns+'regret_fixed'),
 (ns+'regret_variable_bound',ns+'one_step'),
 (ns+'regret_variable_bound',ns+'output_mem'),
 (ns+'regret_variable_bound',ogd+'weighted_potential_sum'),
 (ns+'regret_variable',ns+'regret_variable_bound'),
 (ns+'regret_tuned_distance',ns+'regret_fixed'),
 (ns+'regret_tuned',ns+'regret_tuned_distance'),
 (ns+'canonicalPolicy_legal',osd+'currentSubgradient_mem'),
 (ns+'canonical_output',ns+'output_succ'),
 (ns+'canonical_selected',ns+'canonical_output'),
]
for a,b in required:
    assert any(e['source']==a and e['target']==b and
        (e['kind']=='value' or e.get('also_in_value',False)) for e in edges),(a,b)
boundary={e['target'] for e in edges}-scope
result={'full_export_sha256':hashlib.sha256(raw).hexdigest(),
 'full_export_path':str(export),'full_export_counts':graph['counts'],
 'extraction':graph['extraction'],'lean_version':graph['lean_version'],
 'required_proof_value_checks':required,'scope_nodes':len(scope),
 'boundary_nodes':len(boundary),'nodes':[nodes[n] for n in sorted(scope|boundary)],'edges':edges}
with (run/'compiled-dependencies.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'status':'passed','required_proof_value_checks':len(required),
 'scope_nodes':len(scope),'boundary_nodes':len(boundary),'edges':len(edges),
 'full_counts':graph['counts']}))
