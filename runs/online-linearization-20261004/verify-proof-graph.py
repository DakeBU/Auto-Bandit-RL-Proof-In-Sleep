"""Check actual compiled proof-value edges; teaching links are not substitutes."""
from pathlib import Path
import hashlib, json, re

run=Path(__file__).parent
export=Path('tmp/online-linearization-full-graph.json')
raw=export.read_bytes(); graph=json.loads(raw)
ns='BanditRL.OnlineLinearization.'
ogd='BanditRL.OnlineGradientDescent.'
osd='BanditRL.OnlineSubgradientDescent.'
scope={ns+n for n in re.findall(r'^(?:theorem|def|abbrev) (\w+)',
    Path('BanditRLProof/OnlineLinearization.lean').read_text(encoding='utf-8'),re.M)}
nodes={n['name']:n for n in graph['nodes']}
assert scope<=set(nodes),scope-set(nodes)
edges=[e for e in graph['edges'] if e['source'] in scope]
required=[
 (ns+'history_castSucc',ns+'history_succ'),
 (ns+'history_selected',ns+'history_castSucc'),
 (ns+'history_selected',ns+'history_succ'),
 (ns+'output_linear_run',ns+'history_selected'),
 (ns+'outputHistory_played',ns+'history_selected'),
 (ns+'output_prefix',ns+'history_prefix'),
 (ns+'oracle_feedback',ns+'outputHistory_last'),
 (ns+'canonical_feedback',ns+'oracle_feedback'),
 (ns+'canonical_feedback','BanditRL.OnlineSubgradientPolicy.canonicalPolicy_legal'),
 (ns+'trajectory_finite_loss',osd+'finite_loss'),
 (ns+'trajectory_finite_loss',ns+'output_mem'),
 (ns+'support_gap',osd+'lemma_2_31'),
 (ns+'regret_comparison',ns+'support_gap'),
 (ns+'regret_comparison',ns+'linearLoss_gap'),
 (ns+'regret_comparison',ns+'output_linear_run'),
 (ns+'regret_comparison','BanditRL.OnlineLearning.comparatorRegret_eq_sum'),
 (ns+'regret_transfer',ns+'regret_comparison'),
 (ns+'canonical_regret_comparison',ns+'canonical_feedback'),
 (ns+'canonical_regret_comparison',ns+'regret_comparison'),
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
