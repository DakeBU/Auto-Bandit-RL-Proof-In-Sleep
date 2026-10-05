"""Check actual compiled environment proof-value occurrences for this package."""
from pathlib import Path
import json,hashlib,re
run=Path(__file__).parent
export=Path('tmp/online-unit-scaling-full-graph.json')
raw=export.read_bytes();graph=json.loads(raw)
ns='BanditRL.OnlineUnitScaling.'
scope={ns+n for n in re.findall(r'^(?:theorem|def|abbrev)\s+(\w+)',Path('BanditRLProof/OnlineUnitScaling.lean').read_text(encoding='utf-8'),re.M)}
assert len(scope)==26
nodes={n['name']:n for n in graph['nodes']};assert scope<=set(nodes),scope-set(nodes)
edges=[e for e in graph['edges'] if e['source'] in scope]
required=[(ns+a,ns+b) for a,b in [
    ('subdifferentiable_scaled','proper_scaled_loss'),('subdifferentiable_scaled','subgradient_scaled'),
    ('gradient_scaled','hasGradientAt_scaled'),('history_scaling','inverse_loss'),('history_scaling','step_scaling'),
    ('output_scaling','history_scaling'),('selected_scaling','history_scaling'),('selected_scaling','inverse_loss'),
    ('legal_feedback_scaling','output_scaling'),('legal_feedback_scaling','selected_scaling'),('legal_feedback_scaling','subgradient_scaled'),
    ('loss_value_scaling','output_scaling'),('regret_scaling','loss_value_scaling'),('wrong_step_output','output_scaling'),
    ('energy_scaling','selected_scaling'),('regret_fixed_scaled','regret_scaling')]]
required += [(ns+'subgradient_scaled','BanditRL.OnlineConvex.theorem_2_28'),
    (ns+'history_scaling','BanditRL.OnlineSubgradientPolicy.history_succ'),
    (ns+'history_scaling','BanditRL.OnlineHuber.project_fullSpace'),
    (ns+'regret_fixed_scaled','BanditRL.OnlineSubgradientPolicy.regret_fixed'),
    (ns+'hasGradientAt_scaled','HasFDerivAt.comp')]
for a,b in required:
    assert any(e['source']==a and e['target']==b and (e['kind']=='value' or e.get('also_in_value',False)) for e in edges),(a,b)
boundary={e['target'] for e in edges}-scope
result=dict(full_export_sha256=hashlib.sha256(raw).hexdigest(),full_export_path=export.as_posix(),
    full_export_counts=graph['counts'],extraction=graph['extraction'],lean_version=graph['lean_version'],
    required_proof_value_checks=required,scope_nodes=len(scope),boundary_nodes=len(boundary),
    nodes=[nodes[n] for n in sorted(scope|boundary)],edges=edges)
with (run/'compiled-dependencies.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(dict(status='passed',required_proof_value_checks=len(required),scope_nodes=len(scope),boundary_nodes=len(boundary),edges=len(edges),full_counts=graph['counts'])))
