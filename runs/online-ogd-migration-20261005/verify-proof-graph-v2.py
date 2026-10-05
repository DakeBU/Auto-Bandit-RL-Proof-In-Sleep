"""Check actual compiled proof-value occurrences in the shared root environment."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
export=Path('tmp/online-ogd-migration-full-graph.json')
raw=export.read_bytes();graph=json.loads(raw)
inventory=json.loads((run/'public-named-declarations-v2.json').read_text())
scope=set(inventory['new_public']+inventory['old_reused']);assert len(scope)==38
nodes={n['name']:n for n in graph['nodes']};assert scope<=set(nodes),scope-set(nodes)
edges=[e for e in graph['edges'] if e['source'] in scope]
new='BanditRL.OnlineGradientDescentSource.'
old='BanditRL.OnlineGradientDescent.'
required=[(new+a,new+b) for a,b in [
    ('lemma_2_12','first_order'),('lemma_2_12','linear_regular'),('lemma_2_12','gradient_linear'),
    ('theorem_2_13_fixed','lemma_2_12'),('variable_one_step','lemma_2_12'),
    ('theorem_2_13_variable_bound','variable_one_step'),
    ('theorem_2_13_variable','theorem_2_13_variable_bound'),
    ('equation_2_1_distance','theorem_2_13_fixed'),('equation_2_1','equation_2_1_distance')]]
required += [(new+a,old+b) for a,b in [
    ('lemma_2_12','lemma_2_12'),('theorem_2_13_fixed','iterate_mem'),
    ('variable_one_step','iterateVariable_mem'),
    ('theorem_2_13_variable_bound','weighted_potential_sum'),
    ('theorem_2_13_variable_bound','iterateVariable_mem')]]
required += [(new+a,b) for a,b in [
    ('source_to_feasible','DifferentiableOn.differentiableAt'),
    ('regular_to_feasible','ConvexOn.subset'),
    ('first_order','BanditRL.OnlineConvex.convex_gradient_lower_bound'),
    ('linear_regular','LinearMap.convexOn'),('linear_regular','ContinuousLinearMap.differentiable'),
    ('gradient_linear','HasGradientAt.gradient'),('gradient_linear','hasGradientAt_iff_hasFDerivAt'),
    ('gradient_linear','ContinuousLinearMap.hasFDerivAt'),
    ('theorem_2_13_variable','Metric.dist_le_diam_of_mem')]]
required += [(old+a,old+b) for a,b in [
    ('lemma_2_12','first_order'),('lemma_2_12','proposition_2_11'),
    ('theorem_2_13_fixed','lemma_2_12'),('theorem_2_13_fixed','iterate_mem'),
    ('variable_one_step','lemma_2_12'),('variable_one_step','iterateVariable_mem'),
    ('theorem_2_13_variable_bound','weighted_potential_sum'),
    ('theorem_2_13_variable_bound','variable_one_step')]]
required += [(old+'project_spec','exists_norm_eq_iInf_of_complete_convex'),
    (old+'proposition_2_11','norm_eq_iInf_iff_real_inner_le_zero')]
for a,b in required:
    assert any(e['source']==a and e['target']==b and
        (e['kind']=='value' or e.get('also_in_value',False)) for e in edges),(a,b)
boundary={e['target'] for e in edges}-scope
result=dict(status='passed',full_export_path=export.as_posix(),
    full_export_sha256=hashlib.sha256(raw).hexdigest(),full_export_counts=graph['counts'],
    extraction=graph['extraction'],lean_version=graph['lean_version'],scope_nodes=len(scope),
    boundary_nodes=len(boundary),required_proof_value_checks=required,
    nodes=[nodes[n] for n in sorted(scope|boundary)],edges=edges,
    boundary='38 explicit source/old compatibility declarations in one shared compiled graph; '
        'generated structure/recursor declarations remain in graph/boundary, not source-result counts. '
        'This is actual proof-term evidence, separate from teaching navigation. '
        'Compiled current isolated checkout; no merge/main/live claim.')
with (run/'compiled-dependencies-v2.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(dict(status='passed',scope_nodes=len(scope),boundary_nodes=len(boundary),
    actual_edges=len(edges),required_value_pairs=len(required),full_counts=graph['counts'])))
