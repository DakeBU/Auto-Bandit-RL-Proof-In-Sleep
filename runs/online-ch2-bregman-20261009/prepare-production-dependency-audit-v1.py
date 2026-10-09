from common import *
fixed()
old=(ROOT/'runs/online-ch2-proximal-20261009/export-selected-dependencies-v1.lean').read_text(encoding='utf8')
start=old.index('def targets : Array Name := #[')
end=old.index('\n\ndef moduleName',start)
d=load(CONTRACT/'stabilized-v1.json')
names=[d['definition']['declaration']]+[t['declaration'] for t in d['targets']]
text=old[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+old[end:]
text=text.replace('import BanditRLProof.OnlineProximalComparison\nimport Tests.OnlineProximalComparisonCanary','import BanditRLProof.OnlineBregmanProximal')
text=text.replace('#[{ module := `BanditRLProof.OnlineProximalComparison }, { module := `Tests.OnlineProximalComparisonCanary }]','#[{ module := `BanditRLProof.OnlineBregmanProximal }]')
text=text.replace('_private.Tests.OnlineProximalComparisonCanary.','_private.BanditRLProof.OnlineBregmanProximal.')
text=text.replace('One frozen real convex minimizer-comparison proof and three exact public canary families.','Five frozen Bregman helper proofs and one complete canonical definition, no Test nodes yet.')
write(RUN/'export-production-dependencies-v1.lean',text)
capture('production-dependency-command-v1','lake','env','lean','--run',RUN/'export-production-dependencies-v1.lean',RUN/'production-dependency-data-v1.json')
graph=load(RUN/'production-dependency-data-v1.json')
nodes={n['name']:n for n in graph['nodes']}
assert len(nodes)==6 and all(n['has_value'] for n in nodes.values())
pairs=[['BanditRL.OnlineBregman.proximal_one_step',n] for n in ['BanditRL.OnlineProximal.convex_minimizer_comparison','BanditRL.OnlineBregman.three_point_identity']]
pairs+=[['BanditRL.OnlineBregman.divergence_nonneg','ConvexOn.le_slope_of_hasDerivAt'],['BanditRL.OnlineBregman.divergence_eq_gradient','HasGradientAt.fderiv_apply']]
for a,b in pairs:
    assert b in nodes[a]['value_dependencies'],(a,b)
write(RUN/'production-dependency-inspected-v1.json',dict(selected_nodes=6,definitions=1,theorems=5,coalesced_direct_TYPE_VALUE_presences=len(graph['edges']),required_actual_VALUE_pairs=pairs,graph_sha256=sha(RUN/'production-dependency-data-v1.json'),production_sha256=sha(PUBLIC),not_full_transitive_graph=True,not_registry_or_source_denominator=True,source_container_closed=False,whole_Goal_status='ACTIVE'))
fixed()
print('Six compiled production nodes and four required actual VALUE parent pairs inspected.')
