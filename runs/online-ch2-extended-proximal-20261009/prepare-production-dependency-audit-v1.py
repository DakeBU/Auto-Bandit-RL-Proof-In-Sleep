from common import *
fixed();old=(ROOT/'runs/online-ch2-bregman-20261009/export-production-dependencies-v1.lean').read_text(encoding='utf8')
start=old.index('def targets : Array Name := #[');end=old.index('\n\ndef moduleName',start)
d=load(CONTRACT/'stabilized-v1.json');names=[t['declaration'] for t in d['targets']]
text=old[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+old[end:]
text=text.replace('BanditRLProof.OnlineBregmanProximal','BanditRLProof.OnlineBregmanExtended')
text=text.replace('Five frozen Bregman helper proofs and one complete canonical definition, no Test nodes yet.','Three frozen EReal finite-domain bridge proofs, no Test nodes yet.')
write(RUN/'export-production-dependencies-v1.lean',text)
capture('production-dependency-command-v1','lake','env','lean','--run',RUN/'export-production-dependencies-v1.lean',RUN/'production-dependency-data-v1.json')
graph=load(RUN/'production-dependency-data-v1.json');nodes={n['name']:n for n in graph['nodes']}
assert len(nodes)==3 and all(n['has_value'] for n in nodes.values())
prefix='BanditRL.OnlineBregman.'
pairs=[[names[0],'BanditRL.OnlineConvex.subgradient_point_finite'],[names[1],'BanditRL.OnlineConvex.minOn_finitePart_iff']]
pairs += [[names[2],n] for n in [names[0],names[1],prefix+'proximal_one_step','BanditRL.OnlineConvex.subgradient_point_finite']]
for a,b in pairs:assert b in nodes[a]['value_dependencies'],(a,b)
write(RUN/'production-dependency-inspected-v1.json',dict(selected_nodes=len(nodes),definitions=0,theorems=3,coalesced_direct_TYPE_VALUE_presences=len(graph['edges']),required_actual_VALUE_pairs=pairs,graph_sha256=sha(RUN/'production-dependency-data-v1.json'),production_sha256=sha(PUBLIC),not_full_transitive_graph=True,not_registry_or_source_denominator=True,source_container_closed=False,whole_Goal_status='ACTIVE'))
fixed();print('Three actual compiled bridge nodes and six required actualVALUE parentpairs inspected:',len(graph['edges']),'direct presences')
