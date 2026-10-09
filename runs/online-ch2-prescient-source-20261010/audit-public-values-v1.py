from proof_driver import *
import re
fixed()
assert load(RUN/'decreasing-canary-focused-inspected-v1.json')['compiled_module_markers']
TEST=ROOT/'Tests/OnlinePrescientBregmanSourceCanary.lean'
st=load(CONTRACT/'stabilized-v1.json')
cs=load(CONTRACT/'canary-headers-draft-v2.json')
names=[t['name'] for t in st['six_targets']+cs['targets']]
probe=cs['imports'].replace('import BanditRLProof.OnlinePrescientBregmanSource\n','')
for row in cs['targets']:
    probe+=row['header'].replace('theorem '+row['name'].rsplit('.',1)[1],'example',1).rstrip()+' := by\n  exact '+row['name']+'\n\n#check @'+row['name']+'\n#print axioms '+row['name']+'\n'
probe+='end BanditRL.OnlinePrescientBregmanSourceCanary\n'
probe=probe.replace('import Tests.OnlinePrescientBregmanRegretCanary','import Tests.OnlinePrescientBregmanSourceCanary')
write(RUN/'two-full-canaries-public-v1.lean',probe)
code,out=capture('two-full-canaries-public-v1','lake','env','lean',RUN/'two-full-canaries-public-v1.lean')
ax=re.findall(r'depends on axioms: \[([^\]]*)\]',out)
assert len(ax)==2 and all(set(map(str.strip,s.split(',')))<=set(['propext','Classical.choice','Quot.sound']) for s in ax)
graph=(ROOT/'runs/online-ch2-prescient-causal-20261009/export-selected-dependencies-v1.lean').read_text(encoding='utf8')
a=graph.index('def targets : Array Name := #[')
b=graph.index('\n\ndef moduleName',a)
graph=graph[:a]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+graph[b:]
graph=graph.replace('Tests.OnlinePrescientBregmanCanary','Tests.OnlinePrescientBregmanSourceCanary')
graph=graph.replace('Eight frozen production proofs/two exact definitions and four complete concrete Test conjunctions plus referenced compiler-generated Test auxiliaries.','Six frozen production proofs and two complete concrete Test conjunctions plus referenced compiler-generated Test auxiliaries.')
write(RUN/'export-selected-dependencies-v1.lean',graph)
assert not (RUN/'selected-value-graph-v1.json').exists()
capture('selected-graph-export-v1','lake','env','lean','--run',RUN/'export-selected-dependencies-v1.lean',RUN/'selected-value-graph-v1.json')
numeric=(ROOT/'runs/online-ch2-prescient-cumulative-20261009/audit-four-numeric-branches-v2.lean').read_text(encoding='utf8')
numeric=numeric.replace('Tests.OnlinePrescientBregmanRegretCanary','Tests.OnlinePrescientBregmanSourceCanary')
a=numeric.index('  for (name,index,required) in #[')
b=numeric.index('] do',a)+len('] do')
numeric=numeric[:a]+'''  for (name,index,required) in #[
    (`BanditRL.OnlinePrescientBregmanSourceCanary.fixed_source_run,7,`BanditRL.OnlinePrescientBregman.source_fixed_regret),
    (`BanditRL.OnlinePrescientBregmanSourceCanary.decreasing_source_run,5,`BanditRL.OnlinePrescientBregman.source_variable_regret)] do'''+numeric[b:]
write(RUN/'audit-two-numeric-branches-v1.lean',numeric)
capture('two-numeric-branches-v1','lake','env','lean','--run',RUN/'audit-two-numeric-branches-v1.lean',RUN/'two-numeric-branches-v1.json')
g=load(RUN/'selected-value-graph-v1.json');nd={n['name']:n for n in g['nodes']}
assert set(names)<=set(nd) and all(nd[n]['has_value'] for n in names)
p='BanditRL.OnlinePrescientBregman.';c='BanditRL.OnlineConvex.';B='BanditRL.OnlineBregman.'
pairs=[
 (c+'sourceProper_of_domain','EReal.coe_toReal'),
 (p+'penalized_strictConvex',B+'finitePart_convex_of_subdifferentiable'),
 (p+'advance_eq_some_of_minimizer',p+'penalized_strictConvex'),
 (p+'advance_eq_some_of_minimizer',B+'proximal_finitePart_minimizer_iff'),
 (p+'advance_eq_some_of_minimizer','StrictConvexOn.eq_of_isMinOn'),
 (p+'iterate_eq_of_source_updates',p+'advance_eq_some_of_minimizer'),
 (p+'source_fixed_regret',c+'sourceProper_of_domain'),
 (p+'source_fixed_regret',p+'iterate_eq_of_source_updates'),
 (p+'source_fixed_regret',p+'iterate_fixed_regret'),
 (p+'source_variable_regret',c+'sourceProper_of_domain'),
 (p+'source_variable_regret',p+'iterate_eq_of_source_updates'),
 (p+'source_variable_regret',p+'iterate_variable_regret')]
cf=cs['targets'][0]['name'];cv=cs['targets'][1]['name']
pairs += [(cf,n) for n in [c+'sourceProper_of_domain',p+'penalized_strictConvex',p+'advance_eq_some_of_minimizer',p+'iterate_eq_of_source_updates',p+'source_fixed_regret']]
pairs += [(cv,n) for n in [c+'sourceProper_of_domain',p+'iterate_eq_of_source_updates',p+'source_variable_regret']]
for a,b in pairs:assert b in nd[a]['value_dependencies'],(a,b)
tails=load(RUN/'two-numeric-branches-v1.json')['rows']
assert len(tails)==2 and all(r['required_present'] for r in tails)
for row in st['six_targets']+cs['targets']:
    short=row['name'].rsplit('.',1)[1]
    file=PUBLIC if row in st['six_targets'] else TEST
    frozen=load(CONTRACT/('frozen-'+short+'-v1.json'))
    assert lifecycle.statement_hash(lifecycle.lean_declaration_header(file,row['name']))==frozen['statement_hash']
    capture('native-fence-'+short+'-v2',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',row['name'],'--file',file.relative_to(ROOT),'--output',CONTRACT.relative_to(ROOT)/('native-'+short+'-v2.json'))
    capture('safe-verify-'+short+'-v1',sys.executable,'-B','-X','utf8',ROOT/'tools/bandit.py','safe-verify','--fence',CONTRACT.relative_to(ROOT)/('native-'+short+'-v2.json'))
write(RUN/'eight-public-values-inspected-v1.json',dict(public_nodes=len(names),total_selected_nodes=len(nd),generated_auxiliaries=len(nd)-len(names),coalesced_direct_TYPE_VALUE_presences=len(g['edges']),required_VALUE_pairs=pairs,selected_numeric_tails=tails,public_full_canary_conjunction_sizes=[8,6],public_canary_axiom_lists=2,production_axiom_lists=6,standard_only_axioms=['propext','Classical.choice','Quot.sound'],actual_sources=rows([PUBLIC,TEST]),eight_headers_unchanged=True,semantic_BODY='pending',root_Tests_harness='pending',package_accepted=False,chapter_complete=False,whole_goal='active'))
fixed()
