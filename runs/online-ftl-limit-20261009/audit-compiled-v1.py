from common_canary_v1 import *
import re
s=canary_contract_fixed()
assert load(RUN/'canary-attempt-v1.json')['actual_build_exit']==0
canaries=load(CONTRACT/'canary-targets-v1.json')['targets']
parents=['empiricalMean','meanPredict','empiricalMean_minimizes','empiricalMean_decomposition',
    'squaredLoss_minimum_eq','squaredBestRegret_eq_comparatorRegret','meanPredict_bestRegret_bound']
names=[t['name'] for t in s['targets']+canaries]+['BanditRL.OnlineLearning.'+p for p in parents]
value='import Tests.OnlineFTLLimitSemanticsCanary\nopen Filter BanditRL.OnlineLearning\nnamespace ActualFTLValues\n'
for i,t in enumerate(s['targets'],1):
    args,goal=t['header'].split(t['name'].split('.')[-1],1)[1].split(' :\n',1)
    value+='\ndef Q%d : Prop := ∀ '%i+args.strip()+',\n'+goal+'\n'
    value+='\ntheorem wholePublicValue%d : Q%d := @%s\n'%(i,i,t['name'])
    value+='#check wholePublicValue%d\n#print axioms wholePublicValue%d\n'%(i,i)
value+='\nend ActualFTLValues\n\n'
for name in names:
    value+='#check '+name+'\n#print axioms '+name+'\n'
write(RUN/'whole-public-values-axioms-v1.lean',value)
gate('whole-public-values-axioms-v1','lake','env','lean',RUN/'whole-public-values-axioms-v1.lean')
log=(RUN/'whole-public-values-axioms-v1.log').read_text(encoding='utf8')
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
assert len(axioms)==len(names)+5==29
allowed={'propext','Classical.choice','Quot.sound'}
for name,axiomlist in axioms:
    assert set(x.strip() for x in axiomlist.split(',') if x.strip()) <= allowed,(name,axiomlist)
assert 'sorryAx' not in log
source=(ROOT/'runs/online-kernel-causal-20261008/export-compiled-body-graph-v1.lean').read_text(encoding='utf8')
source=source.replace('Tests.OnlineGuessingKernelCausalCanary','Tests.OnlineFTLLimitSemanticsCanary')
start=source.index('def targets : Array Name := #[')
end=source.index('\n\ndef moduleName',start)
source=source[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+source[end:]
start=source.index('  let anonymous :=')
end=source.index('    let some info :=',start)
source=source[:start]+'  for n in targets do\n'+source[end:]
source=source.replace('Five frozen actual causal-kernel proof bodies, stochastic history-feedback canaries and exact parents.',
    'Five frozen actual FTL limit proof bodies, periodic binary canaries and exact parents.')
write(RUN/'export-compiled-graph-v1.lean',source)
gate('export-compiled-graph-v1','lake','env','lean','--run',RUN/'export-compiled-graph-v1.lean',RUN/'compiled-graph-v1.json')
g=load(RUN/'compiled-graph-v1.json')
byname={n['name']:n for n in g['nodes']}
ns=[t['name'] for t in s['targets']]
cs=[t['name'] for t in canaries]
pairs=[(ns[0],'BanditRL.OnlineLearning.empiricalMean_minimizes'),
    (ns[1],'BanditRL.OnlineLearning.empiricalMean_decomposition'),(ns[2],ns[0]),
    (ns[2],'BanditRL.OnlineLearning.meanPredict_bestRegret_bound'),(ns[3],ns[1]),(ns[3],ns[2]),
    (ns[4],ns[3]),(cs[2],cs[1]),(cs[5],ns[0]),(cs[6],ns[1]),(cs[7],ns[2]),(cs[8],ns[3]),
    (cs[9],ns[4]),(cs[10],ns[4]),(cs[11],ns[4]),(cs[9],cs[2])]
for a,b in pairs:
    assert b in byname[a]['value_dependencies'],(a,b)
for t in canaries:
    native(t['id']+'-fence-v1','statement-fence','--declaration',t['name'],'--file',CANARY.relative_to(ROOT).as_posix(),
        '--output',(RUN/('fences/'+t['id']+'-v1.json')).relative_to(ROOT).as_posix())
    native(t['id']+'-safe-v1','safe-verify','--fence',(RUN/('fences/'+t['id']+'-v1.json')).relative_to(ROOT).as_posix())
write(RUN/'compiled-audit-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    whole_public_type_value_witnesses=5,actual_named_axiom_outputs=29,axioms_only=sorted(allowed),sorryAx=False,
    actual_canary_proofs=12,actual_selected_nodes=len(g['nodes']),actual_selected_coalesced_TYPE_VALUE_edges=len(g['edges']),
    required_direct_value_pairs=pairs,actual_required_pairs=len(pairs),
    all_frozen_headers_unchanged=True,native_fences=17,native_safe_checks_successful=17,
    initial_F1_prose_fence_failed_retained=True,F1_correct_literal_fence_v2_successful=True,
    body_acceptance_pending=True,chapter_complete=False,goal_complete=False))
print('Actual five whole VALUE witnesses;29 standard-only axiom outputs;24 selected nodes;16 direct VALUE pairs;17 native fences.',flush=True)
