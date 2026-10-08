from common_canary_v1 import *
import re
s=canary_contract_fixed()
assert load(RUN/'canary-attempt-v1.json')['actual_build_exit']==0
canaries=load(CONTRACT/'canary-targets-v1.json')['targets']
parents=['empiricalMean','meanPredict','dyadicObservation','meanPredict_fixedRegret_limit_iff',
    'meanPredict_limitNoRegret_of_mean_converges','meanPredict_noRegret',
    'meanPredict_bestRegret_average_tendsto_zero','empiricalMean_mem','squaredBestRegret_eq_comparatorRegret']
names=[t['name'] for t in s['targets']+canaries]+['BanditRL.OnlineLearning.'+p for p in parents]
assert len(names)==len(set(names))
value='import Tests.OnlineFTLOscillationCanary\nopen Filter BanditRL.OnlineLearning\nnamespace ActualFTLObstructionValues\n'
for i,t in enumerate(s['targets'],1):
    args,goal=t['header'].split(t['name'].split('.')[-1],1)[1].split(' :\n',1)
    value+='\ndef Q%d : Prop := '%i+('∀ '+args.strip()+',\n' if args.strip() else '')+goal+'\n'
    value+='\ntheorem wholePublicValue%d : Q%d := @%s\n'%(i,i,t['name'])
    value+='#check wholePublicValue%d\n#print axioms wholePublicValue%d\n'%(i,i)
value+='\nend ActualFTLObstructionValues\n\n'
for name in names:value+='#check '+name+'\n#print axioms '+name+'\n'
write(RUN/'whole-public-values-axioms-v1.lean',value)
gate('whole-public-values-axioms-v1','lake','env','lean',RUN/'whole-public-values-axioms-v1.lean')
log=(RUN/'whole-public-values-axioms-v1.log').read_text(encoding='utf8')
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
assert len(axioms)==len(names)+4
allowed={'propext','Classical.choice','Quot.sound'}
for name,alist in axioms:assert set(x.strip() for x in alist.split(',') if x.strip())<=allowed,(name,alist)
assert 'sorryAx' not in log
source=(ROOT/'runs/online-kernel-causal-20261008/export-compiled-body-graph-v1.lean').read_text(encoding='utf8')
source=source.replace('Tests.OnlineGuessingKernelCausalCanary','Tests.OnlineFTLOscillationCanary')
start=source.index('def targets : Array Name := #[');end=source.index('\n\ndef moduleName',start)
source=source[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+source[end:]
start=source.index('  let anonymous :=');end=source.index('    let some info :=',start)
source=source[:start]+'  for n in targets do\n'+source[end:]
source=source.replace('Five frozen actual causal-kernel proof bodies, stochastic history-feedback canaries and exact parents.',
    'Four frozen actual FTL obstruction/iff bodies, eleven dyadic public canaries and exact parents.')
write(RUN/'export-compiled-graph-v1.lean',source)
gate('export-compiled-graph-v1','lake','env','lean','--run',RUN/'export-compiled-graph-v1.lean',RUN/'compiled-graph-v1.json')
g=load(RUN/'compiled-graph-v1.json');byname={n['name']:n for n in g['nodes']}
ns=[t['name'] for t in s['targets']];cs=[t['name'] for t in canaries]
pairs=[(ns[0],'BanditRL.OnlineLearning.meanPredict_fixedRegret_limit_iff'),
    (ns[0],'BanditRL.OnlineLearning.meanPredict_limitNoRegret_of_mean_converges'),
    (ns[0],'BanditRL.OnlineLearning.empiricalMean_mem'),
    (ns[3],ns[1]),(ns[3],ns[2]),(ns[3],'BanditRL.OnlineLearning.meanPredict_noRegret'),
    (ns[3],'BanditRL.OnlineLearning.meanPredict_bestRegret_average_tendsto_zero'),
    (ns[3],'BanditRL.OnlineLearning.meanPredict_fixedRegret_limit_iff'),
    (cs[0],ns[1]),(cs[2],'BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret'),
    (cs[3],ns[0]),(cs[4],cs[3]),(cs[4],ns[3]),(cs[5],ns[2]),(cs[6],ns[3])]+[(cs[i],ns[3]) for i in range(7,11)]
for a,b in pairs:assert b in byname[a]['value_dependencies'],(a,b)
for t in canaries:
    native(t['id']+'-fence-v1','statement-fence','--declaration',t['name'],'--file',CANARY.relative_to(ROOT).as_posix(),
        '--output',RUN/('fences/'+t['id']+'-v1.json'))
    native(t['id']+'-safe-v1','safe-verify','--fence',RUN/('fences/'+t['id']+'-v1.json'))
write(RUN/'compiled-audit-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    whole_public_type_value_witnesses=4,actual_named_axiom_outputs=len(axioms),axioms_only=sorted(allowed),sorryAx=False,
    actual_canary_proofs=11,actual_selected_nodes=len(g['nodes']),actual_selected_coalesced_TYPE_VALUE_edges=len(g['edges']),
    required_direct_value_pairs=pairs,actual_required_pairs=len(pairs),all_frozen_headers_unchanged=True,
    native_fences=15,native_safe_checks_successful=15,initial_D4_inference_failure_retained=True,
    D4_explicit_zero_body_repair_v2_successful=True,body_acceptance_pending=True,chapter_complete=False,goal_complete=False))
print('Actual four whole VALUE witnesses; %d standard-only axiom outputs; %d selected nodes; %d direct VALUE pairs;15 fences.'%(len(axioms),len(g['nodes']),len(pairs)),flush=True)
