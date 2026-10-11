from common import *
import re
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
public=ROOT/'Tests/OnlineAdaptiveOSDCanary.lean'
headers=load(CONTRACT/'algorithm-canary-stabilized-v1.json')['exact_headers']
probe='''import Tests.OnlineAdaptiveOSDCanary
noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineAdaptiveOSD AdaptiveProbe
'''
successes={}
for name,row in headers.items():
    actual=[p for p in RUN.glob('algorithm-canary-'+name+'-focused-build-v*.json') if load(p)['actual_exit']==0]
    assert actual,name
    successes[name]=rows(actual)
    assert sha(row['path'])==row['raw_sha256']
    assert statement_hash(lean_declaration_header(public,name))==row['normalized_statement_hash']
    probe+='\n'+Path(row['path']).read_text(encoding='utf8').replace('theorem '+name,'example',1)
    probe+='  exact AdaptiveProbe.'+name+(' U t' if name=='loss_regular' else '')+'\n'
    probe+='#check AdaptiveProbe.'+name+'\n#print axioms AdaptiveProbe.'+name+'\n'
write(RUN/'AlgorithmCanaryPublicProbeV1.lean',probe)
code,out=capture('algorithm-canary-public-probe-v1','lake','env','lean',RUN/'AlgorithmCanaryPublicProbeV1.lean')
print(out,flush=True)
audits=re.findall(r"depends on axioms: \[(.*?)\]",out)
assert len(audits)==7 and all(set(a.split(', ')).issubset({'propext','Classical.choice','Quot.sound'}) for a in audits)
for name in headers:
    capture('algorithm-canary-'+name+'-fence-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py',
        'statement-fence','--declaration',name,'--file',public,
        '--output',RUN/('algorithm-canary-'+name+'-fence-native-v1.json'))
    capture('algorithm-canary-'+name+'-safe-verify-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py',
        'safe-verify','--fence',RUN/('algorithm-canary-'+name+'-fence-native-v1.json'),'--lean-file',public)
capture('algorithm-canary-named-declarations-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py',
    'list-lean-decls','OnlineAdaptiveOSDCanary','--statement')
exporter=(RUN/'ExportPotentialCanaryConjunctValuesV1.lean').read_text(encoding='utf8')
exporter=exporter.replace('Tests.OnlineAdaptivePotentialCanary','Tests.OnlineAdaptiveOSDCanary')
a=exporter.index('  for n in #[')
b=exporter.index(' do\n',a)
exporter=exporter[:a]+'  for n in #['+', '.join('`AdaptiveProbe.'+name for name in headers)+']'+exporter[b:]
expected=[('performance_canary',0,'BanditRL.OnlineAdaptiveOSD.regret_bound'),
    ('performance_canary',1,'BanditRL.OnlineAdaptiveOSD.source_eq4_4'),
    ('performance_canary',2,'BanditRL.OnlineAdaptiveBenchmark.source_theorem4_14_infimum'),
    ('performance_canary',3,'BanditRL.OnlineAdaptiveBenchmark.source_theorem4_14_infimum'),
    ('zero_energy_canary',4,'BanditRL.OnlineAdaptiveOSD.regret_bound'),
    ('zero_diameter_canary',4,'BanditRL.OnlineAdaptiveOSD.regret_bound'),
    ('prefix_canary',0,'BanditRL.OnlineAdaptiveOSD.state_prefix'),
    ('trace_canary',2,'BanditRL.OnlineAdaptiveOSD.output_succ'),
    ('trace_canary',4,'BanditRL.OnlineAdaptiveOSD.output_succ'),
    ('feedback_energy',1,'BanditRL.OnlineAdaptiveOSD.energy_eq_sum')]
a=exporter.index('  for (name,index) in #[')
b=exporter.index(' do\n',a)
exporter=exporter[:a]+'  for (name,index,required) in #[\n'+',\n'.join(
    '      (`AdaptiveProbe.'+name+','+str(index)+',`'+parent+')' for name,index,parent in expected)+']'+exporter[b:]
exporter=exporter.replace('    let required := `BanditRL.OnlineAdaptivePotential.weighted_potential_sum\n','')
exporter=exporter.replace('Direct TYPE/VALUE constants in three selected full declarations and four independently selected inequality conjunction branches (including strictgap via C3), substituting local lets/removing metadata/id. Presence does not certify proof necessity or occurrence counts; no full transitive graph, algorithm guarantee or chapter denominator.',
    'Seven complete actual canary declaration TYPE/VALUEs and ten selected conjunction VALUEs, substituting lets/removing metadata/id. Branch occurrence is not necessity or a complete dependency graph; no combined package/chapter acceptance.')
write(RUN/'ExportAlgorithmCanaryValuesV1.lean',exporter)
capture('algorithm-canary-value-export-v1','lake','env','lean','--run',RUN/'ExportAlgorithmCanaryValuesV1.lean',
    RUN/'algorithm-canary-values-native-v1.json')
data=load(RUN/'algorithm-canary-values-native-v1.json')
assert len(data['nodes'])==7 and len(data['selected_conjuncts'])==10
assert all(row['required_present'] for row in data['selected_conjuncts'])
write(RUN/'algorithm-canary-direct-parent-checks-v1.json',dict(expected_selected_branches=expected,
    actual_VALUE_sha256=sha(RUN/'algorithm-canary-values-native-v1.json'),all_expected_found=True,
    all_focused_successes=successes,full_public=True,standard_axioms_only=True,
    boundary='Complete source-facing numerical propositions applied publicly; selected actual branch occurrences only. Distinct BODY review/full package gates open.'))
capture('algorithm-canary-compiled-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py',
    'trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','compiled',
    '--attempt-id','algorithm-canary-bodies-v1','--harness','hierarchical','--progress-class','compiled-leaf',
    '--obligations-before','7','--obligations-after','7','--verifier-evidence',RUN/'algorithm-canary-public-probe-v1.json',
    '--verifier-evidence',RUN/'algorithm-canary-values-native-v1.json',
    '--notes','Seven complete actual-run canary statements; sequential focus/full public/standard axioms/fences/ten selected VALUE branches. Distinct BODY review and combined gates open.')
print('Full seven canaries/public/standard axioms/fences/ten selected actual branch parents verified.',flush=True)
