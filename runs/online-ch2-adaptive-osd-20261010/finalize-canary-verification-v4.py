from common import *
import re
public=ROOT/'Tests/OnlineAdaptiveOSDCanary.lean'
assert sha(public)=='4b62e01f4f57bce6a3ca45bf8bc021a9c7fceab61fdabefee535306c1e27c905'
headers=load(CONTRACT/'algorithm-canary-stabilized-v1.json')['exact_headers']
values=RUN/'algorithm-canary-values-native-v4.json';data=load(values)
assert len(data['nodes'])==7 and len(data['selected_conjuncts'])==10 and all(r['required_present'] for r in data['selected_conjuncts'])
probe=load(RUN/'algorithm-canary-public-probe-v1.json');assert probe['actual_exit']==0
out=base64.b64decode(probe['stdout_base64']).decode('utf8')
audits=re.findall(r'depends on axioms: \[(.*?)\]',out)
assert len(audits)==7 and all(set(a.split(', ')).issubset({'propext','Classical.choice','Quot.sound'}) for a in audits)
focused={}
for name in headers:
    successes=[p for p in RUN.glob('algorithm-canary-'+name+'-focused-build-v*.json') if load(p)['actual_exit']==0]
    assert successes;focused[name]=rows(successes)
    for suffix in ['-fence-v1.json','-safe-verify-v1.json']:
        assert load(RUN/('algorithm-canary-'+name+suffix))['actual_exit']==0
write(RUN/'algorithm-canary-direct-parent-checks-v4.json',dict(production=rows([public]),actual_VALUE=rows([values]),extractor=rows([RUN/'ExportAlgorithmCanaryValuesV4.lean']),actual_export=rows([RUN/'algorithm-canary-value-export-v4.json']),all_focused_successes=focused,full_public=True,standard_axioms_only=True,selected_branch_count=10,all_expected_found=True,boundary='Actual selected lexical VALUE subexpressions after let/beta/id normalization and local lambda/And eliminator continuation traversal. No closed independent subproof, necessity or complete transitive graph claim. Whole package/source/chapter acceptance remains independent.'))
files=[public,RUN/'algorithm-canary-BODY-frozen-v1.lean.txt',RUN/'algorithm-canary-BODY-proof-context-v1.json',CONTRACT/'algorithm-canary-stabilized-v1.json',CONTRACT/'algorithm-canary-context-draft-v2.lean.txt',RUN/'AlgorithmCanaryPublicProbeV1.lean',RUN/'algorithm-canary-public-probe-v1.json',RUN/'algorithm-canary-direct-parent-checks-v4.json',values,RUN/'ExportAlgorithmCanaryValuesV4.lean',RUN/'algorithm-canary-value-export-v4.json',RUN/'algorithm-canary-value-export-v1.json',RUN/'algorithm-canary-value-export-v2.json',RUN/'algorithm-canary-value-diagnostic-v3.json',RUN/'algorithm-canary-exporter-repair-v2.json',RUN/'algorithm-canary-exporter-repair-v4.json']
files += list(RUN.glob('algorithm-canary-*-fence-native-v1.json'))+list(RUN.glob('algorithm-canary-*-safe-verify-v1.json'))
write(RUN/'algorithm-canary-verification-manifest-v4.json',dict(files=rows(files),production_sha256=sha(public),seven_full_public_statements=True,seven_standard_axiom_audits=True,seven_fences_and_safe_verifies=True,ten_actual_lexical_branch_occurrences=True,original_v1_verifier_status='failed at original extractor after successful public/fences; retained',resumption='v4 extractor succeeds; original failures retained; original file unmodified',scope='Local compiler/public/fence/occurrence evidence only. Distinct source/BODY review and combined integration/harness/site gates pending.'))
capture('algorithm-canary-compiled-trial-v4',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','compiled','--attempt-id','algorithm-canary-bodies-v4','--harness','hierarchical','--progress-class','compiled-leaf','--obligations-before','7','--obligations-after','7','--verifier-evidence',RUN/'algorithm-canary-verification-manifest-v4.json','--verifier-evidence',values,'--notes','Seven whole canaries; public/axioms/fences and10syntactic selected VALUE branches verified. Extractor failures retained. Independent source/BODY, combined gates and chapter obligations remain separate.')
print('Manifest SHA256 '+sha(RUN/'algorithm-canary-verification-manifest-v4.json'))
