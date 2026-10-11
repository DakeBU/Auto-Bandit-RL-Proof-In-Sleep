from common import *
import gzip
prior_runs=['online-ch2-adaptive-summation-20261010','online-ch2-adaptive-energy-20261010']
checked=[]
for pr in prior_runs:
    receipt=ROOT/'runs'/pr/'registry-inspected-v1.json'
    d=load(receipt)
    site=ROOT/'tmp'/('online-ch2-adaptive-energy-site-v1' if 'energy' in pr else 'online-ch2-adaptive-summation-site-v1')
    rp=site/'books/registry.json';reg=load(rp)
    assert sha(rp)==d['registry_sha256'] and len(reg['nodes'])==d['total_nodes'] and reg['source_commit']==d['source_commit']
    assert subprocess.run(['git','merge-base','--is-ancestor',reg['source_commit'],BASE],cwd=ROOT).returncode==0
    checked.append(dict(receipt=rows([receipt])[0],registry=rows([rp])[0],source_commit=reg['source_commit'],nodes=len(reg['nodes']),source_cards=d['source_cards']))
selected=checked[-1]
assert subprocess.run(['git','merge-base','--is-ancestor',checked[0]['source_commit'],selected['source_commit']],cwd=ROOT).returncode==0
write(RUN/'delivery-registry-baseline-20261011-v1.json.gz',gzip.compress(Path(selected['registry']['path']).read_bytes(),mtime=0))
plan=RUN/'exact-integration-proposal-20261011-v5.json'
mapping=load(RUN/'shared-book-mapping-proposal-20261011-v2.json')
config=dict(plan=rows([plan])[0],review_required='Favorable exact plan SHA binding, supplied explicitly at execution; no script may infer approval from compilation.',baseline_candidates_checked=checked,registry_baseline=selected,registry_compressed=rows([RUN/'delivery-registry-baseline-20261011-v1.json.gz'])[0],new_registry_ids=[r['shared_registry_id'] for r in mapping['canonical_declarations']],expected_total=selected['nodes']+len(mapping['canonical_declarations']),expected_source_cards=selected['source_cards']+3,structural_counts=mapping['structural_counts'],origin_main_at_preparation=subprocess.check_output(['git','rev-parse','origin/main'],cwd=ROOT,encoding='utf8').strip(),base=BASE,branch=BRANCH,root_receipts=['combined-root-20261011-v1.json','combined-Tests-20261011-v1.json'],axiom_receipts=['actual-step-public-probe-v1.json','algorithm-canary-public-probe-v1.json','benchmark-public-probe-v2.json','bootstrap-public-probe-v1.json','causal-state-public-probe-v1.json','parent-public-probe-v1.json','potential-canary-public-probe-v1.json','potential-public-probe-v1.json','specialization-public-probe-v1.json'],owned_canonical_scope=['BanditRLProof/OnlineAdaptivePotential.lean','BanditRLProof/OnlineAdaptiveOSD.lean','BanditRLProof/OnlineAdaptiveBenchmark.lean','Tests/OnlineAdaptivePotentialCanary.lean','Tests/OnlineAdaptiveOSDCanary.lean','BanditRLProof.lean','Tests.lean','website/content/chapters.json','website/content/readings.json','website/content/highlights.json','docs/contracts/online-book-v1/coverage.json','research-wiki/contribution-contracts/'+TASK+'.json'],forbidden_script_actions=['git add/commit/push','canonical file mutation','native acceptance','deployment','worktree retirement'],stage='prepared-only')
write(RUN/'delivery-preparation-config-20261011-v1.json',config)
print('Read-verified baseline:',selected['nodes'],'at',selected['source_commit'],'expected candidate',config['expected_total'],'cards',config['expected_source_cards'])
