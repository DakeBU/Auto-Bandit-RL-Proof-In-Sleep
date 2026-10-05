"""Exact raw review bindings, with explicit authorized historical supersession."""
from pathlib import Path
import hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
snap={x['path']:x for x in load(run/'historical-raw-supersession-v2.json')['rows']}
resolved=[];count=0
for name,verdict in [('source-contract-receipt-v1.json','rejected'),
    ('source-contract-receipt-v2.json','accepted-with-explicit-delta'),
    ('public-body-receipt-v2.json','accepted-with-explicit-delta')]:
    receipt=load(run/name);assert receipt['verdict']==verdict
    assert sha(receipt['report'])==receipt['report_sha256'],name
    for row in receipt['reviewed_files']:
        current=sha(row['path'])
        if current!=row['sha256']:
            s=snap[row['path']]
            assert s['raw_sha256']==row['sha256']==sha(s['snapshot'])
            resolved.append(dict(receipt=name,path=row['path'],expected_sha256=row['sha256'],
                original_snapshot=s['snapshot'],current_sha256=current,
                reason='Authorized public import/source-interface comment; exact original bytes preserved and later current bytes reviewed separately.'))
        count+=1
for n in [1,2]:
    blind=load(run/('blind-receipt-v'+str(n)+'.json'))
    for k in ['input','report']:assert sha(blind[k]['path'])==blind[k]['sha256_raw_bytes']
    assert blind['actor']['task']=='/root/normal_blind' and blind['scope']['semantic_slots_per_target']==7
    assert not blind['scope'].get('source_identity_maps_proofs_compile_evidence_prior_judgments_other_files_read_this_pass',False)
old=load('docs/contracts/online-ogd-migration-v1/native-headers-v1.json');assert len(old)==16
for n,r in old.items():assert hashlib.sha256(lean_declaration_header(Path(r['file']),n).encode()).hexdigest()==r['statement_hash'],n
normalize=lambda s:' '.join(_strip_lean_comments(s).split())
for path in ['BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineGradientDescentVariable.lean']:
    assert normalize(Path(path).read_text(encoding='utf-8'))==normalize(Path(snap[path]['snapshot']).read_text(encoding='utf-8')),path
freeze=load(run/'freeze-review-v2.json');public=Path('BanditRLProof/OnlineGradientDescentSource.lean')
context=Path('docs/contracts/online-ogd-migration-v2/context.lean.txt')
assert sha(context)==freeze['context_sha256']
assert sha('docs/contracts/online-ogd-migration-v2/source-intent.md')==freeze['source_intent_sha256']
for n,h in freeze['headers'].items():
    assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
    fence=load(run/('public-fences/'+n+'.json'))
    assert fence['statement_hash']==h and fence['file']==public.as_posix()
bindings=load(run/'public-actual-bindings-v2.json')
assert sha(public)==bindings['public_module_sha256']
assert sha('Tests/OnlineGradientDescentSourceCanary.lean')==bindings['public_canary_sha256']
assert len(bindings['actual_named_lookup_and_axioms'])==75
assert all(set(xs)<={'propext','Classical.choice','Quot.sound'} for xs in bindings['actual_named_lookup_and_axioms'].values())
assert sha('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
result=dict(status='passed',review_raw_rows_verified=count,authorized_snapshot_resolutions=resolved,
    old16_headers_unchanged=True,old_fixed_and_variable_all_code_tokens_unchanged=True,
    new12_frozen_headers_unchanged=True,public_module_and_canary_exact_body_review_hashes=True,
    actual_axiom_names=75,blind_actor_separate=True,global_SGB_unchanged=True,
    boundary='Historical review bytes verified against exact authorized snapshots where imports/comments changed; no claim that live originals remained byte-identical. Final reader/package gate separate; whole Goal active.')
with (run/'review-history-audit-v2.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
print('Verified',count,'historical review rows;',len(resolved),'explicit exact snapshot resolutions; all old code/new headers unchanged.')
