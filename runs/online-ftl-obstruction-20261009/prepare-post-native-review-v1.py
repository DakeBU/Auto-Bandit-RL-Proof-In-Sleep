from common_accepted_v1 import *
accepted_fixed();assert load(RUN/'proof-obligations-accepted-v1.json')['derived_obligations_after']==0
for label in ['accepted-reviewer-trial-v1','accepted-lifecycle-v1','accepted-frontier-refresh-v1',
    'accepted-frontier-shadow-v1','accepted-memory-record-v1','accepted-retrieval-record-v1']:
    assert load(RUN/(label+'-exit.json'))['actual_exit']==0
for label,base in [('contributor-accepted-stack-v1',BASE),('contributor-accepted-main-v1','origin/main')]:
    gate(label,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base)
    text=(RUN/(label+'.log')).read_text(encoding='utf8')
    assert 'Contributor contract passed.' in text and ' - covered: '+PUBLIC.relative_to(ROOT).as_posix() in text
gate('delivery-base-PR201-v1','gh','pr','view','201','--json','number,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt,url')
basepr=load(RUN/'delivery-base-PR201-v1.log')
assert basepr['number']==201 and basepr['state']=='OPEN' and basepr['isDraft'] and basepr['mergedAt'] is None
assert basepr['headRefOid']==BASE and basepr['headRefName']=='codex/research-online-c1-source-reconcile'
write(RUN/'delivery-base-verification-v1.json',dict(basePR=201,actual=basepr,exact_base=BASE,
    base_unmerged_confirmed=True,main_or_live_updated=False))
indexed={}
def add(p):
    p=Path(p).resolve();assert p.is_file();indexed[p.as_posix()]=dict(path=p.as_posix(),sha256=sha(p))
for x in load(RUN/'FINAL-review-inputs-v1.json')['rows']:add(x['path'])
for folder in [RUN,CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts:add(p)
for p in [CONTRIBUTION,ROOT/'runs/lifecycle_sessions.jsonl']+APPEND_METADATA:add(p)
write(RUN/'post-native-review-inputs-v1.json',dict(rows=sorted(indexed.values(),key=lambda x:x['path']),
    fixed_input_count=len(indexed),exact_metadata_bindings=load(RUN/'accepted-metadata-bindings-v1.json'),
    actual_new_production_proofs=4,public_supporting_definitions=1,source_private_inventory_helpers=8,
    original_source_objects=16,unknown_required_proof_total=None,
    allowed_outputs=['post-native-review-v1.md','post-native-receipt-v1.json'],chapter_complete=False,goal_complete=False))
write(RUN/'post-native-review-packet-v1.md',
    'Independent POST-NATIVE audit: hash EVERY current indexed RAW input before/after. Verify favorable FINAL493, R1-R7, source/typedrepair/privateinventory boundaries. All public/canary/header/pin/root/Test/reader/site bytes remain same. Exact six OWNmanifest field changes/three identical append-only OWNtask suffixes/ONLY ownaccepted lifecycle journal suffix checked against original FINAL metadata snapshots and bindings. Original historicalguard artifacts/BODY390 preserved; exact BODY-approved rootimports remain, no silent weakening.\n\n'
    'Six actual original trial records (five compiled attempts including repairedD4 and one retained failedD4) copied into NEWaccepted-scoped-trials plus exactly ONE reviewer accepted4->0; original BODY/FINAL-bound trials and globaltrials unchanged. Actualnative reviewer/lifecycle/frontier-refresh/frontier-shadow/memory-record/retrieval-record real0, OWN output only. GlobalSGB frontier/memory and allfrozen retrievalindexes unchanged. OnlyfourDERIVED mathematicalterminals close; source-private8helpers notpublic endpoints. Original16/null and allhistoricaloverlays intact; fullChapter1 reconciliation/otherC1C2/C3-16/appendices/GoalACTIVE. No main/live claim.\n\n'
    'Current aftermetadata contributor logs BOTHbases nonempty andcoverednewPUBLIC. Actualroot9104/Tests9268/harness472tests7skips/28axes/15fences/applicablecleanlocal site6abb and10actualpersonalFINALpixel views remain applicable by exact hashes; no rerun/freshviews inferred. Registry10964COMPLETEoldrecords+5PUBLIC/8SOURCEPRIVATE total10977, initialv1count1 evidence-onlyv2repair0 retained. OriginalD4v1inference1/v2explicitrealzero0 preserved. Exact threeRAWcompiler-log whitespace exceptions only; no source/Test/reader/contract exemption. FreshPR201read verifies OPENdraft/unmerged exactBASE/headbranch.\n\n'
    'Review exactprospectivePRtitle/body and future OWNscoped commit/push/draft+immediateofficialappattachment only. No force/merge/deploy/retire. Output ONLY post-native-review-v1.md/post-native-receipt-v1.json: verdict/fixed_input_count/reviewed_files(includeindexSHA)/raw_input_checks(path/before_sha256/after_sha256/unchanged)/inputs_unchanged/report_sha256/required_blocking_repairs/authorized_delivery_scope(exacttitle/body hashes,branch/base andscope). Reuseddistinctautomatedactor/Astra mediumrequested/runtime_attestedfalse; no input/native/git/site mutations.\n')
print('Post-native current RAW inputs:',len(indexed),flush=True)
