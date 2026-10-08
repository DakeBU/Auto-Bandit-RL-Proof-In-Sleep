from common_delivery_v5 import *
from importlib.machinery import SourceFileLoader

review=delivery_fixed()
delivery=SourceFileLoader('deliver_reviewed_v4',str(RUN/'deliver-reviewed-v4.py')).load_module()
pr=load(RUN/'created-PR-v4.json');number=pr['number'];assert number==194
assert not load(RUN/'app-attach-v4.json')['isError']
current=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/'+str(number)]))
assert current['head']['sha']==pr['head']['sha'] and current['draft'] and current['state']=='open' and not current['merged']
assert current['base']['ref']==BASE_BRANCH
assert current['title']==(RUN/'prospective-pr-title-v4.txt').read_text(encoding='utf8').strip()
assert current['body'].replace('\r\n','\n').strip()==(RUN/'prospective-pr-body-v4.md').read_text(encoding='utf8').strip()
gate('draft-PR-evidence-update-v5','gh','pr','edit',str(number),'--body-file',RUN/'prospective-pr-body-v5.md')
current=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/'+str(number)]))
assert current['head']['sha']==pr['head']['sha'] and current['draft'] and current['state']=='open' and not current['merged']
assert current['body'].replace('\r\n','\n').strip()==(RUN/'prospective-pr-body-v5.md').read_text(encoding='utf8').strip()
write(RUN/'delivery-PR-body-update-v5.json',dict(PR=194,body_sha256=sha(RUN/'prospective-pr-body-v5.md'),
    exact_remote_body_checked=True,title_branch_base_and_code_unchanged=True,initial_head=pr['head']['sha'],
    reviewer_receipt_sha256=sha(RUN/'delivery-reader-receipt-v5.json'),merged=False,chapter_complete=False,goal_complete=False))
canonical=Path('E:/ABRL/research')
canonical_head=subprocess.check_output(['git','-C',str(canonical),'rev-parse','HEAD'],encoding='utf8').strip()
assert canonical_head==subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf8').strip()
assert not subprocess.check_output(['git','-C',str(canonical),'status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
write(RUN/'delivery-obligations-overlay-v5.json',dict(PR=current['html_url'],PR_number=194,PR_state='OPEN-DRAFT-unmerged-appattached',
    stacked_base_PR=193,stacked_base_exact_head=BASE,canonical_head=canonical_head,canonical_clean=True,
    source_package_accepted=True,whole_source_items_closed=0,chapter1_source_items=16,chapter1_required_proof_total=None,
    remaining_required=load(RUN/'accepted-decision-v4.json')['remaining_required'],chapters3_16='unenumerated',
    original_FINAL_reviewed_12_evidence_exceptions_unchanged=True,delivery_reviewed_bound_evidence_exceptions=14,
    retained_failed_delivery_gate=True,metadata_body_update_distinctly_reviewed=True,
    chapter_complete=False,goal_complete=False,merged=False,deployed=False,main_live_updated=False,
    checkout_retained_for_active_total_goal=True,unique_evidence_preserved=True,final_metadata_push_DIRECT_required=True))
digest=('PR194 OPENdraft/unmerged/appattached, exact PR193 basebf9f896cdfebb2b836dacb01f3d4b209466c2100. '
    'Eight frozenv2 derived terminals/two definitions accepted; actual root9097/Tests9253/harness472skip7/53kernel/36guards/26VALUEpairs/28canaries5fixtures2probability proofs. '
    'Clean a15115609562ea163c9b95a3bd111cac2df74edc v9site/10913oldsharedregistry IDsURLsHashes+10new/14current actual ROOT+distinct reviewer views; '
    'CONTRACT186/BODY583/FINAL876 and R1–R9 native8->0 accepted; rejected FINALv2F1F2 andv3M1 retained. '
    'Postpublication GitHub stdout caused actual delivery whitespace failure; distinct64input metadata review accepts raw-only12->14 exceptions and exactoneparagraph PRbody update. '
    'Fullunexcluded diffexit2; scoped14passes; two original frozenhelperEOF findings reviewed, no production/reader/test/contract/otherhelper exemption. '
    'No math/reader change or additional Lean rerun claimed. Randomized/external-seed/general-filtration/asymptotic-equivalence/old5sourceaudits/fullC1C2/program required; '
    '16sourceitems/proof-totalnull/3–16unenumerated/appendicesrequired/GoalACTIVE. No main/live/merge/deploy/retirement; checkoutretained; final metadata push/DIRECT separate.')
write(RUN/'delivery-handoff-v5.md',digest)
for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']:
    p=Path(folder)/(TASK+'.md')
    p.write_bytes(p.read_bytes()+('\n\n## Actual delivery evidence repair\n\n'+digest+'\n').encode('utf8'))
gate('contributor-delivery-v5',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
text=(RUN/'contributor-delivery-v5.log').read_text(encoding='utf8')
assert 'affected production paths: 5' in text and 'changed contribution contracts: 1' in text
delivery.stage_owned()
gate('scoped-diff-delivery-v5',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-delivery-v5.py','delivery-v5')
gate('source-scope-delivery-v5',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v2.py','delivery-v5')
delivery_fixed()
delivery.commit_owned('Preserve reviewed PR194 delivery stdout and exact remaining book scope')
print('Clean local delivery commit; final metadata push and no-write DIRECT audit required.')
