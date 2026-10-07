from common_accepted_v1 import *
accepted_fixed()
pr=load(RUN/'created-PR-v1.json')
assert pr['state']=='open' and pr['draft'] and not pr['merged']
assert not load(RUN/'app-attach-v1.json').get('isError')
for label in ['branch-push-v1','draft-PR-create-v1','contributor-publication-v1','scoped-diff-publication-v5','source-scope-publication-v1']:
    assert load(RUN/(label+'-exit.json'))['exit_code']==0
current=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/'+str(pr['number'])]))
assert current['head']['sha']==pr['head']['sha'] and current['base']['ref']==BASE_BRANCH and current['draft'] and not current['merged']
canonical=Path('E:/ABRL/research')
ch=subprocess.check_output(['git','-C',str(canonical),'rev-parse','HEAD'],encoding='utf8').strip()
cs=subprocess.check_output(['git','-C',str(canonical),'status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
assert not cs and ch==subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf8').strip()
boundary=dict(source_package_accepted=True,source_subobligation_closed='C1-NOREGRET',source_closures_this_package=1,
    chapter_complete=False,goal_complete=False,PR=current['html_url'],PR_number=current['number'],PR_state='OPEN-DRAFT-unmerged',
    PR_creation_source_head=pr['head']['sha'],stacked_base_PR=191,stacked_base_exact_head=BASE,
    canonical_head=ch,canonical_clean=True,merged=False,deployed=False,main_live_updated=False,
    temporary_checkout='E:/ABRL/worktrees/research-online-book',checkout_retained_for_active_total_goal=True,
    unique_evidence_preserved=True,final_DIRECT_remote_REST_and_raw_audit_required=True)
write(RUN/'delivery-obligations-overlay-v1.json',dict(remaining_required=load(RUN/'accepted-decision-v1.json')['remaining_required'],
    chapter1_source_items=16,chapter1_required_proof_total=None,chapters3_16='unenumerated',
    historical_acceptance_and_all_raw_receipts_preserved=True,
    credentials='Per-command GH research credential helper; global login/config unchanged',**boundary))
write(RUN/'delivery-handoff-v1.md','C1-NOREGRET source reconciliation accepted; draft PR'+str(pr['number'])+' delivered on exact OPEN/unmerged PR191 stack. Nine derived proofs, three definitions, three reused proofs,15canaries; conditional finite convergence and negative limits preserved; signed unbounded fixed affine stream only. Actual postcomment combined root/Tests/harness,34kernel/type/statement/value, source/reader/registry/site/pixel and distinct FINAL gates passed. Review entries: accepted-decision-v1.json and final-reader-review-v1.md. All source/API/proof/audit/native/contributor failures retained, including vacuous contributor N/A and exact hash-bound raw whitespace exceptions. Chapter1/Chapter2/program remain incomplete; five other main-relative source audits unwaived. Active checkout retained. Final metadata push and DIRECT raw/local/remote/REST audit required immediately.\n')
for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']:
    path=Path(folder)/(TASK+'.md')
    path.write_bytes(path.read_bytes()+('\n\nDraft PR'+str(pr['number'])+' delivered, OPEN/unmerged, exact PR191 stack. Only C1-NOREGRET accepted. Delivery overlay and final DIRECT audit are separate; total Goal ACTIVE, this checkout retained for continuing work.\n').encode('utf8'))
gate('contributor-delivery-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-delivery-v5',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v5.py','delivery-v5')
gate('source-scope-delivery-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v3.py','delivery-v1')
accepted_fixed()
for command in [['git','add','--',*load(RUN/'owned-commit-paths-v2.json')],['git','commit','-m','Record no-regret draft PR delivery and remaining whole-book obligations']]:
    result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print('\n'.join(result.stdout.decode('utf8',errors='replace').splitlines()[-5:]),flush=True)
    assert result.returncode==0,command
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
print('Delivery commit',subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip(),'; next scoped push and direct raw audit.')
