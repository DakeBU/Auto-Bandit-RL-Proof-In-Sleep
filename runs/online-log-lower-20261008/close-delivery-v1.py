from common_accepted_v1 import *
accepted_fixed()
pr=load(RUN/'created-PR-v1.json');assert pr['number']==191 and pr['state']=='open' and pr['draft'] and not pr['merged']
assert not load(RUN/'app-attach-v1.json').get('isError')
for label in ['branch-push-v2','draft-PR-create-v1','contributor-publication-v4','scoped-diff-publication-v4','source-scope-publication-v4','full-harness-final-v1']:
 assert load(RUN/(label+'-exit.json'))['exit_code']==0,label
current=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/191']))
assert current['head']['sha']==pr['head']['sha'] and current['base']['ref']==BASE_BRANCH and current['draft'] and not current['merged']
canonical=Path('E:/ABRL/research')
canonical_head=subprocess.check_output(['git','-C',str(canonical),'rev-parse','HEAD'],encoding='utf8').strip()
canonical_status=subprocess.check_output(['git','-C',str(canonical),'status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
assert not canonical_status and canonical_head==subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf8').strip()
boundary=dict(source_package_accepted=True,source_subobligation_closed='C1-LOG-UNAVOIDABLE',source_closures_this_package=1,chapter_complete=False,goal_complete=False,PR=current['html_url'],PR_state='OPEN-DRAFT-unmerged',PR_creation_source_head=pr['head']['sha'],stacked_base_PR=190,stacked_base_exact_head=BASE,canonical_head=canonical_head,canonical_clean=True,merged=False,deployed=False,main_live_updated=False,temporary_checkout='E:/ABRL/worktrees/research-online-book',checkout_retained_for_active_total_goal=True,unique_evidence_preserved=True,final_DIRECT_remote_REST_and_raw_audit_required=True)
write(RUN/'delivery-obligations-overlay-v1.json',dict(remaining_required=load(RUN/'accepted-decision-v1.json')['remaining_required'],chapter1_source_items=16,chapter1_required_proof_total=None,chapters3_16='unenumerated',historical_acceptance_and_all_raw_receipts_preserved=True,actual_credentials_repair='GH research account used only via per-command helper; global login/config unchanged',publication_prose_repair_receipt_sha256=sha(RUN/'publication-repair-receipt-v4.json'),**boundary))
write(RUN/'delivery-handoff-v1.md','C1 logarithmic lower source package accepted and draft PR191 delivered on PR190 exact stack. Combined Lean root/Tests, full harness472tests/seven skips, kernel/type/statement/value, source/reader/registry/site gates actually passed. Review entry: accepted-decision-v1.json and final-reader-review-v1.md. Retained raw audit membership failure and corrected DIRECT audit, PR prose rejection and separate accepted repair, missing local stacked ref and read-only ls-remote resolution, 403 cached anonymous credential failure and per-command GH credential resolution. Final metadata commit/push and no-write raw/local/remote/REST check remain immediately required. Chapter1/Chapter2/program remain incomplete. Checkout stays active.\n')
for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']:
 path=Path(folder)/(TASK+'.md');path.write_bytes(path.read_bytes()+b'\n\nDraft PR191 delivered, OPEN/unmerged, exact PR190 stack. Only C1-LOG-UNAVOIDABLE accepted. Delivery overlay and final DIRECT check are separate; total Goal remains ACTIVE and this checkout remains in use.\n')
gate('contributor-delivery-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-delivery-v1',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','delivery-v1')
gate('source-scope-delivery-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','delivery-v1')
accepted_fixed()
owned=load(RUN/'owned-commit-paths-v1.json')
for cmd in [['git','add','--',*owned],['git','commit','-m','Record draft PR191 delivery and retained whole-book obligations']]:
 child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);print('\n'.join(child.stdout.decode('utf8',errors='replace').splitlines()[-4:]),flush=True);assert child.returncode==0,cmd
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
print('Delivery commit',subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip(),'; next push with scoped GH helper then DIRECT no-write audit')
