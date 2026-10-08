from common_accepted_v4 import *
from importlib.machinery import SourceFileLoader

delivery = SourceFileLoader('deliver_reviewed_v4', str(RUN/'deliver-reviewed-v4.py')).load_module()
accepted_fixed()
pr = load(RUN/'created-PR-v4.json')
number = pr['number']
assert pr['draft'] and not pr['merged']
assert not load(RUN/'app-attach-v4.json')['isError']
current = json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/'+str(number)]))
assert current['head']['sha'] == pr['head']['sha'] and current['draft'] and current['state'] == 'open' and not current['merged']
assert current['base']['ref'] == BASE_BRANCH
canonical = Path('E:/ABRL/research')
canonical_head = subprocess.check_output(['git','-C',str(canonical),'rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','-C',str(canonical),'status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
assert canonical_head == subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf8').strip()
boundary = dict(source_package_accepted=True, bounded_subobligation_closed='Expected-fixed minimum / deterministic finite-history IID core',
    whole_source_items_closed=0, chapter_complete=False, goal_complete=False, PR=current['html_url'], PR_number=number,
    PR_state='OPEN-DRAFT-unmerged', PR_creation_source_head=pr['head']['sha'], stacked_base_PR=193, stacked_base_exact_head=BASE,
    canonical_head=canonical_head, canonical_clean=True, merged=False, deployed=False, main_live_updated=False,
    temporary_checkout='E:/ABRL/worktrees/research-online-book', checkout_retained_for_active_total_goal=True,
    unique_evidence_preserved=True, final_DIRECT_remote_REST_and_raw_audit_required=True)
write(RUN/'delivery-obligations-overlay-v4.json', dict(remaining_required=load(RUN/'accepted-decision-v4.json')['remaining_required'],
    chapter1_source_items=16, chapter1_required_proof_total=None, chapters3_16='unenumerated',
    historical_acceptance_rejection_and_all_raw_receipts_preserved=True,
    credentials='Per-command GH research credential helper; global login/config unchanged', **boundary))
write(RUN/'delivery-handoff-v4.md', 'Eight frozen v2 derived proofs/two definitions accepted after distinct rejected FINALv2/F1F2 reader-only repair and fresh FINALv4. '
    'Draft PR'+str(number)+' delivered OPEN/unmerged, exact PR193 stack. Actual min E/feasiblemean/IsLeast beforecsInf and a.s.-supported strict-past causal producers preserved. '
    'T0 no uniqueness/T>0 finite averages/knownmean oracle; genuine fair IID T2 min E1/2 versus E min1/4/meanPredict excess1/4/illegal current-target trace-1/2. '
    'Root9097/Tests9253/harness472skip7/contributor5paths1contract/53kernel/36guards/26VALUEpairs/28canaries5fixtures2probability proofs; '
    'clean reader-repair v9 local site10913oldshared registry IDsURLsHashes+10new/14current ROOT+distinct FINAL views; originalR1–R9 and native acceptance pass. '
    'Full unexcluded diffexit2/12individually bound evidence/protocol files; scoped pass, twofrozenhelperEOFexceptions disclosed/reviewed. '
    'All failures/rejections preserved. Original16C1items/proof-totalnull, randomized/external-seed/general-filtration and asymptotic-success equivalence REQUIRED next; '
    'old5main sourceaudits unwaived/C1C2programopen/3–16unenumerated/appendicesrequired/GoalACTIVE. No main/live/merge/deploy; activecheckoutretained. Final metadata push/DIRECT audit follows.\n')
for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']:
    p = Path(folder)/(TASK+'.md')
    p.write_bytes(p.read_bytes()+('\n\nDraft PR'+str(number)+' delivered OPEN/unmerged, exact PR193 stack; bounded deterministic IID core only. '
        'Randomized/filtration/asymptotic source coverage and whole chapter/program remain required. FinalDIRECT audit separate; checkoutretained.\n').encode('utf8'))
gate('contributor-delivery-v4',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
assert 'affected production paths: 5' in (RUN/'contributor-delivery-v4.log').read_text(encoding='utf8')
delivery.stage_owned()
gate('scoped-diff-delivery-v4',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v7.py','delivery-v4')
gate('source-scope-delivery-v4',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v2.py','delivery-v4')
accepted_fixed()
delivery.commit_owned('Record IID draft PR'+str(number)+' delivery and required book obligations')
print('Final metadata push and no-file-write DIRECT audit required next.')
