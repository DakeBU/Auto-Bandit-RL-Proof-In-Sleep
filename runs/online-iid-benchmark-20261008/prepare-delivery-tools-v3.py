from common_integrated_v2 import *

fixed_integrated()
prior = ROOT/'runs/online-square-minimum-20261008'
text = (prior/'deliver-reviewed-v1.py').read_text(encoding='utf8')
for old, new in [('common_accepted_v1','common_accepted_v3'), ('native-acceptance-overlay-v1','native-acceptance-overlay-v3'),
    ('final-reader-receipt-v1','final-reader-receipt-v3'), ('pulls/192','pulls/193'),
    ('source-scope-pre-publication-v1','source-scope-pre-publication-v3'), ("'pre-publication-v1'", "'pre-publication-v3'"),
    ('scoped-diff-pre-publication-v2','scoped-diff-pre-publication-v3'), ('check-scoped-diff-v2.py','check-scoped-diff-v7.py'),
    ("'pre-publication-v2'", "'pre-publication-v3'"), ('prospective-pr-title-v1','prospective-pr-title-v3'),
    ('prospective-pr-body-v1','prospective-pr-body-v3'), ('PR-payload-v1','PR-payload-v3'),
    ('Accept reviewed square-minimum package and preserve local reader evidence','Accept the repaired IID package and preserve distinct FINAL evidence'),
    ('contributor-pre-publication-v2','contributor-pre-publication-v3'),
    ('Record the final nonvacuous square-minimum contributor gate','Record the final nonvacuous IID contributor gate'),
    ('branch-push-v1','branch-push-v3'), ('draft-PR-create-v1','draft-PR-create-v3'), ('created-PR-v1','created-PR-v3')]:
    assert old in text, old
    text = text.replace(old, new)
stage = '''def stage_owned():
    paths = current_owned_paths()
    globals_ = {'MANIFEST.md', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl'}
    raw = [p for p in paths if p not in globals_]
    for start in range(0, len(raw), 48):
        child = subprocess.run(['git', '-c', 'core.autocrlf=false', 'add', '--']+raw[start:start+48], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert child.returncode == 0
    globals_changed = [p for p in paths if p in globals_]
    if globals_changed:
        assert subprocess.run(['git','add','--']+globals_changed, stdout=subprocess.PIPE, stderr=subprocess.STDOUT).returncode == 0
    for p in raw:
        assert subprocess.check_output(['git','show',':'+p]) == Path(p).read_bytes()
    for p in globals_changed:
        assert subprocess.check_output(['git','show',':'+p]).startswith(subprocess.check_output(['git','show',BASE+':'+p]))

'''
text = text.replace("if __name__ == '__main__':", stage+"if __name__ == '__main__':")
text = text.replace("    gate('source-scope-pre-publication-v3'", "    stage_owned()\n    gate('source-scope-pre-publication-v3'")
write(RUN/'deliver-reviewed-v3.py', text)
text = (prior/'final-direct-audit-v1.py').read_text(encoding='utf8')
text = text.replace('common_accepted_v1','common_accepted_v3').replace('pulls/193', "pulls/' + str(load(RUN / 'created-PR-v3.json')['number']) + '")
text = text.replace('prospective-pr-body-v1','prospective-pr-body-v3').replace("PR=193", "PR=pr['number']")
write(RUN/'final-direct-audit-v3.py', text)
write(RUN/'close-delivery-v3.py', '''from common_accepted_v3 import *
from importlib.machinery import SourceFileLoader

delivery = SourceFileLoader('deliver_reviewed_v3', str(RUN/'deliver-reviewed-v3.py')).load_module()
accepted_fixed()
pr = load(RUN/'created-PR-v3.json')
number = pr['number']
assert pr['draft'] and not pr['merged']
assert not load(RUN/'app-attach-v3.json')['isError']
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
write(RUN/'delivery-obligations-overlay-v3.json', dict(remaining_required=load(RUN/'accepted-decision-v3.json')['remaining_required'],
    chapter1_source_items=16, chapter1_required_proof_total=None, chapters3_16='unenumerated',
    historical_acceptance_rejection_and_all_raw_receipts_preserved=True,
    credentials='Per-command GH research credential helper; global login/config unchanged', **boundary))
write(RUN/'delivery-handoff-v3.md', 'Eight frozen v2 derived proofs/two definitions accepted after distinct rejected FINALv2/F1F2 reader-only repair and fresh FINALv3. '
    'Draft PR'+str(number)+' delivered OPEN/unmerged, exact PR193 stack. Actual min E/feasiblemean/IsLeast beforecsInf and a.s.-supported strict-past causal producers preserved. '
    'T0 no uniqueness/T>0 finite averages/knownmean oracle; genuine fair IID T2 min E1/2 versus E min1/4/meanPredict excess1/4/illegal current-target trace-1/2. '
    'Root9097/Tests9253/harness472skip7/contributor5paths1contract/53kernel/36guards/26VALUEpairs/28canaries5fixtures2probability proofs; '
    'clean reader-repair v9 local site10913oldshared registry IDsURLsHashes+10new/14current ROOT+distinct FINAL views; originalR1–R9 and native acceptance pass. '
    'Full unexcluded diffexit2/12individually bound evidence/protocol files; scoped pass, twofrozenhelperEOFexceptions disclosed/reviewed. '
    'All failures/rejections preserved. Original16C1items/proof-totalnull, randomized/external-seed/general-filtration and asymptotic-success equivalence REQUIRED next; '
    'old5main sourceaudits unwaived/C1C2programopen/3–16unenumerated/appendicesrequired/GoalACTIVE. No main/live/merge/deploy; activecheckoutretained. Final metadata push/DIRECT audit follows.\\n')
for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']:
    p = Path(folder)/(TASK+'.md')
    p.write_bytes(p.read_bytes()+('\\n\\nDraft PR'+str(number)+' delivered OPEN/unmerged, exact PR193 stack; bounded deterministic IID core only. '
        'Randomized/filtration/asymptotic source coverage and whole chapter/program remain required. FinalDIRECT audit separate; checkoutretained.\\n').encode('utf8'))
gate('contributor-delivery-v3',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
assert 'affected production paths: 5' in (RUN/'contributor-delivery-v3.log').read_text(encoding='utf8')
delivery.stage_owned()
gate('scoped-diff-delivery-v3',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v7.py','delivery-v3')
gate('source-scope-delivery-v3',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v2.py','delivery-v3')
accepted_fixed()
delivery.commit_owned('Record IID draft PR'+str(number)+' delivery and required book obligations')
print('Final metadata push and no-file-write DIRECT audit required next.')
''')
print('Conditional own delivery tools prepared; no push, PR or native acceptance executed.')
