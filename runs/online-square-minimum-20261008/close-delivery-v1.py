from common_accepted_v1 import *
from importlib.machinery import SourceFileLoader

delivery = SourceFileLoader('deliver_reviewed_v1', str(RUN / 'deliver-reviewed-v1.py')).load_module()
commit_owned = delivery.commit_owned

accepted_fixed()
pr = load(RUN / 'created-PR-v1.json')
assert pr['number'] == 193 and pr['draft'] and not pr['merged']
assert not load(RUN / 'app-attach-v1.json')['isError']
current = json.loads(subprocess.check_output(['gh', 'api', 'repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/193']))
assert current['head']['sha'] == pr['head']['sha'] and current['draft'] and current['state'] == 'open' and not current['merged']
assert current['base']['ref'] == BASE_BRANCH
canonical = Path('E:/ABRL/research')
canonical_head = subprocess.check_output(['git', '-C', str(canonical), 'rev-parse', 'HEAD'], encoding='utf8').strip()
assert not subprocess.check_output(['git', '-C', str(canonical), 'status', '--porcelain', '--untracked-files=all'], encoding='utf8').strip()
assert canonical_head == subprocess.check_output(['git', 'rev-parse', 'origin/main'], encoding='utf8').strip()
boundary = dict(source_package_accepted=True, source_subobligation_closed='C1 pathwise square-minimum hinge',
    source_closures_this_package=1, chapter_complete=False, goal_complete=False, PR=current['html_url'], PR_number=193,
    PR_state='OPEN-DRAFT-unmerged', PR_creation_source_head=pr['head']['sha'], stacked_base_PR=192, stacked_base_exact_head=BASE,
    canonical_head=canonical_head, canonical_clean=True, merged=False, deployed=False, main_live_updated=False,
    temporary_checkout='E:/ABRL/worktrees/research-online-book', checkout_retained_for_active_total_goal=True,
    unique_evidence_preserved=True, final_DIRECT_remote_REST_and_raw_audit_required=True)
write(RUN / 'delivery-obligations-overlay-v1.json', dict(
    remaining_required=load(RUN / 'accepted-decision-v1.json')['remaining_required'],
    chapter1_source_items=16, chapter1_required_proof_total=None, chapters3_16='unenumerated',
    historical_acceptance_and_all_raw_receipts_preserved=True,
    credentials='Per-command GH research credential helper; global login/config unchanged', **boundary))
write(RUN / 'delivery-handoff-v1.md',
    'Six frozen derived square-minimum terminals and one full definition accepted; draft PR193 delivered, OPEN/unmerged on exact PR192 stack. '
    'Actual mean feasibility/IsLeast produces the generally infinite interval loss-image infimum; signed same-trace regret identity/order and two existing actual first-half strict-past FTL guarantees preserved. '
    'T0 empty extension without uniqueness; T>0 performance, finite negative signed canary, no expectation/minimum exchange. '
    'Actual root9096/Tests9251/harness472skip7, committed contributor5productionpaths1contract,38kernel/26guards/16VALUEpairs/20canaries2fixtures, '
    'clean47c6a03 local site10906old registryIDsURLsHashes+7new,12actual pixels and distinct CONTRACT/BODY/FINAL R1–R8 passed; separate native acceptance passed. '
    'All observed operational failures/raw evidence retained. Original16C1items/proof-totalnull, expected fixed-loss minimum and causal IID cumulative variance next, five main-relative source audits unwaived, '
    'C1/C2/program incomplete,3–16unenumerated/necessaryappendicesrequired. No main/live/merge/deploy; active checkout retained. Final metadata push/DIRECT audit follows.\n')
for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index']:
    p = Path(folder) / (TASK + '.md')
    p.write_bytes(p.read_bytes() + ('\n\nDraft PR193 delivered, OPEN/unmerged, exact PR192 stack. Only bounded pathwise square-minimum hinge accepted; '
        'expected fixed-loss minimum/causal IID variance and whole C1/program remain required. Delivery overlay and final DIRECT audit separate; active checkout retained.\n').encode('utf8'))
gate('contributor-delivery-v1', sys.executable, '-B', '-X', 'utf8', 'tools/check_contributor_contract.py', '--base', BASE)
assert 'affected production paths: 5' in (RUN / 'contributor-delivery-v1.log').read_text(encoding='utf8')
gate('scoped-diff-delivery-v2', sys.executable, '-B', '-X', 'utf8', RUN / 'check-scoped-diff-v2.py', 'delivery-v2')
gate('source-scope-delivery-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'audit-scope-v2.py', 'delivery-v1')
accepted_fixed()
commit_owned('Record square-minimum draft PR193 delivery and remaining book obligations')
print('Final metadata push and no-file-write DIRECT audit required next.')
