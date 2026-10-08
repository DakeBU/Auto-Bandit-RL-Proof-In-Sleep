from common_accepted_v3 import *
from commit_owned_v2 import stage_owned, commit_owned

accepted_fixed()
post = reviewer_receipt('post-native-receipt-v4.json')
assert post['inputs_unchanged'] and post['fixed_input_count'] == 56
created = load(RUN/'actual-PR195-REST-v3.log')
proposal = load(RUN/'proposed-publication-v3.json')
publication = load(RUN/'publication-source-head-v3.json')
base = load(RUN/'actual-base-PR194-after-publication-v3.log')
assert created['head']['sha'] == publication['head']
assert created['base']['sha'] == BASE and created['base']['ref'] == BASE_BRANCH
assert created['state'] == 'open' and created['draft'] and not created['merged']
assert created['merged_at'] is None
assert created['title'] == Path(proposal['title_path']).read_text(encoding='utf8').rstrip('\n')
assert created['body'].encode('utf8') == Path(proposal['body_path']).read_bytes()
assert base['headRefOid'] == BASE and base['state'] == 'OPEN' and base['mergedAt'] is None
remote = (RUN/'actual-published-remote-head-v3.log').read_text(encoding='utf8').split()
assert remote == [publication['head'], 'refs/heads/'+BRANCH]
attachment = load(RUN/'official-app-PR195-attachment-v3.json')
assert attachment['url'] == created['html_url'] and not attachment['actual_result'].get('isError')
gate('actual-PR195-check-runs-v3','gh','api',
    'repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/commits/'+publication['head']+'/check-runs')
checks = load(RUN/'actual-PR195-check-runs-v3.log')
write(RUN/'delivery-obligations-overlay-v3.json', dict(
    status='Bounded independent-private-tape finite producer accepted and delivered as reviewable draft PR195',
    PR=195, url=created['html_url'], actual_head_at_creation=publication['head'],
    actual_remote_head_at_creation=remote[0], exact_base_PR=194, exact_base_head=BASE,
    exact_base_branch=BASE_BRANCH, branch=BRANCH, state_at_record='OPEN', draft=True, merged=False,
    exact_reviewed_title_and_body_bytes=True, official_app_attached=True,
    root_jobs=9098, Tests_jobs=9255, full_harness_tests=472, full_harness_skips=7,
    selected_kernel_checks=55, actual_direct_VALUE_pairs=26, named_canary_proofs=29,
    new_public_proofs=7, new_public_definitions=1, frozen_terminals_before=7, frozen_terminals_after=0,
    term_count_scope='Only frozen v2 private-tape derived terminal contract; no whole-source result count reduction',
    FINAL_receipt_sha256=sha(RUN/'final-reader-receipt-v3.json'),
    actual_native_receipt=load(RUN/'native-acceptance-overlay-v3.json'),
    actual_suffix_review_sha256=sha(RUN/'post-native-receipt-v4.json'),
    clean_applicable_site_source=load(RUN/'registry-v3.json')['source_commit'],
    preserved_shared_registry_IDs=10923, added_shared_registry_nodes=8,
    current_original_pixels_viewed_by_root_and_reviewer=13,
    full_unexcluded_whitespace_passed=False, full_unexcluded_whitespace_exit=2,
    exact_RAW_stdout_exceptions=5, production_Test_reader_contract_helper_exemptions=0,
    inherited_main_relative_five_source_audits_unwaived=True,
    remaining_required=['Universal-kernel/completed-information/AE-factorization source coverage audit',
        'Source asymptotic-success equivalence','Five old main-relative source-module audits',
        'Original16 C1 source objects/full C1 gate','Chapter2 remaining source obligations/full chapter gate',
        'Chapters3-16 source enumeration and proofs','Necessary appendix dependencies'],
    chapter1_source_items=16, chapter_mandatory_proof_total=None,
    whole_source_items_closed_by_this_package=0, chapter1_complete=False, chapter2_complete=False,
    chapters3_to16='unenumerated', goal_complete=False, main_updated=False, live=False,
    canonical_source='E:/ABRL/research', canonical_main_last_verified='6847b678a73db68dee5101d6f05c2453c1405afc',
    current_worktree=ROOT.as_posix(), worktree_retained_for_active_whole_book_goal=True,
    check_runs_at_publication=[dict(name=x['name'],status=x['status'],conclusion=x['conclusion']) for x in checks['check_runs']],
    later_evidence_commit_and_remote_head='Verify after evidence commit/push using stdout-only final audit; do not infer an unexecuted future head')))
write(RUN/'delivery-handoff-v3.md', '''# Private-tape finite IID producer: bounded draft delivery

Canonical source E:/ABRL/research; active checkout E:/ABRL/worktrees/research-online-book, branch codex/research-online-randomized-iid. Draft PR195 https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pull/195, base OPENdraft/unmerged PR194 exact b08f8312259ae10032b6318060e18911532d4610. Initial actual publication head is recorded in publication-source-head-v3.json; subsequent evidence-only commit/head is verified directly after push. Exact approved title/body and app attachment are checked against actual REST bytes.

Seven derived causal/interface proofs and one information definition accepted;29 named nondegenerate canaries/55 kernel checks/26 directVALUE pairs/36 fences, combined root9098/Tests9255/fullharness472tests7skips, scoped shadow/nonvacuous contributor/sharedregistry/current13pixels and distinct CONTRACT/BODY/FINAL/actual10metadata suffix review pass. Five exact SHA-bound raw stdout whitespace exceptions preserve original failures; full unexcluded diffexit2 and zero production/Test/reader/contract/helper exemptions are explicit. All original failed proof/audit/tracking/parser/reader/credential attempts are retained. Official gh credentials were used only per Git command after the unrelated cached Git account returned403; no global credential configuration changed.

Only the independent-private-tape/subordinate-information finite model is supported. Whole-process tape and jointly IID target independence are kept; legal cube-only every-seed feasibility, min expectedFIXED outsideE, same stream/prefix and emptyT0 are explicit. Universal-kernel/completed-information/AE-factorization source coverage audit and source asymptotic-success equivalence remain required, together with five old source-module audits, original16/null/fullC1/C2/3-16/appendices. No chapter or Goal completion, merge/deployment/main/live update or retirement. Active whole-book Goal continues with source asymptotic-success equivalence. Worktree and all shared links/runtime/stores are retained.
''')
stage_owned()
gate('source-scope-draft-delivery-v3',sys.executable,'-B','-X','utf8',RUN/'audit-owned-scope-v2.py','draft-delivery-v3')
gate('scoped-diff-draft-delivery-v3',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','draft-delivery-v3')
commit_owned('Record exact draft PR195 delivery, app attachment and retained source obligations')
head = subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
accepted_fixed()
print('Actual clean evidence head:',head)
print('DraftPR195 bounded package only; whole-book Goal active; no merge/live/retirement.')
