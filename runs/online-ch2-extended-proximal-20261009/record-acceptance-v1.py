from publication_guard_v1 import *
import copy
fixed()
final = RUN / 'FINAL-review-v1.json'
review = load(final)
assert review['package_verdict'] in ['accepted', 'accepted-with-explicit-delta'] and not review['required_repairs']
for row in load(RUN / 'FINAL-inputs-v1.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
targets = load(CONTRACT / 'stabilized-v1.json')['targets']
names = [t['declaration'] for t in targets]
assert len(names) == 3
docs = [ROOT / d / (TASK + '.md') for d in ['tasks', 'proof-obligations', 'research-wiki/retrieval-index']]
native = [RUN / n for n in ['trials.jsonl', 'lifecycle-sessions.jsonl', 'lifecycle-state.json', 'own-artifact-journal.md']]
mutable = [*native, CONTRIBUTION, *docs]
before = {p: p.read_bytes() for p in mutable}
write(RUN / 'pre-native-exact-bytes-v1.json', dict(rows=[dict(path=p.as_posix(), sha256=sha(p), raw_base64=base64.b64encode(raw).decode('ascii')) for p, raw in before.items()], FINAL_sha256=sha(final), scope='Only FINAL-permitted OWN paths; immutable exact before bytes.'))
bound = ('Three frozen extended-loss bridge proofs, no new definitions; two complete public infinity canaries and one generated Test auxiliary separately inventoried. Proper global supports produce feasible finite-part convexity; actual EReal proximal minimum transports through shared finite-part order API and real proximal comparison retains both negative residuals. Full source X/interior/ambient-extension locality, attained current-loss causal recursion/interior invariants and sharp same-run fixed/variable telescopes including main-text fixed-step exercise remain REQUIRED/OPEN. All8Chapter2 forwards OPEN; Chapter2 partial/proof denominatornull; whole16Goal ACTIVE. No merge/deploy/main/live/CI/retirement.')
write(RUN / 'memory-digest-accepted-v1.md', '# ' + TASK + '\n\n' + bound + '\n\nDistinct bounded FINAL ' + sha(final) + '. Five full public VALUEs/ten standard-only axioms/five frozen headers/guards; selected6nodes/1241coalesced direct presences/12VALUEpairs, two genuinely selected Eq.mp numeric tails retain extended helper. Root9110/Tests9280/fullharness472tests7existing skips/exporter/checkpassed first current attempt0; tracked source beforehand. Own shadow mismatches[]/would_mutatefalse/globalSGB unchanged. Two nonempty contributor bases; clean isolated SITEv1 source2b929d03d7ace7c418986e429d0ccf317a2721c6,11002complete old records+3shared production nodes. Actual local-file desktop12formulas/zeroerrors/15originals inspected by root and distinctFINAL;4generated input files unchanged. Current full package whitespace0/no exceptions; parent historical RAW unchanged. Proof/selector/reader failures retained; minimum vs minimizer/center wording explicitly repaired, no old receipt rewriting. Compiler/native/semantic/site gates separately evidenced. Postnative and actual delivery pending.\n')
write(RUN / 'current-obligations-accepted-v1.json', dict(scope=bound, terminals=[dict(declaration=t['declaration'], statement_hash=t['statement_hash'], status='bounded-FINAL-accepted', proof_module_sha256=sha(PUBLIC)) for t in targets], public_canaries=2, new_definitions=0, generated_Test_auxiliaries=1, FINAL_sha256=sha(final), source_container_closed=False, chapter_proof_total=None, chapter_complete=False, goal_complete=False, native_post_review='pending', delivery='pending'))
notes = bound + ' Root records distinct source_reviewer FINAL ' + sha(final) + '. Counter3->0 ONLY three frozen bridge proofs, not source/chapter coverage. Postnative/delivery pending.'
args = [sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'reviewer', '--kind', 'review', '--status', 'accepted', '--run-id', RUN.name, '--attempt-id', 'three-frozen-extended-bridge-proofs-v1', '--progress-class', 'closed-frontier', '--reviewer-validated', '--obligations-before', '3', '--obligations-after', '0', '--notes', notes, '--verifier-evidence', final]
for name in names:
    args.extend(['--new-declaration', name])
capture('native-acceptance-trial-v1', *args)
payload = dict(scope=bound, terminals=[dict(declaration=t['declaration'], statement_hash=t['statement_hash']) for t in targets], FINAL_sha256=sha(final), recorded_by='/root from distinct /root/source_reviewer decision', bounded_obligations_before=3, bounded_obligations_after=0, chapter_proof_total=None, chapter_complete=False, goal_complete=False, post_native_review='pending', delivery='pending')
event('native-acceptance-event-v1', 'accepted', payload)
c = load(CONTRIBUTION)
oldc = copy.deepcopy(c)
allowed = [('semantic_roundtrip', 'remaining_semantic_delta'), ('verification', 'independent_review'), ('graph_contribution', 'visual_review')]
c['semantic_roundtrip']['remaining_semantic_delta'] = bound + ' Distinct staged CONTRACT/BODY/canary/reader and bounded FINAL accepted-with-explicit-delta ' + sha(final) + '; reader-v1/v2 rejected then v3 repaired. Reused automated actor history disclosed; no human/external/absolute-blind/runtime attestation. OWN postnative/delivery pending.'
c['verification']['independent_review'] = 'Distinct staged CONTRACT/BODY/canary/reader and bounded FINAL accepted-with-explicit-delta ' + sha(final) + '. Three frozen derived bridge proofs only; full source/Chapter2 open. Actual full gates/registry and15original desktop pixels reviewed; current full whitespace0/no exceptions. OWN postnative/concrete delivery pending. Requested Astra/medium staged automated actors with reused history; no human/external/absolute-blind/runtime attestation.'
c['graph_contribution']['visual_review'] = 'Selected6nodes=3production+2public canaries+1generated Test auxiliary,1241coalesced direct TYPE_VALUE presences/12required VALUE pairs and two genuinely selected Eq.mp numeric helper tails inspected. Complete shared registry11002unchanged records+3canonical production nodes. Actual local-file1440desktop12formulas/zeroerrors/strict geometry/15originals personally inspected by root and distinctFINAL; no HTTP/live/all-viewports/per-Book duplication claim.'
CONTRIBUTION.write_bytes((json.dumps(c, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
suffix = '\nBounded FINAL accepted: three frozen extended-loss bridge proofs/no new definitions, two full public infinity canaries/one generated Test auxiliary separately inventoried. FINAL SHA ' + sha(final) + '. OWN native3->0 only these three proof obligations. Combined Lean/fullharness/clean isolated SITEv1/sharedregistry/local-file15pixels passed. Source/general prescient/all8Ch2forwards REQUIRED/OPEN, Chapter2 partial/denominatornull, whole16Goal ACTIVE. Postnative/draftPR pending; historical pending entries retain stage meaning. No merge/main/live/CI/deploy/retirement/HTTP claim.\n'
for p in docs:
    p.write_bytes(before[p] + suffix.encode('utf8'))
capture('accepted-frontier-refresh-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'frontier-refresh', '--root-objective', 'Persistent Orabona Chapters1-16; ONLY three extended-loss bridge proofs accepted', '--leaf', TASK, '--kind', 'review', '--statement', bound, '--file', final, '--source-status', 'source-reviewed', '--leaf-status', 'accepted', '--dependency', 'review:bounded-extended-bridge-FINAL:accepted', '--trials', RUN / 'trials.jsonl', '--output', RUN / 'accepted-frontier-v1.json', '--shadow-status', 'pending')
_, out = capture('accepted-frontier-shadow-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'frontier-shadow', '--trials', RUN / 'trials.jsonl', '--memory-digest', RUN / 'memory-digest-accepted-v1.md', '--frontier', RUN / 'accepted-frontier-v1.json')
shadow = json.loads(out)
assert shadow['mismatches'] == [] and not shadow['would_mutate']
for p in native[:2]:
    assert p.read_bytes().startswith(before[p])
ts = native[0].read_bytes()[len(before[native[0]]):].decode('utf8').splitlines()
assert len(ts) == 1
tr = json.loads(ts[0])
assert (tr['task'], tr['role'], tr['kind'], tr['status']) == (TASK, 'reviewer', 'review', 'accepted')
assert tr['new_declarations'] == names and tr['notes'] == notes and tr['reviewer_validated'] is True
assert (tr['obligations_before'], tr['obligations_after']) == (3, 0) and tr['verifier_evidence'] == [str(final)]
es = native[1].read_bytes()[len(before[native[1]]):].decode('utf8').splitlines()
assert len(es) == 1
ev = json.loads(es[0])
state_before = json.loads(before[native[2]])
assert ev['session_id'] == TASK and ev['event_type'] == 'accepted' and ev['payload'] == payload
assert ev['sequence'] == state_before['next_sequence'] and ev['parent_id'] == state_before['current_entry_id']
expected = copy.deepcopy(state_before)
expected.update(next_sequence=state_before['next_sequence'] + 1, current_entry_id=ev['entry_id'])
assert load(native[2]) == expected and native[3].read_bytes() == before[native[3]]
reset = copy.deepcopy(c)
for a, b in allowed:
    reset[a][b] = oldc[a][b]
assert reset == oldc
for p in docs:
    assert p.read_bytes() == before[p] + suffix.encode('utf8')
changes = []
for row in load(RUN / 'FINAL-inputs-v1.json')['rows']:
    p = Path(row['path'])
    if sha(p) != row['sha256']:
        assert p in before and hashlib.sha256(before[p]).hexdigest() == row['sha256'], p
        changes.append(dict(path=p.as_posix(), before_sha256=row['sha256'], after_sha256=sha(p), exact_before_snapshot='pre-native-exact-bytes-v1.json'))
assert len(changes) == 7
write(RUN / 'post-native-root-audit-v1.json', dict(scope=bound, actual_trial_suffix=tr, actual_lifecycle_suffix=ev, state_exact_expected=True, own_journal_unchanged=True, contribution_changed_fields=allowed, docs_suffix=suffix, changed_FINAL_inputs=changes, all_other_FINAL_inputs_unchanged=True, shadow=shadow, root_self_audit_only=True, distinct_post_native_review='pending'))
write(RUN / 'PR-body-v1.md', '''Proves three reusable extended-loss proximal bridges. Properness and global subgradients at every feasible point produce convexity of the finite part on the feasible set. An actual extended-real proximal minimum transports through the existing finite-part order API; the resulting one-step comparison retains both negative Bregman residuals, both regularizer derivative hypotheses, and permits the center outside the feasible set and loss domain. No loss differentiability or global convexity of the finite-part extension is assumed.

Two public test families prove actual extended-real minima and global supports, infinity outside the domain, feasible convexity and failure of global finite-part convexity. They cover a nonquadratic regularizer with absolute loss and a boundary minimizer with an outside center. Both separately selected final numerical proof branches retain the new public comparison. Current and eight legacy reader fields explicitly distinguish minimizer p=0 from objective minimum values11/64 and1/2; the outside center is\u22121. Prior reader rejections and exact repairs remain recorded.

Validation: focused builds, five full public VALUEs/ten standard-only axiom outputs, five frozen headers/native guards, selected compiled graph6nodes/1241coalesced direct TYPE_VALUE presences/12required VALUE pairs and both selected Eq.mp numeric tails. Combined root9110/Tests9280 and full harness472tests with7existing skips/exporter/checkpassed, first current full attempt0; these are cached-inclusive job counts, not proof coverage. Two nonempty contributor bases and clean isolated site/check at source2b929d03d7ace7c418986e429d0ccf317a2721c6 passed. Shared registry preserves all11002 complete prior records and adds3canonical production theorems, no test or per-Book duplicates. Fifteen actual local-file desktop originals/formulas/geometry reviewed by root and a distinct staged automated FINAL reviewer. Current full package whitespace0/no exceptions; failures and warnings retained. Native and actual delivery receive separate review. No HTTP/live/later-head-site claim.

Stacked on OPEN draft unmerged PR #209, exact base65e21be78abfbd4255798e54265ce418651ef70f, branch codex/research-online-ch2-bregman. Three derived bridges lower a required Chapter2 prescient dependency; they do not complete Algorithm15.8/Theorem15.30 or accept Chapters6/15. Source X/interior/ambient-extension locality, attained current-loss causal recursion/interior invariants and sharp same-run fixed/variable telescopes including the main-text fixed-step exercise remain REQUIRED/OPEN. All8Chapter2 forwards remain open, Chapter2 partial/denominatornull, Chapters1\u201316 Goal ACTIVE. No merge/main/live/CI/deploy/retirement claim. Functor audit: none-found-with-reason.

Evidence: docs/contracts/online-ch2-extended-proximal-v1; runs/online-ch2-extended-proximal-20261009/FINAL-review-v1.md and SHA-bound JSON; research-wiki/contribution-contracts/ONLINE-CH2-EXTENDED-PROXIMAL-20261009.json.
''')
write(RUN / 'PR-plan-v1.json', dict(title='[Online Learning Ch2] Prove extended-loss proximal bridges', body_path=(RUN / 'PR-body-v1.md').as_posix(), body_sha256=sha(RUN / 'PR-body-v1.md'), base='codex/research-online-ch2-bregman', head=BRANCH, draft=True, parent_exact_head=BASE, merge=False, deploy=False, scope=bound))
fixed()
print('Actual OWN native acceptance and exact permitted metadata transitions audited; distinct postnative review pending.')
