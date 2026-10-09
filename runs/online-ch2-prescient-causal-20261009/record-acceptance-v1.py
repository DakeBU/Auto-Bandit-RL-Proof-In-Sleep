from publication_guard_v4 import *
import copy
fixed()
final = RUN / 'FINAL-review-v1.json'
review = load(final)
assert review['package_verdict'] in ['accepted', 'accepted-with-explicit-delta'] and not review['required_repairs']
for row in load(RUN / 'FINAL-inputs-v1.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
targets = load(CONTRACT / 'stabilized-v1.json')['targets']
names = [t['declaration'] for t in targets]
assert len(names) == 8
docs = [ROOT / d / (TASK + '.md') for d in ['tasks', 'proof-obligations', 'research-wiki/retrieval-index']]
native = [RUN / n for n in ['trials.jsonl', 'lifecycle-sessions.jsonl', 'lifecycle-state.json', 'own-artifact-journal.md']]
mutable = [*native, CONTRIBUTION, *docs]
before = {p: p.read_bytes() for p in mutable}
write(RUN / 'pre-native-exact-bytes-v1.json', dict(rows=[dict(path=p.as_posix(), sha256=sha(p), raw_base64=base64.b64encode(raw).decode('ascii')) for p, raw in before.items()], FINAL_sha256=sha(final), scope='Only FINAL-permitted OWN paths; immutable exact before bytes.'))
bound = 'Eight frozen derived proofs and two exact partial definitions: ambient-extension divergence locality at interior bases; current-whole-loss Option selection/recursion, actual minimum specifications, prefix causality, absorbing failure, conditional local-attainment completion, and a signed one-step comparison for the same actual consecutive returned states. Four complete nondegenerate public canaries separately audit two different nonsmooth/current losses and a nonquadratic generator, an outside initial center and boundary minimizer, strict closed regularizer without attained minimum, and invalid boundary differentiation. Full source X/interior regularity transport into a valid generated run, source interior conditions and sharp same-run fixed/variable cumulative bounds including the mandatory main-text fixed-step exercise remain REQUIRED/OPEN. All8Chapter2 forwards OPEN; Chapter2 partial/proof denominatornull; Chapters1-16 Goal ACTIVE. Not full Algorithm15.8/Theorem15.30, Chapters6/15 acceptance or source erratum. No merge/deploy/main/live/CI/retirement.'
write(RUN / 'memory-digest-accepted-v1.md', '# ' + TASK + '\n\n' + bound + '\n\nDistinct bounded FINAL ' + sha(final) + '. Twelve complete public proof VALUEs/26standard-only axiom outputs including2definitions/12frozen proof headers and native guards;14selected nodes/2027coalesced direct TYPE_VALUE presences/12required canaryVALUEpairs plus6productionpairs. Two genuinely selected Eq.mp numeric tails retain actual iterate_one_step. Fresh combined/root/Tests/fullharness inspected in full-harness-inspected-v2.json; source unchanged, boundary config rerun. OWN shadow no mismatch/globalSGB unchanged. Clean isolated SITEv3 source ' + load(RUN / 'clean-candidate-site-binding-v3.json')['actual_head'] + '; all11005 complete old registry records+10canonical production nodes. Actual file-URI desktop13formulas/zeroerrors/22originals personally reviewed by root and distinctFINAL;4generated inputs unchanged. Retained lost-premise rendering, browser filename collision, neighboring theorem contamination and rejected stale count plan; exact versioned repairs separately reviewed. Current full whitespace0/no exceptions. Compiler/native/semantic/site gates separately evidenced. Postnative and actual delivery pending.\n')
write(RUN / 'current-obligations-accepted-v1.json', dict(scope=bound, terminals=[dict(declaration=t['declaration'], statement_hash=t['statement_hash'], status='bounded-FINAL-accepted', proof_module_sha256=sha(PUBLIC)) for t in targets], public_canaries=4, new_definitions=2, generated_Test_auxiliaries=0, FINAL_sha256=sha(final), source_container_closed=False, chapter_proof_total=None, chapter_complete=False, goal_complete=False, native_post_review='pending', delivery='pending'))
notes = bound + ' Root records distinct source_reviewer FINAL ' + sha(final) + '. Counter8->0 ONLY eight frozen derived proofs, not source/chapter coverage. Postnative/delivery pending.'
args = [sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'reviewer', '--kind', 'review', '--status', 'accepted', '--run-id', RUN.name, '--attempt-id', 'eight-frozen-prescient-causal-proofs-v1', '--progress-class', 'closed-frontier', '--reviewer-validated', '--obligations-before', '8', '--obligations-after', '0', '--notes', notes, '--verifier-evidence', final]
for name in names:
    args.extend(['--new-declaration', name])
capture('native-acceptance-trial-v1', *args)
payload = dict(scope=bound, terminals=[dict(declaration=t['declaration'], statement_hash=t['statement_hash']) for t in targets], FINAL_sha256=sha(final), recorded_by='/root from distinct /root/source_reviewer decision', bounded_obligations_before=8, bounded_obligations_after=0, chapter_proof_total=None, chapter_complete=False, goal_complete=False, post_native_review='pending', delivery='pending')
event('native-acceptance-event-v1', 'accepted', payload)
c = load(CONTRIBUTION)
oldc = copy.deepcopy(c)
allowed = [('semantic_roundtrip', 'remaining_semantic_delta'), ('verification', 'independent_review'), ('graph_contribution', 'visual_review')]
c['semantic_roundtrip']['remaining_semantic_delta'] = bound + ' Distinct staged CONTRACT/BODY/canary/reader/range repairs and bounded FINAL ' + sha(final) + '; related actor history disclosed. No human/external/absolute-blind/runtime attestation. OWN postnative/delivery pending.'
c['verification']['independent_review'] = 'Distinct bounded FINAL ' + sha(final) + '. Eight derived proofs/two exact partial definitions and four full public canaries; actual full gates/sharedregistry/22original local-file pixels reviewed. Required full-source/cumulative/chapter obligations OPEN. OWN postnative/concrete delivery pending. Requested Astra/medium, staged related actors, no human/external/runtime attestation.'
c['graph_contribution']['visual_review'] = 'Selected14nodes=10production(8proofs/2defs)+4publicTests,2027coalesced direct TYPE_VALUE presences/12required canaryVALUEpairs plus6productionpairs; two genuinely selected Eq.mp numeric tails retain actual iterate_one_step. All11005complete old registry records unchanged+10canonical production nodes. Actual file URI1440desktop13sourceguide formulas/zeroerrors/strictgeometry/22originals personally reviewed by root and distinctFINAL; exact complete iterate source range excludes neighbor. No HTTP/live/all-viewports/per-Book duplication claim.'
CONTRIBUTION.write_bytes((json.dumps(c, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
suffix = '\nBounded FINAL accepted: ' + bound + ' FINAL SHA ' + sha(final) + '. OWN native8->0 only these eight proofs. Combined gates/full harness and clean isolated SITEv3/shared registry/actual file URI22pixels reviewed. Postnative/draftPR pending; historical pending entries retain stage meaning.\n'
for p in docs:
    p.write_bytes(before[p] + suffix.encode('utf8'))
capture('accepted-frontier-refresh-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'frontier-refresh', '--root-objective', 'Persistent Orabona Chapters1-16; ONLY eight prescient causal derived proofs accepted', '--leaf', TASK, '--kind', 'review', '--statement', bound, '--file', final, '--source-status', 'source-reviewed', '--leaf-status', 'accepted', '--dependency', 'review:bounded-prescient-causal-FINAL:accepted', '--trials', RUN / 'trials.jsonl', '--output', RUN / 'accepted-frontier-v1.json', '--shadow-status', 'pending')
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
assert (tr['obligations_before'], tr['obligations_after']) == (8, 0) and tr['verifier_evidence'] == [str(final)]
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
write(RUN / 'PR-body-v1.md', 'Proves a current-whole-loss partial Bregman recursion and its actual transition bound, plus divergence locality at interior bases. The producer selects a feasible attained current minimum when one exists and otherwise returns none; it has no future, horizon or comparator input. Prefix causality, actual predecessor/minimum extraction, absorbing failure and conditional local-attainment completion are proved. The one-step comparison derives both signed Bregman residuals from two actual consecutive returned states, reusing the accepted extended-loss producer. Classical choice is a mathematical partial selection, not an executable or measurable optimizer.\n\nFour complete public canaries exercise two distinct current losses with a nonquadratic regularizer and actual0.5->0->0.5 states; an outside initial center and boundary minimizer; a strict closed differentiable regularizer with no attained minimum; and extension agreement that permits interior-base locality but not boundary derivative validity. Both final numeric proof branches retain the new actual-transition theorem.\n\nValidation: focused builds;12complete public proof VALUE probes;26standard-only axiom outputs including2exact definitions; frozen statements/whole definitions and12native proof guards; selected compiled graph14nodes/2027coalesced direct TYPE_VALUE presences/12required canaryVALUEpairs plus6productionpairs. Fresh combined root/Tests/full harness and exporter/check markers are bound in full-harness-inspected-v2.json (472tests,7existing skips; cached-inclusive build jobs are not coverage). Two nonempty contributor bases and clean isolated SITEv3 build/check/shared registry pass:11005complete old records unchanged+10canonical production nodes. Root and distinct staged automated FINAL review all22actual local-file desktop originals. Lost-premise rendering, browser output collision, neighboring theorem contamination and stale-count rejection are retained with separately reviewed exact repairs; frozen Lean and generator remain unchanged. No HTTP/live/later-evidence-head fresh-site claim.\n\nStacked on OPEN draft unmerged PR #210, exact41f1fb26915b3bf7f84035393080991c38aeba64, branch codex/research-online-ch2-extended-proximal. Eight derived proofs/two definitions lower the required Chapter2 prescient dependency; they do not complete Algorithm15.8/Theorem15.30, accept Chapters6/15 or establish a source erratum. Full source X/interior valid-run transport and sharp same-run fixed/variable cumulative bounds, including the mandatory main-text fixed-step exercise, remain REQUIRED/OPEN. All8Chapter2 forward containers remain open, Chapter2partial/denominatornull, Chapters1-16 Goal ACTIVE. No merge/main/live/CI/deploy/retirement. Functor audit none-found-with-reason.\n\nEvidence: docs/contracts/online-ch2-prescient-causal-v1; runs/online-ch2-prescient-causal-20261009/FINAL-review-v1.md and SHA-bound JSON; research-wiki/contribution-contracts/ONLINE-CH2-PRESCIENT-CAUSAL-20261009.json.\n')
write(RUN / 'PR-plan-v1.json', dict(title='[Online Learning Ch2] Prove causal partial prescient Bregman updates', body_path=(RUN / 'PR-body-v1.md').as_posix(), body_sha256=sha(RUN / 'PR-body-v1.md'), base='codex/research-online-ch2-extended-proximal', head=BRANCH, draft=True, parent_exact_head=BASE, merge=False, deploy=False, scope=bound))
fixed()
print('Actual OWN native acceptance and exact permitted metadata transitions audited; distinct postnative review pending.')
