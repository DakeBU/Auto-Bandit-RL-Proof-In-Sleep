from publication_guard_v4 import *
import copy
fixed()
final = RUN / 'FINAL-review-v1.json'
review = load(final)
assert review['package_verdict'] in ['accepted', 'accepted-with-explicit-delta'] and not review['required_repairs']
for row in load(RUN / 'FINAL-inputs-v1.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
targets = load(CONTRACT / 'stabilized-v1.json')['targets']
for t in targets:
    t['statement_hash']=next(load(f)['statement_hash'] for f in CONTRACT.glob('*fence-v1.json') if load(f).get('declaration')==t['declaration'])
names = [t['declaration'] for t in targets]
assert len(names) == 5
docs = [ROOT / d / (TASK + '.md') for d in ['tasks', 'proof-obligations', 'research-wiki/retrieval-index']]
native = [RUN / n for n in ['trials.jsonl', 'lifecycle-sessions.jsonl', 'lifecycle-state.json', 'own-artifact-journal.md']]
mutable = [*native, CONTRIBUTION, *docs]
before = {p: p.read_bytes() for p in mutable}
write(RUN / 'pre-native-exact-bytes-v1.json', dict(rows=[dict(path=p.as_posix(), sha256=sha(p), raw_base64=base64.b64encode(raw).decode('ascii')) for p, raw in before.items()], FINAL_sha256=sha(final), scope='Only FINAL-permitted OWN paths; immutable exact before bytes.'))
bound = 'Five frozen conditional same-run cumulative proofs: actual consecutive Option outputs produce the common divergence sum; fixed and positive nonincreasing played steps yield sharp bounds retaining negative terminal and movement terms; strict generator convexity certifies terminal nonnegativity for the printed forms. Two complete16/22conjunct public canaries use actual distinct losses/nonquadratic generator and genuinely decreasing steps; four independently selected numeric proof branches retain the corresponding new production theorem. Full source X/interior generator and source loss hypothesis transport plus source valid-run wrapper remain REQUIRED/OPEN. All8Chapter2forwards OPEN, Chapter2partial/denominatornull, wholeChapters1-16GoalACTIVE. Not full Algorithm15.8/Theorem15.30/Chapter6/15/Chapter2 acceptance or source erratum. No merge/deploy/main/live/CI/retirement.'
write(RUN/'memory-digest-accepted-v1.md','# '+TASK+'\n\n'+bound+'\n\nDistinct bounded FINAL '+sha(final)+'. Seven complete public VALUEs/standard-only axiom lists,7frozenheaders/nativefences;7selectednodes/1885coalesced directTYPE_VALUE presences/8production+5canaryVALUEpairs/four selected Eq.mprnumericbranches. Actual combinedroot/Tests/fullharness in full-harness-inspected-v1; exact math/pins unchanged after applicable gate. Clean repaired SITEv2 source '+load(RUN/'clean-candidate-site-binding-v2.json')['actual_head']+';11015oldregistryrecords+5production=11020. Actual local-file desktop14formulas/12root+distinct originals, notHTTP/live/mobile. Reader ambiguity/13field approved repair, resolver missing-field failure and two prospective helper generator failures preserved. No acceptance helper executed before acceptedFINAL. Compiler/native/semantic/site gates separate; postnative/delivery pending.\n')
write(RUN/'current-obligations-accepted-v1.json',dict(scope=bound,terminals=[dict(declaration=t['declaration'],raw_UTF8_header_sha256=t['statement_sha256'],native_normalized_statement_hash=t['statement_hash'],status='bounded-FINAL-accepted',proof_module_sha256=sha(PUBLIC)) for t in targets],public_canaries=2,new_definitions=0,generated_Test_auxiliaries=0,FINAL_sha256=sha(final),source_container_closed=False,chapter_proof_total=None,chapter_complete=False,goal_complete=False,native_post_review='pending',delivery='pending'))
notes=bound+' Root records distinct source_reviewer FINAL '+sha(final)+'. Counter5->0 ONLY five frozen derived proofs, not source/chapter coverage. Postnative/delivery pending.'
args = [sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'reviewer', '--kind', 'review', '--status', 'accepted', '--run-id', RUN.name, '--attempt-id', 'five-frozen-prescient-cumulative-proofs-v1', '--progress-class', 'closed-frontier', '--reviewer-validated', '--obligations-before', '5', '--obligations-after', '0', '--notes', notes, '--verifier-evidence', final]
for name in names:
    args.extend(['--new-declaration', name])
capture('native-acceptance-trial-v1', *args)
payload = dict(scope=bound, terminals=[dict(declaration=t['declaration'], statement_hash=t['statement_hash']) for t in targets], FINAL_sha256=sha(final), recorded_by='/root from distinct /root/source_reviewer decision', bounded_obligations_before=5, bounded_obligations_after=0, chapter_proof_total=None, chapter_complete=False, goal_complete=False, post_native_review='pending', delivery='pending')
event('native-acceptance-event-v1', 'accepted', payload)
c = load(CONTRIBUTION)
oldc = copy.deepcopy(c)
allowed = [('semantic_roundtrip', 'remaining_semantic_delta'), ('verification', 'independent_review'), ('graph_contribution', 'visual_review')]
c['semantic_roundtrip']['remaining_semantic_delta']=bound+' Distinct staged CONTRACT/BODY/canary/reader-repair and boundedFINAL '+sha(final)+'; reused related actor history disclosed, no human/external/absolute-blind/runtimeattestation. OWNpostnative/deliverypending.'
c['verification']['independent_review']='Distinct boundedFINAL '+sha(final)+'. Five conditional proofs/two complete public canaries; actual combined gates/sharedregistry/repaired12original localfile pixels reviewed. Full source/Chapter2/Goal OPEN. OWNpostnative/concrete deliverypending. RequestedAstra-medium/stagedrelatedactors, no human/external/runtimeattestation.'
c['graph_contribution']['visual_review']='Selected7public/7totalnodes,1885coalesced directTYPE_VALUE presences/8production+5canaryVALUEpairs/four individuallyselected Eq.mpr numericbranches. All11015complete oldregistryobjects unchanged+5production=11020. Actual localfile desktop1440/14formulas/zeroerrors/12originals personallyviewed byroot anddistinctFINAL; foldedLean/built-inwrap. NotHTTP/live/allviewports/perBookduplicates/fulltransitive/sourcecount.'
CONTRIBUTION.write_bytes((json.dumps(c, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
suffix='\nBounded FINAL accepted: '+bound+' FINAL SHA '+sha(final)+'. OWNnative5->0 only these five proofs. Combined gates/fullharness and repairedSITEv2/sharedregistry/localfile12pixels reviewed. Postnative/draftPRpending; historical pending entries retain stage meaning.\n'
for p in docs:
    p.write_bytes(before[p] + suffix.encode('utf8'))
capture('accepted-frontier-refresh-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'frontier-refresh', '--root-objective', 'Persistent Orabona Chapters1-16; ONLY five conditional prescient cumulative proofs accepted', '--leaf', TASK, '--kind', 'review', '--statement', bound, '--file', final, '--source-status', 'source-reviewed', '--leaf-status', 'accepted', '--dependency', 'review:bounded-prescient-cumulative-FINAL:accepted', '--trials', RUN / 'trials.jsonl', '--output', RUN / 'accepted-frontier-v1.json', '--shadow-status', 'pending')
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
assert (tr['obligations_before'], tr['obligations_after']) == (5, 0) and tr['verifier_evidence'] == [str(final)]
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
write(RUN/'PR-body-v1.md','Derives cumulative prescient Bregman regret from the same actual partial recursion. The common summation bound allows arbitrary positive played steps and zero rounds. Fixed and nonincreasing-step sharp bounds retain the negative terminal divergence and movement terms; the printed forms drop only the terminal term after proving its nonnegativity. No desired one-step regret inequality is assumed.\n\nTwo complete public canaries use restricted nonsmooth/affine losses, a nonquadratic generator, actual states 1/2 -> 0 -> 1/2, and a genuinely decreasing schedule. Four separately selected numeric proof branches retain their specific new production theorem. The previous-state maximum is checked at a comparator where it differs from the initial divergence.\n\nValidation: focused and combined Lean root/Tests builds, public VALUE probes, frozen statements, standard-only axiom audit, full harness (472 tests, 7 existing skips), scoped frontier shadow, and two contributor bases. A clean local site build/check preserves all 11,015 old registry records and adds five production nodes. Root and distinct staged automated review inspect twelve actual desktop originals. The reader scope ambiguity and exact prose-only repair, earlier failures and RAW history remain in the evidence. The site build applies to its bound candidate commit; no fresh site build at the later evidence commit is claimed.\n\nStacked on OPEN draft unmerged PR #211, exact 24de0231aa067f141251aac5c20deb58e448ea66, branch codex/research-online-ch2-prescient-causal. These five conditional interfaces advance a required Chapter2 forward dependency. Full source-domain/generator/loss hypothesis transport and a valid source-run wrapper remain required/open; all eight Chapter2 forward containers remain open. Chapter2 and the Chapters1-16 Goal are incomplete. No full Algorithm15.8/Theorem15.30, Chapter6/15 acceptance, merge, deployment or main/live update. Functor audit: none-found-with-reason.\n\nEvidence: docs/contracts/online-ch2-prescient-cumulative-v1; runs/online-ch2-prescient-cumulative-20261009/FINAL-review-v1.md and bound JSON; research-wiki/contribution-contracts/ONLINE-CH2-PRESCIENT-CUMULATIVE-20261009.json.\n')
write(RUN/'PR-plan-v1.json',dict(title='[Online Learning Ch2] Prove same-run prescient cumulative regret',body_path=(RUN/'PR-body-v1.md').as_posix(),body_sha256=sha(RUN/'PR-body-v1.md'),base='codex/research-online-ch2-prescient-causal',head=BRANCH,draft=True,parent_exact_head=BASE,merge=False,deploy=False,scope=bound))
fixed()
print('Actual OWN native acceptance and exact permitted metadata transitions audited; distinct postnative review pending.')
