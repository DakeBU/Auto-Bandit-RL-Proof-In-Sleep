from publication_guard_v3 import *
import copy

fixed()
final=RUN/'FINAL-review-v1.json'
assert sha(final)=='aea107ead82743ae4c4948d64cbd9ba5b299dde77b2b1eeb1689cb0cabf8a0cf'
review=load(final);assert review['package_verdict']=='accepted-with-explicit-delta' and not review['required_repairs']
for row in load(RUN/'FINAL-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256']
targets=load(CONTRACT/'stabilized-v1.json')['targets'];names=[t['declaration'] for t in targets];assert len(names)==7
manifest=ROOT/'research-wiki/contribution-contracts'/(TASK+'.json')
docs=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows','research-wiki/retrieval-index']]
native=[RUN/n for n in ['trials.jsonl','lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md']]
mutable=[*native,manifest,*docs];before={p:p.read_bytes() for p in mutable}
write(RUN/'pre-native-exact-bytes-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(raw).decode('ascii')) for p,raw in before.items()],FINAL_sha256=sha(final),scope='Only explicitly permitted OWN native/metadata paths; immutable before bytes.'))
bound='Exactly seven frozen affine Euclidean prescient derived terminals form one foundation chain, with five public canaries and three nondegenerate API audit values. Full general convex/subdifferentiable/Bregman/variable-step source, its constant-step source exercise and all eight Chapter2 forward containers remain REQUIRED/OPEN. Chapter2 incomplete, chapter proof denominator null, whole Chapters1-16 Goal ACTIVE. No merge/deployment/main/live/CI acceptance/retirement.'
write(RUN/'memory-digest-accepted-v1.md','# '+TASK+'\n\n'+bound+'\n\nDistinct bounded FINAL accepted-with-explicit-delta '+sha(final)+'. Actual shared root9107/Tests9274/fullharness472tests7existing skips/exporter/checkpassed; twelve frozen guards and full public VALUE kernels with standard-only axioms. Selected graph29nodes/3538coalesced direct TYPE_VALUE presences/12required VALUE pairs; not full registry or proof counts. Actual clean SITEv2/check/shared registry10984complete old records+11newproduction nodes; two nonempty contributor gates, desktop DOM/geometry/16original images reviewed by root and distinct reviewer. Native/post-native/delivery separate from mathematical/semantic/site gates; no single enforced runtime. Historical failures and exactly2SHA-bound immutable received decoder EOF exceptions retained.\n')
write(CONTRACT/'current-obligations-accepted-v1.json',dict(scope=bound,terminals=[dict(declaration=t['declaration'],statement_hash=t['statement_hash'],status='bounded-FINAL-accepted',proof_module_sha256=sha(PUBLIC)) for t in targets],public_canaries=5,additional_API_audit_values=3,FINAL_sha256=sha(final),source_container_closed=False,chapter_proof_total=None,chapter_complete=False,goal_complete=False,native_post_review='pending',delivery='pending'))
notes=bound+' Recorded by root from distinct source_reviewer FINAL '+sha(final)+'. Counters7->0 only these exact derived proof terminals, not printed source results or chapter coverage. Post-native audit/delivery pending.'
args=[sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','seven-frozen-affine-terminals-v1','--progress-class','closed-frontier','--reviewer-validated','--obligations-before','7','--obligations-after','0','--notes',notes,'--verifier-evidence',final]
for name in names:args.extend(['--new-declaration',name])
capture('native-acceptance-trial-v1',*args)
payload=dict(scope=bound,terminals=[dict(declaration=t['declaration'],statement_hash=t['statement_hash']) for t in targets],FINAL_sha256=sha(final),recorded_by='/root from distinct /root/source_reviewer decision',bounded_obligations_before=7,bounded_obligations_after=0,chapter_proof_total=None,chapter_complete=False,goal_complete=False,post_native_review='pending',delivery='pending')
event('native-acceptance-event-v1','accepted',payload)
c=load(manifest);oldc=copy.deepcopy(c)
allowed=[('graph_contribution','visual_review'),('verification','bandit_check'),('verification','site_build'),('verification','site_check'),('verification','independent_review')]
c['graph_contribution']['visual_review']='Actual selected29nodes/3538coalesced direct TYPE_VALUE presences/12required VALUE pairs and complete shared registry10984old records+11production nodes inspected. Actual1440px desktop DOM/strict geometry/16originals personally inspected by root and distinct FINAL reviewer. No all-viewports claim.'
c['verification']['bandit_check']='Actual current root9107/Tests9274 cached-inclusive jobs and full tools/bandit.py check exit0,472tests/7existing skips/exporter/checkpassed; unchanged exact production/Test/roots/pins confirmed in FINAL. Counts are not new theorem counts.'
c['verification']['site_build']='Actual clean isolated SITEv2 build exit0 at5680bcca81c5f894b801c0599689f2a5870e8306; exact unchanged Lean/root/pins full gate applies. Historical sitev1 failure retained with separately reviewed link repair. No new build at later evidence commit or deployment claim.'
c['verification']['site_check']='Actual SITEv2 check/registry exit0;10984complete prior records+11source-qualified production nodes, no Test/per-Book duplication. Actual9source-guide formulas/zeroerrors/strict desktop geometry and16originals inspected by root and distinct FINAL reviewer; four exact generated inputs unchanged through capture.'
c['verification']['independent_review']='Distinct staged source/CONTRACT/BODY/canary/reader and bounded FINAL accepted-with-explicit-delta '+sha(final)+'. Only seven derived terminals in one affine foundation chain/five canaries/three API audit values; full general source and Chapter2 incomplete. Exactly2immutable decoder EOF exceptions accepted; historical failures retained. OWN native post-review and concrete delivery pending. Requested Astra/medium actors, no human/external/absolute-blind/runtime attestation.'
manifest.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
suffix='\nBounded FINAL update: seven exact affine prescient derived terminals in one foundation chain, five public canaries and three nondegenerate API values accepted-with-explicit-delta; FINAL SHA '+sha(final)+'. Actual combined Lean/harness, clean SITEv2/check/shared registry and desktop pixels passed. OWN native acceptance records7->0 ONLY these derived terminals; post-native review and PR delivery pending. All general-source/eight-forward-container/Chapter2/whole-Goal obligations stay open/ACTIVE. Historical pending entries above remain stage records, not current gate statuses. No main/live/merge/deploy/retirement.\n'
for p in docs:p.write_bytes(before[p]+suffix.encode('utf8'))
capture('accepted-frontier-refresh-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; ONLY seven affine prescient derived terminals accepted','--leaf',TASK,'--kind','review','--statement',bound,'--file',final,'--source-status','source-reviewed','--leaf-status','accepted','--dependency','review:bounded-affine-FINAL:accepted','--trials',RUN/'trials.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending')
_,out=capture('accepted-frontier-shadow-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-shadow','--trials',RUN/'trials.jsonl','--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=json.loads(out);assert shadow['mismatches']==[] and not shadow['would_mutate']
for p in native[:2]:assert p.read_bytes().startswith(before[p])
ts=(native[0].read_bytes()[len(before[native[0]]):]).decode('utf8').splitlines();assert len(ts)==1
tr=json.loads(ts[0]);assert (tr['task'],tr['role'],tr['kind'],tr['status'])==(TASK,'reviewer','review','accepted')
assert tr['new_declarations']==names and tr['notes']==notes and tr['reviewer_validated'] is True
assert (tr['obligations_before'],tr['obligations_after'])==(7,0) and tr['verifier_evidence']==[str(final)]
es=(native[1].read_bytes()[len(before[native[1]]):]).decode('utf8').splitlines();assert len(es)==1
ev=json.loads(es[0]);state_before=json.loads(before[native[2]]);state=load(native[2])
assert ev['session_id']==TASK and ev['event_type']=='accepted' and ev['payload']==payload
assert ev['sequence']==state_before['next_sequence'] and ev['parent_id']==state_before['current_entry_id']
expected=copy.deepcopy(state_before);expected.update(next_sequence=state_before['next_sequence']+1,current_entry_id=ev['entry_id']);assert state==expected
assert native[3].read_bytes()==before[native[3]]
reset=copy.deepcopy(c)
for a,b in allowed:reset[a][b]=oldc[a][b]
assert reset==oldc
for p in docs:assert p.read_bytes()==before[p]+suffix.encode('utf8')
changes=[]
for row in load(RUN/'FINAL-inputs-v1.json')['rows']:
    p=Path(row['path'])
    if sha(p)!=row['sha256']:
        assert p in before and hashlib.sha256(before[p]).hexdigest()==row['sha256'],p
        changes.append(dict(path=p.as_posix(),before_sha256=row['sha256'],after_sha256=sha(p),exact_before_snapshot='pre-native-exact-bytes-v1.json'))
assert len(changes)==8
write(RUN/'post-native-root-audit-v1.json',dict(scope=bound,actual_trial_suffix=tr,actual_lifecycle_suffix=ev,state_exact_expected=True,own_journal_unchanged=True,contribution_changed_fields=allowed,docs_suffix=suffix,changed_FINAL_inputs=changes,all_other_FINAL_inputs_unchanged=True,shadow=shadow,root_self_audit_only=True,distinct_post_native_review='pending'))

write(RUN/'PR-body-v1.md','''Adds a bounded Orabona v10 Chapter2 prescient dependency: the actual affine/quadratic projected proximal update, current-inclusive prefix invariance, affine loss identity and same-run regret bound retaining negative terminal distance and movement energy. Seven public proofs form one producer chain, supported by five complementary canaries and three nondegenerate public API audit values. Projection/minimizer and single-step inequalities are proved, not assumed. On constrained domains movement energy is not silently replaced by ordinary-gradient energy.

The shared BanditRLProof library/registry is reused;10984 complete existing records are preserved and11 source-qualified production nodes(7proofs/4definitions) added. Reader material shows source, assumptions, formula proof, folded Lean, actual parents and the open boundary. Functor audit: none-found-with-reason; no certified cross-setting transport is added.

Validation: focused builds, full public VALUE kernel checks and standard-only axioms,12 frozen statement guards,12 required actual VALUE dependency pairs. Combined root9107/Tests9274 cached-inclusive jobs passed; tools/bandit.py check passed472tests with7existing skips, exporter compilation and check-passed inspected. Clean isolated site build/check and shared registry passed at5680bcca81c5f894b801c0599689f2a5870e8306; actual desktop DOM/geometry and16original screenshots reviewed. Two nonempty contributor bases passed. Distinct staged automated FINAL accepted-with-explicit-delta; this is not human/external review. Historical failures are retained; full package whitespace check reports exactly two SHA-bound immutable received decoder EOF exceptions, while the scoped check passes with no code/Test/reader/contract exemption.

Stacked on OPEN unmerged PR #204, exact base b1486aa11451556858fda44eabf356ba26ab01b8, branch codex/research-online-ch2-chapter-audit. Affine-loss/Euclidean constant-step specialization and explicit complete-Hilbert extension only. The full general convex/subdifferentiable/Bregman/variable-step source theorem, including its constant-step main-text exercise, and all eight required Chapter2 forward containers remain REQUIRED/OPEN. Chapter2 is incomplete and the whole Chapters1–16 Goal remains ACTIVE. No merge/deployment/main/live update or CI acceptance claim.

Evidence: docs/contracts/online-ch2-prescient-v1; runs/online-ch2-prescient-20261009/FINAL-review-v1.md and its SHA-bound JSON; research-wiki/contribution-contracts/ONLINE-CH2-PRESCIENT-20261009.json. Native acceptance and prospective delivery receive a separate post-native review before publication.
''')
write(RUN/'PR-plan-v1.json',dict(title='[Online Learning Ch2] Prove affine prescient proximal regret with movement residuals',body_path=(RUN/'PR-body-v1.md').as_posix(),body_sha256=sha(RUN/'PR-body-v1.md'),base='codex/research-online-ch2-chapter-audit',head=BRANCH,draft=True,parent_exact_head=BASE,merge=False,deploy=False,scope=bound))
fixed()
print('Actual OWN native acceptance/parsed suffixes/state/metadata audited; distinct post-native review pending.')
