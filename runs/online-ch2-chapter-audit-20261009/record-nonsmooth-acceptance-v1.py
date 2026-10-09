from common_nonsmooth_publication_v5 import *
import base64,copy

fixed()
final=RUN/'nonsmooth-FINAL-review-v1.json'
assert sha(final)=='b3f416c09f63a980067ab044bc3a550396fcbe998bbf6408b253030b5cc4d723'
review=load(final);assert review['package_verdict']=='accepted-with-explicit-delta' and not review['required_repairs']
targets=load(CONTRACT/'nonsmooth-targets-draft-v1.json')['targets']
names=[t['declaration'] for t in targets];assert len(names)==3
retrieval=ROOT/'research-wiki/retrieval-index/ONLINE-CH2-NONSMOOTH-20261009.md'
mutable=[RUN/'trials.jsonl',RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json',CONTRIBUTION,retrieval]
before={p:p.read_bytes() for p in mutable}
write(RUN/'nonsmooth-pre-native-exact-bytes-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(b).decode('ascii')) for p,b in before.items()],
    FINAL_sha256=sha(final),scope='Only five OWN metadata paths may change; all historical bytes preserved here.'))
bound='Exactly three frozen derived terminals / two introductory source families / five public canaries. Chapter2 incomplete; chapter proof denominator null; whole Chapters1-16 Goal ACTIVE. All eight required mathematical forward references remain open. No merge/deployment/main/live/CI acceptance.'
write(RUN/'memory-digest-nonsmooth-accepted-v1.md','# '+TASK+'\n\n'+bound+'\n\nDistinct bounded FINAL accepted-with-explicit-delta. Current actual root9106/Tests9272/full harness472 tests7 skips and exporter compiled/check-passed; all8 full public VALUE kernels standard-only axioms,8 statement fences,13 required VALUE pairs. Current isolated SITE4/check/shared registry preserve10981 old full nodes plus3 new proofs; actual desktop DOM/geometry and8 original pixels reviewed by distinct reviewer. Native recording and prospective delivery require separate post-native audit. Historical failures and exactly3 frozen RAW decoder whitespace exceptions retained. Native CLI does not enforce the full semantic paper workflow.\n')
write(CONTRACT/'current-obligations-nonsmooth-accepted-v1.json',dict(scope=bound,terminals=[dict(declaration=t['declaration'],statement_hash=t['statement_hash'],status='bounded-FINAL-accepted',proof_module_sha256=sha(PUBLIC)) for t in targets],
    source_families=2,public_canaries=5,FINAL_sha256=sha(final),source_enumeration_status='enumeration-only accepted',chapter_proof_total=None,
    chapter_complete=False,goal_complete=False,native_post_review='pending',delivery='pending'))
notes=bound+' Recorded by root from distinct source_reviewer FINAL '+sha(final)+'. Counters3->0 refer only to these three exact terminals, not chapter containers or coverage. Post-native audit/delivery pending.'
args=[sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted',
    '--run-id',RUN.name,'--attempt-id','nonsmooth-three-frozen-terminals-v1','--progress-class','closed-frontier','--reviewer-validated',
    '--obligations-before','3','--obligations-after','0','--notes',notes,'--verifier-evidence',final]
for name in names:args.extend(['--new-declaration',name])
capture('nonsmooth-native-acceptance-trial-v1',*args)
payload=dict(scope=bound,terminals=[dict(declaration=t['declaration'],statement_hash=t['statement_hash']) for t in targets],
    FINAL_sha256=sha(final),recorded_by='/root from distinct /root/source_reviewer decision',bounded_obligations_before=3,bounded_obligations_after=0,
    chapter_proof_total=None,chapter_complete=False,goal_complete=False,post_native_review='pending',delivery='pending')
event('nonsmooth-native-acceptance-event-v1','accepted',payload)
# Metadata fields describe already verified exact sources; they do not mutate reader/site bytes.
c=load(CONTRIBUTION)
c['graph_contribution']['visual_review']='Current actual selected13nodes/1773 coalesced TYPE_VALUE presences/13 required VALUE pairs; shared registry preserves10981 full prior nodes plus3 public proofs. Current1440px desktop DOM/strict geometry and8 original images personally inspected by root and distinct FINAL reviewer. No all-viewports claim.'
c['verification']['site_build']='Actual clean isolated SITE4 build exit0, source commit07b2fa54420e9e224253946a5409bc4aa632e610; nonsmooth-site-build-v4.json. Existing unchanged exact Lean/root/pins full gate applies. No generated _site edit/deployment.'
c['verification']['site_check']='Actual SITE4 check exit0; nonsmooth-registry-inspected-v2.json preserves all10981 full prior records plus3 new shared public proof nodes; no per-Book duplication/Test canonical nodes. Actual browser/geometry8images and distinct FINAL pixel review passed.'
c['verification']['independent_review']='Distinct staged source/CONTRACT/BODY/canary/reader reviews and bounded FINAL accepted-with-explicit-delta: '+sha(final)+'. Three frozen derived terminals/two families/five canaries only. Historical failures/RAW exceptions retained. OWN native post-review and real delivery pending; Chapter2 incomplete; no human/external/runtime attestation.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
suffix='\nBounded FINAL update: three exact derived terminals/two introductory families/five public canaries accepted-with-explicit-delta; FINAL SHA '+sha(final)+'. Current combined Lean/harness, clean isolated SITE4/check/shared registry and actual desktop pixels passed. Own native acceptance recorded with explicit3->0 bounded counters; post-native audit and real PR delivery pending. Historical entries above are stage records, not current pending gates. Chapter2 remains incomplete; independent chapter proof denominatornull; all required forward references stay open; whole Goal ACTIVE. No merge/deploy/main/live/CI claim.\n'
retrieval.write_bytes(before[retrieval]+suffix.encode('utf8'))
capture('nonsmooth-accepted-frontier-refresh-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','frontier-refresh',
    '--root-objective','Persistent Orabona Chapters1-16; ONLY three nonsmooth derived terminals accepted',
    '--leaf',TASK,'--kind','review','--statement',bound,'--file',final,'--source-status','source-reviewed',
    '--leaf-status','accepted','--dependency','review:nonsmooth-bounded-FINAL:accepted','--trials',RUN/'trials.jsonl',
    '--output',RUN/'nonsmooth-accepted-frontier-v1.json','--shadow-status','pending')
_,out=capture('nonsmooth-accepted-frontier-shadow-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','frontier-shadow',
    '--trials',RUN/'trials.jsonl','--memory-digest',RUN/'memory-digest-nonsmooth-accepted-v1.md','--frontier',RUN/'nonsmooth-accepted-frontier-v1.json')
shadow=json.loads(out);assert shadow['mismatches']==[] and not shadow['would_mutate']
# Inspect actual semantic suffixes, sequence and ownership, not just prefix preservation.
for p in mutable[:2]:assert p.read_bytes().startswith(before[p])
trial_suffix=(mutable[0].read_bytes()[len(before[mutable[0]]):]).decode('utf8').splitlines();assert len(trial_suffix)==1
tr=json.loads(trial_suffix[0]);assert tr['task']==TASK and tr['role']=='reviewer' and tr['kind']=='review' and tr['status']=='accepted'
assert tr['new_declarations']==names and tr['notes']==notes and tr['reviewer_validated'] is True
assert (tr['obligations_before'],tr['obligations_after'])==(3,0) and tr['verifier_evidence']==[str(final)]
event_suffix=(mutable[1].read_bytes()[len(before[mutable[1]]):]).decode('utf8').splitlines();assert len(event_suffix)==1
ev=json.loads(event_suffix[0]);state_before=json.loads(before[mutable[2]]);state=load(mutable[2])
assert ev['session_id']==TASK and ev['event_type']=='accepted' and ev['payload']==payload
assert ev['sequence']==state_before['next_sequence'] and ev['parent_id']==state_before['current_entry_id']
expected_state=copy.deepcopy(state_before);expected_state.update(next_sequence=state_before['next_sequence']+1,current_entry_id=ev['entry_id'])
assert state==expected_state
oldc=json.loads(before[CONTRIBUTION]);allowed_fields=[('graph_contribution','visual_review'),('verification','site_build'),('verification','site_check'),('verification','independent_review')]
reset=copy.deepcopy(c)
for a,b in allowed_fields:reset[a][b]=oldc[a][b]
assert reset==oldc and retrieval.read_bytes()==before[retrieval]+suffix.encode('utf8')
resolved=[]
for row in load(RUN/'nonsmooth-FINAL-inputs-v1.json')['rows']:
    p=Path(row['path'])
    if sha(p)!=row['sha256']:
        assert p in before and hashlib.sha256(before[p]).hexdigest()==row['sha256'],p
        resolved.append(dict(path=p.as_posix(),before_sha256=row['sha256'],after_sha256=sha(p),exact_before_snapshot='nonsmooth-pre-native-exact-bytes-v1.json'))
assert len(resolved)==5
write(RUN/'nonsmooth-post-native-root-audit-v1.json',dict(scope=bound,actual_trial_suffix=tr,actual_lifecycle_suffix=ev,state_exact_expected=True,
    contribution_changed_fields=allowed_fields,retrieval_suffix=suffix,changed_FINAL_inputs=resolved,all_other_FINAL_inputs_unchanged=True,
    shadow=shadow,root_self_audit_only=True,distinct_post_native_review='pending',actual_native_commands_passed=True))
title='[Online Learning Ch2] Prove absolute and hinge differentiability examples'
body='''Closes a bounded Chapter2 example package from Orabona arXiv:1912.13213v10, printed16/PDF28: three public proofs for two introductory source families, with five complementary public canaries. Shifted absolute value is differentiable exactly off its center. Hinge is differentiable exactly off the margin; labelled hinge is globally differentiable exactly when its effective normal is zero, including zero labels/features and dimension zero. The zero-normal qualification is separately reviewed, not attributed as an author correction.

The proofs reuse the shared BanditRLProof library and declaration registry. Canary bodies cover nonzero positive/negative labels, active kinks/smooth points, zero-normal cases, and ambient nondifferentiability versus a smooth tangential curve at the SAME point(1,3).

Validation: focused/public complete VALUE checks and standard-only axioms for all8 proof/canary values;8 frozen statement checks;13 required compiled VALUE dependency pairs. Combined root9106 and Tests9272 cached-inclusive compiler jobs passed. Full tools/bandit.py check passed472 tests with7 existing skips, exporter compilation and check-passed inspected. Clean isolated site build/check and shared registry audit passed:10981 full old records retained plus3 new public proof nodes. Actual1440px desktop DOM/strict geometry and8 screenshots reviewed; no mobile/all-viewports claim. Distinct staged automated FINAL accepted-with-explicit-delta; historical failures and exactly3 SHA-bound immutable decoder whitespace exceptions retained. This is not human/external review.

Stacked on OPEN unmerged PR #203 at097359ac6e1398c55e712bbfa02ff3f1803dd3ea, base codex/research-online-c1-chapter-audit. This PR also carries Chapter2 source reconciliation and exact existing variable-OGD reuse evidence;65 overlapping source containers are enumeration only, not a proof denominator. Chapter2 remains partial, its required forward references stay open, Chapters3-16 remain unenumerated, and the whole-book Goal remains ACTIVE. No main/live update, merge or deployment.

Evidence: runs/online-ch2-chapter-audit-20261009/nonsmooth-FINAL-review-v1.md and its SHA-bound JSON; docs/contracts/online-ch2-chapter-audit-v1; research-wiki/contribution-contracts/ONLINE-CH2-NONSMOOTH-20261009.json. OWN native closure and publication receive a separate post-native review before delivery.
'''
write(RUN/'nonsmooth-PR-body-v1.md',body)
write(RUN/'nonsmooth-PR-plan-v1.json',dict(title=title,body_path=(RUN/'nonsmooth-PR-body-v1.md').as_posix(),body_sha256=sha(RUN/'nonsmooth-PR-body-v1.md'),
    base='codex/research-online-c1-chapter-audit',head=BRANCH,draft=True,parent_exact_head=BASE,merge=False,deploy=False,scope=bound))
fixed()
write(RUN/'nonsmooth-post-native-inputs-v1.json',dict(rows=rows([p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts]+[PUBLIC,CANARY,CONTRIBUTION,retrieval]),
    FINAL_sha256=sha(final),mutable_FINAL_resolution=resolved,whole_Goal_status='ACTIVE'))
print('Actual OWN native suffix/state/metadata audited; distinct post-native and prospective publication review required.')
