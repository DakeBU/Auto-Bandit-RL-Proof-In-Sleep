from publication_guard_v1 import *
import copy
fixed()
final=RUN/'FINAL-review-v1.json';review=load(final)
assert review['package_verdict']=='accepted-with-explicit-delta' and not review['required_repairs']
for row in load(RUN/'FINAL-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256']
targets=load(CONTRACT/'stabilized-v1.json')['targets'];names=[t['declaration'] for t in targets];assert len(names)==5
docs=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows','research-wiki/retrieval-index']]
native=[RUN/n for n in ['trials.jsonl','lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md']]
mutable=[*native,CONTRIBUTION,*docs];before={p:p.read_bytes() for p in mutable}
write(RUN/'pre-native-exact-bytes-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(raw).decode('ascii')) for p,raw in before.items()],FINAL_sha256=sha(final),scope='Only explicitly permitted OWN native/metadata paths; exact immutable before bytes.'))
bound='Canonical actual-fderiv Bregman definition, five exact derived Bregman algebra/nonnegativity/gradient/proximal proofs and two nonsmooth nonquadratic/boundary Test families. Actual supplied minimum derives comparison retaining both negative residuals; old point may lie outside V, both psi derivative hypotheses explicit. Full source X/interior/local-extension/EReal finite-domain supports/convexity/minimum bridges, actual attained current-loss recursion/interiority and sharp same-run fixed/variable telescopes remain REQUIRED/OPEN, including main-text fixed-step exercise. All8 Chapter2 forwards OPEN, Chapter2 incomplete, proof denominatornull, whole16GoalACTIVE. No merge/deploy/main/live/CI/retirement.'
write(RUN/'memory-digest-accepted-v1.md','# '+TASK+'\n\n'+bound+'\n\nDistinct bounded FINAL '+sha(final)+'. Root9109/Tests9278/fullharness472tests7existing skips/exporter/checkpassed, first current full attempt0. Seven normalized frozen proof headers plus canonical definition, seven fullpublicVALUEs/fourteenstandard-onlyaxiomoutputs. Selected8nodes/1619coalesced direct TYPE_VALUE presences/8requiredVALUEpairs; both separately selected final numeric branches retain proximal helper. Clean SITEv1/check/registry10996completeold+6newproduction at69aeeeaf58364177a06bbc10329ea328c3c13b3c. Two nonempty contributor bases. Actual local-file desktop11formulas/zeroerrors/geometry/14originals inspected by root and distinctFINAL. No HTTP/live/later-head-site claim. Compiler/API/collision failures, raw-header/native hashes and two immutable SHA-bound received LaTex trailing-space exceptions retained: full2/scoped0. Native/postnative/delivery separate.\n')
write(CONTRACT/'current-obligations-accepted-v1.json',dict(scope=bound,terminals=[dict(declaration=t['declaration'],statement_hash=t['statement_hash'],status='bounded-FINAL-accepted',proof_module_sha256=sha(PUBLIC)) for t in targets],public_canaries=2,canonical_definitions=1,FINAL_sha256=sha(final),source_container_closed=False,chapter_proof_total=None,chapter_complete=False,goal_complete=False,native_post_review='pending',delivery='pending'))
notes=bound+' Recorded by root from distinct source_reviewer FINAL '+sha(final)+'. Counter5->0 ONLY five exact derived proofs, not printed source/chapter coverage. Post-native audit/delivery pending.'
args=[sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','five-frozen-Bregman-proofs-v1','--progress-class','closed-frontier','--reviewer-validated','--obligations-before','5','--obligations-after','0','--notes',notes,'--verifier-evidence',final]
for name in names:args.extend(['--new-declaration',name])
capture('native-acceptance-trial-v1',*args)
payload=dict(scope=bound,terminals=[dict(declaration=t['declaration'],statement_hash=t['statement_hash']) for t in targets],FINAL_sha256=sha(final),recorded_by='/root from distinct /root/source_reviewer decision',bounded_obligations_before=5,bounded_obligations_after=0,chapter_proof_total=None,chapter_complete=False,goal_complete=False,post_native_review='pending',delivery='pending')
event('native-acceptance-event-v1','accepted',payload)
c=load(CONTRIBUTION);oldc=copy.deepcopy(c)
allowed=[('graph_contribution','visual_review'),('verification','bandit_check'),('verification','site_build'),('verification','site_check'),('verification','independent_review')]
c['graph_contribution']['visual_review']='Selected8nodes/1619direct TYPE_VALUE presences/8requiredVALUEpairs and two individually selected final numeric helper branches inspected. Complete registry10996old+6production nodes; actual local-file1440px desktop14originals personally inspected by root and distinctFINAL. No Test/per-Book duplication/HTTP/all-viewports claim.'
c['verification']['bandit_check']='Actual root9109/Tests9278/full harness exit0,472tests7existing skips/exporter/checkpassed first current full attempt; sources tracked beforehand, no rule/test/pin weakening.'
c['verification']['site_build']='Actual clean isolated SITEv1 exit0 at69aeeeaf58364177a06bbc10329ea328c3c13b3c, applicable unchanged proof/root/pins fullgate. No later evidence-head fresh build/deploy claim.'
c['verification']['site_check']='Actual SITEv1/check/registry exit0,10996complete prior records+6source-qualified production nodes. Local-file browser11source-guide formulas/zeroerrors/strict desktopgeometry/14originals root and distinctFINAL inspected;4exactgeneratedfiles unchanged. Prior HTTP service rejection preserved, no retry/HTTP/live claim.'
c['verification']['independent_review']='Distinct staged CONTRACT/BODY/canary/reader/RAW and boundedFINAL accepted-with-explicit-delta '+sha(final)+'. Five derived proofs/one canonical definition/two canary families only; full source/Chapter2 incomplete. Two SHA-bound immutable received LaTex trailing spaces, full2/scoped0; failures retained. OWNpostnative/actualdelivery pending. Requested Astra/medium automated actors with reused related history; no human/external/absolute-blind/runtime attestation.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
suffix='\nBoundedFINAL update: canonical Bregman definition plus five exact dependency proofs and two actual nonsmooth Test families accepted-with-explicit-delta; FINAL SHA '+sha(final)+'. CombinedLean/fullharness/cleanSITEv1/sharedregistry/localfile14pixels passed. OWNnative5->0 ONLY five frozen derived proof obligations, definition separate; postnative/draftPR pending. Fullsource/all8Ch2forwards REQUIRED/OPEN, chapterdenominatornull, wholeGoalACTIVE. Historical pending entries retain stage meaning. No main/live/merge/deploy/retirement/HTTPclaim.\n'
for p in docs:p.write_bytes(before[p]+suffix.encode('utf8'))
capture('accepted-frontier-refresh-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; ONLY five derived Bregman dependency proofs and one canonical definition accepted','--leaf',TASK,'--kind','review','--statement',bound,'--file',final,'--source-status','source-reviewed','--leaf-status','accepted','--dependency','review:bounded-Bregman-FINAL:accepted','--trials',RUN/'trials.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending')
_,out=capture('accepted-frontier-shadow-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-shadow','--trials',RUN/'trials.jsonl','--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=json.loads(out);assert shadow['mismatches']==[] and not shadow['would_mutate']
for p in native[:2]:assert p.read_bytes().startswith(before[p])
ts=native[0].read_bytes()[len(before[native[0]]):].decode('utf8').splitlines();assert len(ts)==1
tr=json.loads(ts[0]);assert (tr['task'],tr['role'],tr['kind'],tr['status'])==(TASK,'reviewer','review','accepted')
assert tr['new_declarations']==names and tr['notes']==notes and tr['reviewer_validated'] is True
assert (tr['obligations_before'],tr['obligations_after'])==(5,0) and tr['verifier_evidence']==[str(final)]
es=native[1].read_bytes()[len(before[native[1]]):].decode('utf8').splitlines();assert len(es)==1
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
write(RUN/'PR-body-v1.md',"""Adds one canonical Bregman divergence using the actual Frechet derivative and five reusable proofs: self identity, source-oriented three-point identity, convex nonnegativity, gradient conversion and a nonsmooth proximal comparison derived from an actual supplied minimum. The comparison retains both negative residuals, allows the old point outside V and does not differentiate the loss. Two public test families prove their own minima: a nonquadratic regularizer with absolute loss and an interval boundary minimum with an outside initial point. Both final numerical proof branches retain the public helper.

Validation: focused builds, full public VALUE/kernel and standard-only axiom audits, seven frozen proof headers plus canonical definition, eight required compiled VALUE pairs and both separately selected numeric tails. Combined root9109/Tests9278 and full harness472tests with7existing skips/exporter/checkpassed, first current full attempt0. Two nonempty contributor bases and clean isolated site/check/shared registry passed at69aeeeaf58364177a06bbc10329ea328c3c13b3c:10996complete prior records preserved plus6shared production nodes. Fourteen actual local-file desktop originals, formulas and geometry inspected by root and a distinct staged automated FINAL reviewer. No HTTP/live/later-head-site claim. Full whitespace reports exactly two immutable SHA-bound received decoder LaTex trailing spaces; scoped check passes excluding only these reports.

Stacked on OPEN unmerged PR #208, exact base71f2219fa1648094eba8aa17b50e443258f436cb, branch codex/research-online-ch2-proximal. This is a necessary Chapter2 prescient dependency, not complete Algorithm15.8/Theorem15.30 or Chapter6/15 acceptance. Source X/interior/local-extension validity, finite-domain extended-real/subgradient/convexity/minimum bridges, actual attained current-loss recursion/interiority and sharp same-run fixed/variable terminals including the main-text fixed-step exercise remain REQUIRED/OPEN. All8 Chapter2 forwards remain open, Chapter2 partial, Chapters1–16 Goal ACTIVE. No merge/main/live/CI/deploy/retirement claim. Functor audit: none-found-with-reason.

Evidence: docs/contracts/online-ch2-bregman-v1; runs/online-ch2-bregman-20261009/FINAL-review-v1.md and SHA-bound JSON; research-wiki/contribution-contracts/ONLINE-CH2-BREGMAN-20261009.json. Native and concrete delivery records receive separate inspection.
""")
write(RUN/'PR-plan-v1.json',dict(title='[Online Learning Ch2] Prove canonical Bregman proximal comparison',body_path=(RUN/'PR-body-v1.md').as_posix(),body_sha256=sha(RUN/'PR-body-v1.md'),base='codex/research-online-ch2-proximal',head=BRANCH,draft=True,parent_exact_head=BASE,merge=False,deploy=False,scope=bound))
fixed();print('Actual OWN native acceptance/parsed suffix/state/metadata audited; distinct post-native review pending.')
