from publication_guard_v2 import *
import copy
fixed()
final=RUN/'FINAL-review-v1.json';review=load(final)
assert review['package_verdict']=='accepted-with-explicit-delta' and not review['required_repairs']
for row in load(RUN/'FINAL-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256']
targets=load(CONTRACT/'stabilized-v1.json')['targets'];names=[t['declaration'] for t in targets];assert len(names)==1
docs=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows','research-wiki/retrieval-index']]
native=[RUN/n for n in ['trials.jsonl','lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md']]
mutable=[*native,CONTRIBUTION,*docs];before={p:p.read_bytes() for p in mutable}
write(RUN/'pre-native-exact-bytes-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(raw).decode('ascii')) for p,raw in before.items()],FINAL_sha256=sha(final),scope='Only explicitly permitted OWN native/metadata paths; exact immutable before bytes.'))
bound='Exactly one derived real convex minimizer-comparison dependency and three complementary Test families. Actual supplied minimum, convex nonsmooth f and ambient derivative only of h; arbitrary real normed E. Full general Bregman/extended-real/subgradient bridges, attained current-loss recursion/interior validity, same-run fixed/variable source bounds and all eight Chapter2 forward containers remain REQUIRED/OPEN. Chapter2 incomplete, proof denominator null, whole Chapters1-16 Goal ACTIVE. No merge/deploy/main/live/CI/retirement.'
write(RUN/'memory-digest-accepted-v1.md','# '+TASK+'\n\n'+bound+'\n\nDistinct bounded FINAL accepted-with-explicit-delta '+sha(final)+'. Actual root9108/Tests9276/fullharness472tests7existing skips/exporter/checkpassed;4frozenheaders/full public VALUE kernels/standard-only axioms. Selected graph4nodes/1420coalesced direct TYPE_VALUE presences/6required VALUE pairs and two separately selected numeric proof tails retained helper after B1. Clean SITEv1/check/shared registry10995old+1node at3a81dd6ae283fce90b849d928c18094f37b6d3b7; two nonempty contributor bases. Actual local-file desktop DOM10formulas/zeroerrors/geometry/4originals inspected by root and distinct FINAL reviewer. HTTP preview service policy-rejected, no service retry or HTTP/live claim. Historical failures/RAW/2immutable received decoder EOF exceptions retained. Native/postnative/delivery distinct gates, not single enforced runtime.\n')
write(CONTRACT/'current-obligations-accepted-v1.json',dict(scope=bound,terminals=[dict(declaration=t['declaration'],statement_hash=t['statement_hash'],status='bounded-FINAL-accepted',proof_module_sha256=sha(PUBLIC)) for t in targets],public_canaries=3,FINAL_sha256=sha(final),source_container_closed=False,chapter_proof_total=None,chapter_complete=False,goal_complete=False,native_post_review='pending',delivery='pending'))
notes=bound+' Recorded by root from distinct source_reviewer FINAL '+sha(final)+'. Counter1->0 ONLY one exact derived helper, not printed source/chapter coverage. Post-native audit/delivery pending.'
args=[sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','one-frozen-real-comparison-v1','--progress-class','closed-frontier','--reviewer-validated','--obligations-before','1','--obligations-after','0','--notes',notes,'--verifier-evidence',final]
for name in names:args.extend(['--new-declaration',name])
capture('native-acceptance-trial-v1',*args)
payload=dict(scope=bound,terminals=[dict(declaration=t['declaration'],statement_hash=t['statement_hash']) for t in targets],FINAL_sha256=sha(final),recorded_by='/root from distinct /root/source_reviewer decision',bounded_obligations_before=1,bounded_obligations_after=0,chapter_proof_total=None,chapter_complete=False,goal_complete=False,post_native_review='pending',delivery='pending')
event('native-acceptance-event-v1','accepted',payload)
c=load(CONTRIBUTION);oldc=copy.deepcopy(c)
allowed=[('graph_contribution','visual_review'),('verification','bandit_check'),('verification','site_build'),('verification','site_check'),('verification','independent_review')]
c['graph_contribution']['visual_review']='Actual selected4nodes/1420coalesced direct TYPE_VALUE presences/6requiredVALUEpairs and two separately selected numeric final proof tails retain helper. Complete registry10995old+1source-qualified production node; no Test/per-Book duplication. Actual local-file1440px desktop DOM/geometry/4originals personally inspected by root and distinct FINAL reviewer; no HTTP/all-viewports claim.'
c['verification']['bandit_check']='Actual root9108/Tests9276 cached-inclusive jobs/full tools/bandit.py check exit0,472tests7existing skips/exporter/checkpassed; exact unchanged proof/Test/root/pins confirmed in FINAL. Initial untracked source inventory failure retained and repaired only by staging the two source files; no rule/test/proof mutation.'
c['verification']['site_build']='Actual clean isolated SITEv1 build exit0 at3a81dd6ae283fce90b849d928c18094f37b6d3b7; applicable exact unchanged proof/root/pins gate. No new build at later evidence head or deployment claim.'
c['verification']['site_check']='Actual SITEv1 check/registry exit0;10995complete prior records+1source-qualified production proof. Actual local-file browser10source-guide formulas/zeroerrors/strict desktop geometry/4originals inspected by root and distinct FINAL reviewer;4exact generated input bytes unchanged. HTTP preview service rejected before execution; no service retry and no HTTP/live claim.'
c['verification']['independent_review']='Distinct staged source/CONTRACT/BODY/canary/B1/reader/status and bounded FINAL accepted-with-explicit-delta '+sha(final)+'. One derived helper/three canaries only, general source/Chapter2 incomplete. Exactly2SHA-bound immutable received decoder EOF exceptions; historical failures retained. OWN post-native review and concrete delivery pending. Requested Astra/medium automated actors; no human/external/absolute-blind/runtime attestation.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
suffix='\nBounded FINAL update: one exact real nonsmooth convex minimizer-comparison dependency and three complementary Test families accepted-with-explicit-delta; FINAL SHA '+sha(final)+'. Actual combined Lean/fullharness/clean SITEv1/shared registry and local-file desktop pixels passed. OWN native acceptance1->0 ONLY this derived helper; post-native review/draftPR delivery pending. General source/all8Chapter2forward containers REQUIRED/OPEN; chapter denominatornull, wholeGoalACTIVE. Historical pending entries retain their stage meaning. No main/live/merge/deploy/retirement or HTTP preview claim.\n'
for p in docs:p.write_bytes(before[p]+suffix.encode('utf8'))
capture('accepted-frontier-refresh-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; ONLY one derived real convex-minimizer comparison accepted','--leaf',TASK,'--kind','review','--statement',bound,'--file',final,'--source-status','source-reviewed','--leaf-status','accepted','--dependency','review:bounded-real-comparison-FINAL:accepted','--trials',RUN/'trials.jsonl','--output',RUN/'accepted-frontier-v1.json','--shadow-status','pending')
_,out=capture('accepted-frontier-shadow-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-shadow','--trials',RUN/'trials.jsonl','--memory-digest',RUN/'memory-digest-accepted-v1.md','--frontier',RUN/'accepted-frontier-v1.json')
shadow=json.loads(out);assert shadow['mismatches']==[] and not shadow['would_mutate']
for p in native[:2]:assert p.read_bytes().startswith(before[p])
ts=native[0].read_bytes()[len(before[native[0]]):].decode('utf8').splitlines();assert len(ts)==1
tr=json.loads(ts[0]);assert (tr['task'],tr['role'],tr['kind'],tr['status'])==(TASK,'reviewer','review','accepted')
assert tr['new_declarations']==names and tr['notes']==notes and tr['reviewer_validated'] is True
assert (tr['obligations_before'],tr['obligations_after'])==(1,0) and tr['verifier_evidence']==[str(final)]
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
write(RUN/'PR-body-v1.md','''Proves a reusable Orabona v10 Chapter2 prescient dependency: an actual minimizer p of f+h over convex V satisfies f(p)-f(u) ≤ Dh(p)[u-p] for every feasible u. The segment argument differentiates only h, so f may be nonsmooth and h need not be convex. The shared real normed-space theorem is used by three public test families, including a nonsmooth absolute loss, a boundary minimum and a nonconvex regularizer. Each family proves its minimizing condition; the two numerical final branches directly retain the public helper.

Validation: focused builds, full public VALUE/kernel and standard-only axiom checks, four frozen headers, six required compiled VALUE pairs, root9108/Tests9276 and full harness472tests with7existing skips/exporter/checkpassed. The initial harness source-inventory failure was repaired by staging the two new Lean files, with no test or proof change. Two nonempty contributor bases and clean isolated site/check/shared registry passed at3a81dd6ae283fce90b849d928c18094f37b6d3b7:10995complete prior records preserved plus one shared source-qualified proof node. Four actual local-file desktop screenshots, formula rendering and geometry were inspected by root and a distinct staged automated FINAL reviewer. No HTTP/live/deployment claim. Full whitespace reports only two SHA-bound immutable received decoder EOF blanks; scoped check passes with no mathematical exemption.

Stacked on OPEN unmerged PR #205, exact base29086b6f3a033f6536054f4d9a06ae0e9b2f8a91, branch codex/research-online-ch2-prescient. This comparison takes an actual minimum as a premise; it does not establish minimizer existence or the full general prescient algorithm. Bregman/extended-real/subgradient bridges, attained current-loss recursion/interior validity, fixed/variable-step source terminals and all eight Chapter2 forwards remain REQUIRED/OPEN. Chapter2 is partial; the Chapters1–16 Goal remains ACTIVE. No merge/main/live/CI acceptance/retirement claim. Functor audit: none-found-with-reason.

Evidence: docs/contracts/online-ch2-proximal-v1; runs/online-ch2-proximal-20261009/FINAL-review-v1.md and SHA-bound JSON; research-wiki/contribution-contracts/ONLINE-CH2-PROXIMAL-20261009.json. Native records and concrete delivery receive separate inspection.
''')
write(RUN/'PR-plan-v1.json',dict(title='[Online Learning Ch2] Prove nonsmooth convex proximal minimizer comparison',body_path=(RUN/'PR-body-v1.md').as_posix(),body_sha256=sha(RUN/'PR-body-v1.md'),base='codex/research-online-ch2-prescient',head=BRANCH,draft=True,parent_exact_head=BASE,merge=False,deploy=False,scope=bound))
fixed();print('Actual OWN native acceptance/parsed suffix/state/metadata audited; distinct post-native review pending.')
