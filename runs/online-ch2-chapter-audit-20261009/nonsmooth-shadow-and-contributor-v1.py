from common_nonsmooth_publication_v2 import *
import base64

fixed()
assert load(RUN/'nonsmooth-full-harness-inspected-v1.json')['actual_check_passed']
write(RUN/'nonsmooth-current-shadow-memory-v1.md',
    '# '+TASK+'\n\nThree actual new production proofs/two introductory nonsmooth source families and five meaningful canaries; exact frozen types, complete VALUE kernels, standard-only axioms, actual13VALUE pairs and eight native fences inspected. '
    'Distinct production CONTRACT/source qualification/BODY, canary CONTRACT/BODY and exact-reader-v2 repair accepted. Original reader-v1 rejection retained. '
    'Actual combined root/Tests/full harness compiler/unittest/exporter/check markers passed. Shared registry/current local site/pixels/FINAL/native/delivery remain pending. '
    '65overlapping chapter source containers are not a proof denominator; proof-totalnull; all future references remain required/open. Chapter2 partial, Chapters3-16unenumerated, whole Goal ACTIVE. '
    'OWN frontier/trials/memory only; global SGB stays fixed; not main/live, merged, deployed or retired.\n')
capture('nonsmooth-current-trial-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','trial-log',
    '--task',TASK,'--role','lower','--kind','build','--status','compiled',
    '--run-id',RUN.name,'--progress-class','compiled-leaf',
    '--notes','Three fixed exact production terminals closed, two source families; five canary actual bodies. Distinct BODY/source qualification/canary/reader repair plus current root/Tests/fullharness passed. Site/FINAL/delivery pending; not Chapter2 completion. Native omitted obligation counters0 are unmeasured defaults, never chapter coverage; total remains null.',
    '--verifier-evidence',RUN/'nonsmooth-full-harness-inspected-v1.json')
capture('nonsmooth-current-frontier-refresh-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','frontier-refresh',
    '--root-objective','Persistent Orabona Chapters1-16; bounded Chapter2 nonsmooth example package only',
    '--leaf',TASK,'--kind','review','--statement','Three actual exact public proofs/two introductory nonsmooth families plus five canaries; current Lean/root/Tests/harness passed, current reader repair accepted, shared registry/site/FINAL/delivery pending. Chapter2 and whole Goal incomplete.',
    '--file',RUN/'nonsmooth-reader-repair-review-v2.md','--source-status','source-reviewed','--leaf-status','gate-pending',
    '--dependency','review:nonsmooth-production-BODY:accepted','--dependency','review:nonsmooth-canary-BODY:accepted',
    '--dependency','lean:BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff:compiled',
    '--trials',RUN/'trials.jsonl','--output',RUN/'nonsmooth-current-frontier-v1.json','--shadow-status','pending')
_,stdout=capture('nonsmooth-current-frontier-shadow-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py','frontier-shadow',
    '--trials',RUN/'trials.jsonl','--memory-digest',RUN/'nonsmooth-current-shadow-memory-v1.md','--frontier',RUN/'nonsmooth-current-frontier-v1.json')
s=json.loads(stdout);assert s['mismatches']==[] and not s['would_mutate']
write(RUN/'nonsmooth-shadow-inspected-v1.json',dict(actual_report=s,global_SGB_frontier_trials_memory_retrieval_unchanged=True,
    native_obligation_default_zero_unmeasured=True,chapter_proof_total=None,chapter_complete=False,whole_Goal_status='ACTIVE'))
for label,base in [('nonsmooth-contributor-stack-v1',BASE),('nonsmooth-contributor-main-v1','origin/main')]:
    _,out=capture(label,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base)
    assert 'Contributor contract: N/A' not in out and PUBLIC.relative_to(ROOT).as_posix() in out
fixed()
print('Actual own shadow has no mismatch/global mutation; both nonempty contributor bases passed. Current site/FINAL/native/delivery remain separate.')
