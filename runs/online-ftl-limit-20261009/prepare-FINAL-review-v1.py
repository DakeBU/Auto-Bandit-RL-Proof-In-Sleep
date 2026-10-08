from common_body_v1 import *

integrated_fixed()
g=load(RUN/'combined-gates-v1.json')
assert g['actual_exit_codes']==[0,0,0]
reg=load(RUN/'registry-v1.json')
assert reg['retained_complete_old_nodes']==10959 and reg['new_production_nodes']==5
assert not reg['source_dirty']
images=load(RUN/'formula-render-v1.json')['images']
pixels=load(RUN/'pixel-review-v1.json')
assert len(images)==12 and pixels['actual_original_images_viewed']==12
assert pixels['images']==[dict(x,actually_viewed=True) for x in images]
for label in ['site-build-v1','site-check-v1','registry-check-v1','formula-render-v1-node',
    'candidate-contributor-stack-v1','candidate-contributor-main-v1','candidate-frontier-shadow-v1']:
    assert load(RUN/(label+'-exit.json'))['actual_exit']==0
write(RUN/'prospective-PR-title-v1.txt','Online Learning C1: actual FTL ordinary-limit criterion')
write(RUN/'prospective-PR-body-v1.md',
    'For the existing initial-half, strict-past empirical-mean FTL process, this package proves its nonnegative loss gap against the horizon empirical mean and its exact fixed-comparator decomposition, including horizon zero. On any one all-time unit observation stream, best-comparator average regret tends to zero. Fixed-comparator normalized regret has an ordinary limit a exactly when its squared distance from the empirical mean tends to -a. Explicit empirical-mean convergence then gives every real comparator the signed limit -(u-m)^2 and the literal unit-comparator LimitNoRegret property. The limiting mean is analysis-only.\n\n'
    'These five endpoints are derived source-reconciliation results for Orabona arXiv:1912.13213v10 (2026-06-21), printed2/4/6, rather than five printed theorems. They do not assert ordinary-limit existence for every bounded stream. A concrete bounded oscillating-stream obstruction and the exact all-comparator converse remain required. F1/F2 algebra allows unbounded real streams without claiming unit-game feasibility. No probabilistic, rate or arbitrary-algorithm nonnegative-regret result is claimed.\n\n'
    'Twelve public canaries instantiate all five endpoints on the actual alternating binary stream. Its empirical mean tends to one half by a proved prefix-count identity; actual predictions begin one half, zero, one half, one third. Fixed comparator zero has limit -1/4, and comparator one half has limit zero. Validation: focused builds, five whole-type VALUE witnesses,29 standard-only axiom outputs,17 native fences,16 required direct VALUE dependencies, combined root/Tests and the full harness, both contributor bases and an owned shadow. Exact logs and counts are in runs/online-ftl-limit-20261009. The first full harness failure (untracked allowlisted Lean files) is retained; staging the reviewed files repairs this verification precondition without changing mathematics or harness. The F1 fence and source-renderer configuration failures are also retained. The applicable clean local site retains10959 complete shared registry records and adds exactly five production declarations. Twelve original reader/catalogue images receive separate formalizer and distinct source-reviewer inspection.\n\n'
    'Distinct automated decoder/reviewer roles have disclosed reused history; no human/external/absolute-blind or runtime-model attestation is claimed. Only these five derived obligations may close. Original16Chapter1 source objects and null unknown proof total, other C1/C2, unenumerated C3-16 and necessary appendices remain required; the full-book Goal stays ACTIVE. Stacked on OPEN draft unmerged PR200 exact'+BASE+', base codex/research-online-kernel-causal. Main/live unchanged; no merge/deployment. Contracts: docs/contracts/online-ftl-limit-v1. Evidence: runs/online-ftl-limit-20261009. The active worktree is retained for subsequent required work.\n')
scope=dict(manifest_fields=['semantic_roundtrip.remaining_semantic_delta','graph_contribution.visual_review',
    'verification.independent_review','verification.bandit_check','verification.site_build','verification.site_check'],
    own_metadata_only='Six own-manifest fields, identical appendices to the three own task/obligations/conversion files, parsed own task/session journal suffixes, versioned accepted ledger/decision/digest/retrieval and native reviewer/lifecycle/owned frontier-shadow/memory/retrieval evidence.',
    conditions=['Public/canary/root/Tests/readers/pins and reviewed RAW inputs immutable.',
        'Snapshot and bind exact metadata changes; distinct post-native audit required.',
        'Only five derived obligations5->0; original16/null and all required source/chapter/Goal gaps remain.',
        'Capture-time candidate readers remain immutable; acceptance recorded separately.',
        'Scoped commit/push/draft with exact reviewed PR title/body and immediate official app attachment; no force/merge/deploy.'])
write(RUN/'FINAL-future-metadata-scope-v1.json',scope)
paths=[CONTRIBUTION,ROOT/'MANIFEST.md',ROOT/'runs/lifecycle_sessions.jsonl',RUN/'trials.jsonl']
paths += [ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows']]
snapshots=[]
for i,p in enumerate(paths):
    q=RUN/'snapshots'/('FINAL-metadata-'+str(i)+'-v1.raw');write(q,p.read_bytes())
    snapshots.append(dict(live_path=p.as_posix(),snapshot=q.as_posix(),sha256=sha(q)))
write(RUN/'FINAL-metadata-snapshots-v1.json',snapshots)
indexed={}
def add(p):
    p=Path(p).resolve();assert p.is_file()
    indexed[p.as_posix()]=dict(path=p.as_posix(),sha256=sha(p))
for x in load(RUN/'body-review-inputs-v1.json')['rows']:add(x['path'])
for folder in [RUN,CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts:add(p)
for p in paths+[PUBLIC,CANARY,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',PDF]+READERS:add(p)
for rel in ['books/registry.json','site-manifest.json','chapters/online-foundations/index.html']+list(reg['module_HTML_sha256']):add(SITE/rel)
write(RUN/'FINAL-review-inputs-v1.json',dict(rows=sorted(indexed.values(),key=lambda x:x['path']),
    fixed_input_count=len(indexed),source_commit=reg['source_commit'],
    original_R1_R7=load(CONTRACT/'reader-requirements-v1.json'),future_metadata_scope=scope,
    allowed_outputs=['final-reader-review-v1.md','final-reader-receipt-v1.json'],chapter_complete=False,goal_complete=False))
write(RUN/'FINAL-review-packet-v1.md',
    'Anti-anchored FINAL. Independently hash EVERY indexed current RAW input before/after. Reinspect all five complete public types/bodies and twelve actual binary canary proofs; original CONTRACT48/CANARY24/BODY287, neutral reconstructions, exact v10 source printed2/4/6 and original source PNG14/16/18. Historical integration baselines and allowed own append-only snapshots are bound, not silently overwritten.\n\n'
    'Inspect actual focused/whole-type VALUE/29 standard-only axioms/17 fences, root/Tests/full harness and real both-base contributor/own shadow logs. Original full harness1 rejects untracked Lean sources; repaired harness-v2 stages only the two reviewed files, no source/header/proof/harness/pin change. Confirm actual test counts from v2 log. Selected graph24nodes2676 coalesced TYPE_VALUEedges16 required direct VALUEpairs is not a full transitive graph or discovery. Preserve the prior F1 fence failure and Poppler renderer repair. Audit exact SHA-bound RAW log whitespace exceptions: production/Test/reader/contract have no exemption; do not claim the full unexcluded diff check passed if it failed.\n\n'
    'Personally view ALL twelve original images from formula-render-v1.json at original detail. Check every R1-R7 verbatim. Inspect browser/MathJax/geometry/folded Lean/wrapped five complete catalogue types, no clipping. Actual clean local site preserves10959 COMPLETE old shared registry records and adds exactly five production targets,19 source cards, five new notes, all old links/status retained. Generated HTML unchanged; local site is not live.\n\n'
    'Search for unconditional ordinary-limit existence, unsigned/zero-only regret, false nonnegativity for arbitrary algorithms, arbitrary unbounded-stream unit feasibility, future-mean algorithm input, supplied regret/mean oracle, loss of T0, true strict-past same-process connection. F1/F2 arbitrary-real algebra; F3/F4/F5 all-time unit stream; F4 equivalence only; F5 explicit mean convergence. Alternating canary proves its mean from prefix count and has fixed-zero limit -1/4. Concrete bounded oscillating obstruction and all-comparator converse remain REQUIRED. Original16/null/otherC1C2/C3-16/appendices remain required, GoalACTIVE, only five derived obligations can close.\n\n'
    'Inspect exact prospective PR title/body and future metadata scope. Favorable FINAL permits only scoped native/metadata acceptance followed by separate post-native audit and scoped draft delivery; no merge/deploy, global frontier/memory/retrieval changes or old proof changes. Distinct reused automated actors; requested Astra/medium not runtime-attested. Write ONLY final-reader-review-v1.md and final-reader-receipt-v1.json: verdict, fixed_input_count, reviewed_files including current index hash, raw_input_checks(path,before_sha256,after_sha256,unchanged), inputs_unchanged, report_sha256, required_blocking_repairs, reader_requirement_verdicts(R1-R7 exact requirement/verdict/evidence), actual_pixel_review(path,sha256,actually_viewed), permitted_future_metadata EXACT proposed scope if favorable. No input/native/git/site mutations.\n')
print('Current FINAL RAW inputs:',len(indexed),flush=True)
