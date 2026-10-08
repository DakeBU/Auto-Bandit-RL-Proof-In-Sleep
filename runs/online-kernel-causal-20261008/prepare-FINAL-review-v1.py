from common_body_v2 import *

fixed_integrated()
g = load(RUN/'combined-gates-v1.json')
assert g['actual_exit_codes'] == [0,0,0]
assert g['public_sha256'] == sha(PUBLIC) and g['canary_sha256'] == sha(CANARY)
reg = load(RUN/'registry-v2.json')
assert reg['preserved_complete_base_node_records'] == 10942
assert reg['new_public_declarations'] == 5 and reg['new_registry_nodes'] == 17
for label in ['site-build-v1','site-check-v1','registry-check-v2','formula-render-v1-node',
              'contributor-candidate-stacked-v2','contributor-candidate-origin-main-v2','candidate-frontier-shadow-v1']:
    assert load(RUN/(label+'-exit.json'))['actual_exit'] == 0
images = load(RUN/'formula-render-v1.json')['images']
assert len(images) == 12 and all(sha(x['path']) == x['sha256'] for x in images)
write(RUN/'pixel-review-v1.json',dict(actor='/root',actual_original_images_viewed=12,
    images=[dict(x,actually_viewed=True) for x in images],
    findings='All source/note formulae readable with no red unknown commands or clipping; five complete wrapped catalogue headers and folded Lean readers. Long repeated capture-time boundary text is retained; source-derived and chapter-incomplete scope is visible.',
    distinct_FINAL_pending=True,generated_HTML_unmodified=True))
write(RUN/'prospective-PR-title-v1.txt','Online Learning C1: causal behavioral kernels and IID expected excess')
write(RUN/'prospective-PR-body-v1.md',
    'Given a Markov decision-kernel family on generated unit-action and strict real-observation histories, this package selects one measurable sampler family before every observation law and horizon. An empty-start finite recursion produces the actual actions; prefix consistency and nonanticipation connect it to one infinite process. Fresh uniform-coordinate independence yields its joint law and the conditional kernel AE under the actual history marginal. Under IID unit observations, the same process has exact every-horizon expected-fixed regret equal to the sum of squared prediction deviations from the population mean, including horizon zero.\n\n'
    'These five frozen endpoints are derived infrastructure for Orabona arXiv:1912.13213v10 (2026-06-21), printed1/PDF13 and printed3/PDF15, not five printed theorems. The entire observation stream is exogenous and independent of the random tape; temporal dependence is allowed for realization, action-dependent adaptive environments are not covered. No arbitrary-protocol/filtration/private-state reduction, off-support conditional uniqueness, numerical sampler, convergence/rate, pathwise/high-probability upgrade or hindsight min/expectation swap is claimed. The population mean is analysis-only.\n\n'
    'The public canary switches a nondegenerate binary action kernel using both the last generated action and the last observation. All five public endpoints are instantiated. Actual predictions are binary AE by the proved joint law. With positive-variance IID Bernoulli observations, exact every-horizon excess is T/4, zero at T=0 and 1/2 at T=2; this is a diagnostic rather than a learning-rate result. Validation: five focused bodies,13canary proofs, whole public-type VALUE witnesses,57standard-only axiom outputs, frozen statement fences,22required direct VALUE dependencies, combined root/Tests and full harness (472tests,7skips), both contributor bases and own shadow. A clean applicable local site preserves10942complete old registry records plus17module records:5terminal theorems,8context definitions and4private helpers. Twelve original screenshots have separate formalizer and distinct source-reviewer inspection. Proof, compilation, EOF and registry-expectation failures and exact reviewed repairs are retained. Distinct automated roles have disclosed reused history; no human/external/absolute-blind or runtime-model attestation.\n\n'
    'Only these five derived obligations may close. Original16Chapter1 source objects and null unknown proof total remain; other source-required constructions, remaining Chapter1/2, unenumerated Chapters3-16 and necessary appendices are required. The full-book Goal stays ACTIVE. Stacked on OPEN draft unmerged PR199 exact'+BASE+'; base codex/research-online-completed-causal. Main and live site unchanged; no merge/deployment. Source contracts: docs/contracts/online-kernel-causal-v1. Separate CONTRACT/BODY/repair/FINAL/native/post-native/delivery evidence: runs/online-kernel-causal-20261008. The active worktree is retained for subsequent required work.\n')
scope = dict(manifest_fields=['semantic_roundtrip.remaining_semantic_delta','graph_contribution.visual_review',
    'verification.independent_review','verification.bandit_check','verification.site_build','verification.site_check'],
    own_metadata_only='Exact six own-manifest fields, four identical own-task appendices and parsed own task/session journal suffixes; actual native reviewer/lifecycle/own frontier-shadow/memory/retrieval commands and new versioned accepted ledger/decision/obligations/digest/delivery evidence. No global frontier or lifecycle memory change.',
    conditions=['Freeze all public/canary/root/Test/readers/pins and reviewed inputs/reports.',
        'Bind prechange RAW snapshots and exact parsed metadata changes; separate post-native review required.',
        'Five derived kernel obligations5->0 only; original16/null/source/chapter/Goal gaps remain required.',
        'Capture-time candidate reader status remains historical and immutable; acceptance is recorded separately.',
        'Scoped commit/push/draft with exactly reviewed PR title/body and immediate official app attachment after creation; no force/merge/deploy/live claim.'])
write(RUN/'FINAL-future-metadata-scope-v1.json',scope)
paths = [CONTRIBUTION,ROOT/'MANIFEST.md',ROOT/'runs/trials.jsonl',ROOT/'runs/lifecycle_sessions.jsonl',ROOT/'runs/lifecycle_memory.jsonl']
paths += [ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','proof-blueprints','conversion-windows']]
snapshots=[]
for i,p in enumerate(paths):
    q=RUN/'snapshots'/('FINAL-metadata-'+str(i)+'-v1.raw');write(q,p.read_bytes())
    snapshots.append(dict(live_path=p.as_posix(),snapshot=q.as_posix(),sha256=sha(q)))
write(RUN/'FINAL-metadata-snapshots-v1.json',snapshots)
rows={}
def add(p):
    p=Path(p).resolve();assert p.is_file()
    rows[p.as_posix()]=dict(path=p.as_posix(),sha256=sha(p))
for x in load(RUN/'body-review-inputs-v1.json')['rows']:add(x['path'])
for folder in [RUN,CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts:add(p)
for p in paths+[PUBLIC,CANARY,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',PDF]+READERS:add(p)
site=ROOT/'tmp/online-kernel-causal-site-v1'
for rel in ['books/registry.json','site-manifest.json','chapters/online-foundations/index.html']+list(reg['module_HTML_sha256']):add(site/rel)
for p in (ROOT/'research-wiki/retrieval-index').glob('*.json'):add(p)
write(RUN/'FINAL-review-inputs-v1.json',dict(phase='Five actual causal-kernel endpoints/public canary/readers/shared Book',
    rows=sorted(rows.values(),key=lambda x:x['path']),fixed_input_count=len(rows),
    original_CONTRACT_count=104,original_BODY_count=350,source_commit=reg['source_commit'],
    original_R1_R7=load(CONTRACT/'reader-requirements-v1.json'),future_metadata_scope=scope,
    allowed_outputs=['final-reader-review-v1.md','final-reader-receipt-v1.json'],chapter_complete=False,goal_complete=False))
write(RUN/'FINAL-review-packet-v1.md',
    'Anti-anchored FINAL: independently hash EVERY current indexed RAW input before/after. Reinspect actual5full public types/bodies,13public canary proofs, both neutral reconstructions, CONTRACT104/retrieval16/BODY350 and originalPDF13/15 pixels. Resolve historical350 root/readers via exact bound integration and the sole common_canary final-LF change via separate EOF22 repair. Old reports/indexes retain old RAW hashes. Audit new strict guard implementation and exact17-node audit repair; no claim old live files still match350.\n\n'
    'Inspect actual focused/whole-type VALUE/57standard-only axioms/five statement fences/root9102/Tests9264/fullharness472tests7skips/both contributor bases/own shadow. Selected compiled graph52nodes3106coalesced TYPE_VALUEedges22required directVALUEpairs is not a full graph/occurrence count/discovery. Personally view ALL12 original images from formula-render-v1.json with original detail. Review browser/math/geometry/wrap/full5catalogueheaders and exact frozen source reader scope. Actual10942complete old records preserved plus17module nodes:5terminals+8contextdefinitions+4privatehelpers,18sourcecards,5newnotes and old curated links retained. Initial5-node-expectation audit1 remains; separately reviewed precise17-node repair actually0. Site/HTML is unchanged.\n\n'
    'Check original R1-R7 verbatim individually. Search for given kernels versus arbitrary protocol reduction, whole-stream exogeneity versus action-dependent environments, single-family witness before laws/horizons, true recursion/strict-past information, assumed fresh-draw independence or desired laws, all-history sampler equality versus AE conditional equality, actual same-process IID expectedFixed identity, infimum outsideE versus hindsight min, T0, numerical sampler or rate claims. Canary: both last-action and last-observation switch dependence; actual binary support from K3; same selected K5 witness, no identity with arbitrary separately existing K1 witness; no unsupported positive-probability history-event claim. ExactT/4 is not learning success.\n\n'
    'Inspect prospective PR title/body, common_accepted_v1.py, record-acceptance-v1.py and post-native/commit/delivery helpers as FUTURE, not actual native acceptance/publication. The six current global retrieval indexes are unchanged since draft; required own retrieval record/index will reference5actual compiled targets; no general scanner refresh or global frontier/lifecycle_memory change. Original16/null arbitrary-protocol/other source-required constructions/remainingC1C2/unenumeratedC3-16/necessaryappendices required, whole Goal ACTIVE. Capture-time candidate pending phrases are historical; future acceptance changes no reader bytes. Only5derived obligations may close. Reused distinct automated actors, requested Astra/medium, no human/external/absolute-blind/runtime attestation.\n\n'
    'Write ONLY final-reader-review-v1.md and final-reader-receipt-v1.json: fixed_input_count, reviewed_files (include current index hash), raw_input_checks(path,before_sha256,after_sha256,unchanged), inputs_unchanged, report_sha256, verdict, required_blocking_repairs; reader_requirement_verdicts R1-R7 exactrequirement/verdict/evidence; actual_pixel_review(path,sha256,actually_viewed); permitted_future_metadata EXACT proposed scope only if accepted. Do not edit inputs or run native/publication actions.\n')
print('Actual FINAL fixed RAW count:',len(rows),flush=True)
