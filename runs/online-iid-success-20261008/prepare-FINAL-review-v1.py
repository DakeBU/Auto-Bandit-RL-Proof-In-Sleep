from common_integrated_v2 import *

fixed_integrated()
render=load(RUN/'formula-render-v1.json')
assert len(render['images']) == 10
for row in render['images']: assert sha(row['path']) == row['sha256']
write(RUN/'pixel-review-v1.json', dict(actor='/root', method='Actual view_image(detail=original), ten images individually viewed in three tool calls',
    images=render['images'], all_images_actually_viewed=True,
    observations=['Source, four notes and four complete wrapped types are legible without horizontal clipping.',
        'The original pathwise Theorem 1.3 and expected derived applications are displayed separately.',
        'Policy iff does not assert all policies converge; meanPredict uses initial half and strictly earlier observations.',
        'No-independence upper and IID nonnegative success are distinguished, with T0 and min-outside-expectation boundaries.',
        'Whole Chapter 1/2 and universal-model/five-old-audit obligations remain open; first viewport explains local compiled route.'],
    generated_page_sha256=render['generated_page_sha256'], module_page_sha256=render['module_page_sha256'],
    distinct_FINAL_pixel_review_pending=True, chapter_complete=False, goal_complete=False))

title='Online Learning C1: IID success criterion and sample-mean convergence'
exceptions=load(RUN/'diff-raw-bound-exceptions-v2.json')['exceptions']
body='''This package connects the Chapter 1 stochastic success definition to the actual unknown-law sample-mean learner. It proves four shared results: centered total is little-o iff its average excess vanishes; the explicit private-seed/strict-history policy succeeds iff its Cesaro mean squared deviation vanishes; the actual mean learner has expected-fixed excess at most 4+4 log T without independence; and under joint IID its ordinary normalized excess tends to zero and its total excess is little-o. Source Theorem 1.3 supplies the pathwise regret bound. The last two results are derived applications, not additional numbered book statements.

The learner starts at 1/2 and then uses the empirical mean of strictly earlier targets. It receives no population mean, law or horizon. Predictions use one jointly measurable private-seed/history policy, with the tape independent of the whole target process and feasibility for every seed on legal unit histories. The IID target stream is one infinite probability process with measurable same-law, almost-sure [0,1] targets. Square integrability is derived. The comparator minimizes expected fixed loss outside expectation; it is not the expected hindsight minimum. A policy success equivalence does not make every policy successful. Normalization identities are used eventually for positive T; the generic T=0 discrepancy is retained.

Validation: actual shared Lean root (9099 jobs), Tests (9257 jobs), full `python tools/bandit.py check` (472 tests, 7 skips), 45 named kernel/axiom checks, four exact public proof values, four whole-proposition and three whole-definition identities, 14 required compiled VALUE pairs, native fences and scoped frontier shadow passed. The 14 named canary proofs include positive-variance infinite fair IID targets, the actual successful mean learner, a persistent independent private bit with excess T/4 and nonzero limiting normalized excess, a generic nonzero initial total, T=0, and a correlated repeated target for which the no-independence upper holds while two-round excess is negative.

The applicable clean local site was built from 1cffe4be362928fb80bfb9a0a7b0b77049840c3c after the combined Lean gate. It preserves all 10931 prior shared registry IDs, URLs and statement fingerprints and adds exactly four nodes. Four complete note/catalogue headers, source formulas, DOM checks and ten current original panel captures are bound to evidence. Distinct staged automated CONTRACT, BODY and final source/reader reviews are separate from compilation and native acceptance. Reused actor history is disclosed; there is no human/external, absolute blindness or model-runtime attestation, and no assertion that one runtime enforces the entire workflow.

Evidence and retained failures are in `runs/online-iid-success-20261008/`; the frozen contract is `docs/contracts/online-iid-success-v1/`. Preserved attempts include the draft renderer/import issue, typed API/universe audit repairs, two upper-proof repairs and commit-helper repairs. No mathematical header was weakened. The full unexcluded whitespace check exits 2 on exact raw logs and reviewed historical snapshots. Scoped checking passes with exactly EXCEPTIONS individually SHA-bound raw evidence exceptions, with zero production, test, reader, contract or executable-helper exemptions. The diff is large because it retains full immutable retrieval/baseline snapshots and the native generated blueprint as well as raw validation evidence; the production proof changes are confined to one new module, one canary and shared roots.

Stacked on OPEN draft, unmerged PR #195, exact head 372c9a6c138c50d7a5e08e91351238f231565219; base branch `codex/research-online-randomized-iid`. Canonical main remains 6847b678a73db68dee5101d6f05c2453c1405afc. The five older main-relative module audits remain required: the previous push contributor check fails on those missing contracts, while this package's committed stacked-base check passes for five production paths and one own contract. No CI bypass or covering manifest is invented.

This delivers four bounded terminals. Full stochastic-kernel/completed-information/AE-factorization source coverage, the five older audits, all original 16 Chapter 1 source objects with unknown/null proof total, full Chapters 1 and 2, unenumerated Chapters 3–16 and necessary appendices remain required. The whole-book Goal stays active. There is no high-probability, almost-sure, minimax, full strategy-class, merge, deployment or live update claim; the active worktree is retained.
'''.replace('EXCEPTIONS',str(len(exceptions)))
write(RUN/'prospective-PR-title-v1.txt',title)
write(RUN/'prospective-PR-body-v1.md',body)
write(RUN/'proposed-publication-v1.json',dict(operative=True,title_path=(RUN/'prospective-PR-title-v1.txt').relative_to(ROOT).as_posix(),
    title_sha256=sha(RUN/'prospective-PR-title-v1.txt'),body_path=(RUN/'prospective-PR-body-v1.md').relative_to(ROOT).as_posix(),
    body_sha256=sha(RUN/'prospective-PR-body-v1.md'),base_branch='codex/research-online-randomized-iid',base_head=BASE,
    branch=BRANCH,draft=True,PR_created=False,FINAL_pending=True,native_acceptance_pending=True,
    user_authorization='Approved scoped commit/push/reviewable draft PR; no merge/deploy',chapter_complete=False,goal_complete=False))
mutable=[MANIFEST]+[Path(p) for p in ['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl']]+APPEND_METADATA
if Path('research-wiki/retrieval-index/'+TASK+'.md').exists(): mutable.append(Path('research-wiki/retrieval-index/'+TASK+'.md'))
snapshots=[]
for p in mutable:
    s=RUN/'snapshots'/('FINAL-current-v1--'+p.as_posix().replace('/','--')+'.raw')
    write(s,p.read_bytes());snapshots.append(dict(live_path=p.resolve().as_posix(),snapshot=s.resolve().as_posix(),sha256=sha(p)))
write(RUN/'FINAL-metadata-snapshots-v1.json',snapshots)
write(RUN/'FINAL-review-packet-v1.md','''# Separate final source and reader audit

Reuse /root/source_reviewer, requested Astra/medium. Reused staged history is disclosed; no absolute blindness/human/external/runtime attestation. Search for mismatches. This is FINAL, not an automatic promotion of CONTRACT/BODY. Recheck pinned source printed1–2,4/PDF13–14,16, exact four full public proof bodies and 14 canaries, neutral decoder, CONTRACT/BODY receipts, actual kernel/type/VALUE/fence/combined/contributor/scoped-shadow/site/registry/DOM evidence. Verify every indexed raw binding before and after. Old indexed source presence or compilation does not recursively accept the five old modules. Original BODY bindings are preserved through exact reviewed immutable snapshots, never silently rehashed.

Personally view ALL TEN current v1 ORIGINAL PNGs through view_image(original), including first viewport, own source card, four notes and four complete wrapped types. ROOT's receipt does not substitute. Read exact current sourcecard JSON, generated HTML and original Eq1.1/1.2 and pathwise Theorem1.3. Copy R1–R8 EXACTLY from stabilized-contract-v1.json into per-ID requirement text/verdict/evidence. Distinguish generic signed S001, S002 iff from all-policy success, S003 upper without independence from S004 IID lower/success. The comparator is min expected fixed loss outside expectation. Population mean is proof comparator, never unknown-law algorithm input. One infinite process/learner precedes all horizons. Standard little-o/ordinary expected zero differs from adversarial upper-epsilon NoRegret; eventual T>0 and generic T0 discrepancy are explicit.

Review retained failures and diff repair: actual full unexcluded exit2 versus scoped exit0; only the exact finite SHA-bound raw logs or immutable reviewed snapshot exceptions in diff-raw-bound-exceptions-v2.json, no production/Test/reader/contract/executable exception. Own native status docs were APPENDED with actual combined-gate status; historical frozen bytes retained, not normalized. The commit-helper v2 filename substitution error is retained, repaired in v3; no commit or pass was inferred from it. Large evidence snapshots/blueprint are disclosed, not counted as mathematical progress.

proposed-publication-v1.json selects the ONE operative prospective title/body. Check these exact public bytes. They describe completed actual math/gates but do not assert future PR delivery/native acceptance already happened. Do not close chapter/program/universal model/five older audits or source16/null obligations. The new S001/S003/S004 progress may be recorded only within the four bounded frozen terminals and source-qualified subobligation, not full model coverage.

If accepted, permit ONLY future six manifest fields semantic_roundtrip.remaining_semantic_delta, graph_contribution.visual_review and verification.independent_review/bandit_check/site_build/site_check; all other current manifest, source and reader bytes immutable. Permit own-only status suffixes to the four task docs and global MANIFEST/journal prefixes; actual reviewer accepted trial/lifecycle/memory/retrieval records; new versioned bounded decision/obligation/ledger/digest/guard evidence under this RUN/CONTRACT; own TASK retrieval note. Future suffixes must have exact versioned raw hashes and semantic task ownership, not arbitrary prefix-only admission. Preserve original16 objects/null proof total and global SGB frontier. Future native records require actual commands and post-native audit. Scoped commits/push/draft delivery/app attachment may record actual heads/state and retain the checkout. Publish only the selected exact reviewed title/body. No merge/deploy/live claim.

Write ONLY final-reader-review-v1.md and final-reader-receipt-v1.json in this RUN. Receipt actor.task=/root/source_reviewer; verdict accepted|accepted-with-explicit-delta|rejected; report path/rawSHA; actual fixed_input_count; ALL indexed reviewed_files exact hashes; before_after_raw_hashes_match/inputs_unchanged; required_repairs/required_mathematical_repairs/required_metadata_repairs/required_blocking_reader_repairs arrays; exact R1–R8 reader_requirement_verdicts; all ten actual_original_pixel_reviews; seven_slot_verdicts; permitted_future_metadata as precise above or objection; exact prospective title/body hashes; remaining required scope. No other edits/state promotions/chapter or Goal acceptance. Return report/receipt hashes.
''')
paths=[]
for p,h in load(RUN/'body-review-inputs-v1.json')['fixed_inputs'].items():
    p=Path(p)
    if sha(p)!=h:
        rel=p.resolve().relative_to(ROOT)
        p=original(rel) if rel in READER_FILES else RUN/'snapshots'/('BODY-current--'+rel.as_posix().replace('/','--')+'.raw')
    assert sha(p)==h,p
    paths.append(p)
# Include top-level evidence/helper files plus only required immutable resolution snapshots.
paths += [p for p in RUN.iterdir() if p.is_file()]
paths += [p for p in CONTRACT.iterdir() if p.is_file()]
paths += [PUBLIC,CANARY,PDF]+READER_FILES+mutable
paths += [Path(x['snapshot']) for x in snapshots]
paths += [Path(e['path']) for e in exceptions]
paths += list(Path('research-wiki/retrieval-index').glob('*.json'))
site=Path('tmp/online-iid-success-site-v1');reg=load(RUN/'registry-v1.json')
paths += [site/'chapters/online-foundations/index.html',site/reg['module_path'],site/'books/registry.json',site/'site-manifest.json']
rows=[dict(path=p,sha256=sha(p)) for p in sorted({p.resolve().as_posix() for p in paths})]
write(RUN/'FINAL-review-inputs-v1.json',dict(schema='abrl.review-inputs.v1',phase='FINAL',contract_version=1,rows=rows,
    fixed_input_count=len(rows),original_CONTRACT_inputs=88,original_BODY_inputs=128,
    future_metadata_snapshots='FINAL-metadata-snapshots-v1.json',operative_publication='proposed-publication-v1.json',
    package_accepted=False,chapter_complete=False,goal_complete=False))
fixed_integrated()
print('Actual FINAL input count',len(rows),'; ten original images inspected by ROOT; separate FINAL pending.')
