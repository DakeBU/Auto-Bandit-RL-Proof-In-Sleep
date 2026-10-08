from common_integrated_v2 import *

fixed_integrated()
render = load(RUN/'formula-render-v3.json')
assert len(render['images']) == 13
for row in render['images']:
    assert sha(row['path']) == row['sha256']
write(RUN/'pixel-review-v3.json', dict(
    actor='/root', method='Actual view_image(detail=original), all13 images in three calls before continuation compaction',
    images=render['images'], all_images_actually_viewed=True,
    observations=['All13 current original panels are legible with no horizontal clipping.',
        'Source card retains whole-tape independence, strict past, legal cube, min expected fixed loss, finite scope and required remaining source obligations.',
        'Seven notes distinguish their actual local hypotheses; generic R001 and R003 do not inherit the complete endpoint assumptions.',
        'Exact Lean remains folded. Four catalogue types were wrapped with the builtin control and appear complete.',
        'First viewport explicitly distinguishes canonical compiled route from complete textbook coverage.'],
    generated_page_sha256=render['generated_page_sha256'], module_page_sha256=render['module_page_sha256'],
    distinct_FINAL_pixel_review_pending=True, chapter_complete=False, goal_complete=False))

title = 'Online Learning C1: private-seed and strict-past IID excess producer'
body = '''This package derives current-target independence for predictions using an independent private tape and strict past, then proves the finite expected-fixed excess identity for the same stream and prefix. The explicit jointly measurable seed/history policy instantiates the subordinate-information endpoint. It adds seven shared proofs and one information definition, reusing the fixed-loss benchmark in PR #194.

The tape is independent of the whole infinite target process. The target family is jointly IID, measurable and a.s. in [0,1]. Policy feasibility is required for every seed only on legal unit histories. The comparator minimizes expected fixed loss outside expectation; this is not the expected hindsight minimum. Source rounds 1..T correspond to Lean 0..T-1, with a disclosed empty-prefix T=0 extension. These are derived producer/interface results, not seven printed book statements or a new rate.

Validation: actual combined root (9098 jobs), Tests (9255 jobs), full `python tools/bandit.py check` (472 tests, 7 skips), 55 named kernel/axiom checks, exact public/canary type and whole-definition checks, 26 direct compiled VALUE pairs, 36 native fences, and scoped frontier shadow passed. The 29 named canaries include an infinite IID stream with an independent fair private bit, actual two-round excess 1/2, T=0, forbidden current information, an off-cube-unbounded policy, and an XOR model showing pairwise independence is insufficient. The clean local site built from f8c25ea9e5e43841410c0449cb226650cdb057cb preserves all 10923 prior registry IDs/URLs/statement hashes and adds eight nodes in the same shared Lean registry; all 13 current panels and formula/DOM checks are bound to evidence.

Distinct staged automated decoder/source-reviewer CONTRACT and BODY reviews are recorded. Final reader/source review and native acceptance are required separately before this exact draft PR is created. Reused role history is disclosed; there is no human/external, absolute blindness or model-runtime attestation, and no claim that one runtime enforces the whole workflow. Evidence is in `runs/online-randomized-iid-20261008/`; the frozen v2 contract is in `docs/contracts/online-randomized-iid-v1/`.

Original failed attempts are preserved, including the untracked-source harness failure (repaired by tracking only), arithmetic/instance/audit-generator repairs, obsolete guessed-hash/prefix helper guard, stdout-parser error, and reader-only corrections. Full unexcluded whitespace checking exits 2 on retained raw stdout. Scoped checking passes with exactly five SHA-bound raw stdout exceptions and no production, test, reader, contract or executable-helper exemption. The full diff is large because it retains raw review snapshots and validation evidence; proof edits are confined to one new public module, one canary and the shared roots.

Stacked on OPEN draft, unmerged PR #194, exact head b08f8312259ae10032b6318060e18911532d4610; base branch `codex/research-online-iid`. Canonical main remains separate. No merge, deployment, live update or worktree retirement is included.

The Chapter 1 original 16 source items and unknown/null required proof total are preserved. Universal-kernel/completed-information/AE-factorization source coverage audit, source asymptotic-success equivalence and five old main-relative source-module audits remain required. Chapters 1 and 2 remain open; Chapters 3-16 remain unenumerated and necessary appendices remain required. The whole-book Goal stays active. This draft PR delivers only the bounded independent-private-tape/subordinate-information finite producer.
'''
write(RUN/'prospective-PR-title-v3.txt', title)
write(RUN/'prospective-PR-body-v3.md', body)
write(RUN/'proposed-publication-v3.json', dict(
    operative=True, title_path=(RUN/'prospective-PR-title-v3.txt').relative_to(ROOT).as_posix(),
    title_sha256=sha(RUN/'prospective-PR-title-v3.txt'),
    body_path=(RUN/'prospective-PR-body-v3.md').relative_to(ROOT).as_posix(),
    body_sha256=sha(RUN/'prospective-PR-body-v3.md'), base_branch=BASE_BRANCH, base_head=BASE,
    branch=BRANCH, draft=True, PR_created=False, FINAL_pending=True, native_acceptance_pending=True,
    user_authorization='Scoped commits, push and reviewable draft PR; no merge/deploy',
    chapter_complete=False, goal_complete=False))

mutable = [MANIFEST] + [Path(p) for p in ['MANIFEST.md', 'runs/trials.jsonl',
    'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl']] + OWN_METADATA
assert len(mutable) == 10
snapshots = []
for p in mutable:
    s = RUN/'snapshots'/('FINAL-current-v3--'+p.as_posix().replace('/','--')+'.raw')
    write(s, p.read_bytes())
    snapshots.append(dict(live_path=p.resolve().as_posix(), snapshot=s.resolve().as_posix(), sha256=sha(p)))
write(RUN/'FINAL-metadata-snapshots-v3.json', snapshots)
write(RUN/'FINAL-review-packet-v3.md', '''# Distinct final source/reader audit of bounded private-seed IID producer

Reuse /root/source_reviewer, requested Astra/medium. History is disclosed; no external/human/absolute-blind/runtime attestation. Search for mismatch. CONTRACT/BODY acceptance is not FINAL acceptance. Read pinned source pp.1-2/PDF13-14, actual public and canary bodies, neutral decoder, source/BODY reports, original R1-R7, operative fingerprint/DAG, exact type/kernel/VALUE/canary/fence and actual combined/native/site evidence. Check all indexed raw bytes before/after. View ALL13 current v3 ORIGINAL PNGs using view_image(original); ROOT's pixel receipt is not a substitute. Read exact current JSON readers, generated HTML, formulas and complete wrapped catalogue types.

R1-R7 must be copied EXACTLY from reader-requirements-v2.json into per-ID verdicts with requirement text, satisfied|blocking, concrete evidence and reasoning. Compare all seven semantic slots. No pairwise replacement of whole-tape/joint IID independence, no global off-cube bound, no given current independence, no expected hindsight minimum, no general kernel/completed-information representation or asymptotic result. General supplied subordinate trace R006 and real policy producer R007 remain distinct. R001/R003 local hypotheses are generic. Derivation and all29 nondegenerate canaries must be actual proof values, not supplied regret certificates.

Review the tracking-only harness repair, parser error, historical incorrect guessed-full-hash OR actual-prefix guard explicitly disclosed/superseded, earlier reader context repair, and preserved failed attempts. Full unexcluded diff exits2; exactly five individually SHA-bound raw stdout exceptions only, zero production/Test/reader/contract/helper exemptions. Decide whether the scoped diff preserves faithful raw evidence without concealing code findings. All original source16/null/fullC1/C2/3-16/appendix/oldfive/kernel/asymptotic obligations remain required. Source item completion is zero for this bounded subobligation. Goal active; exact PR194 b08 stack remains OPENdraft/unmerged, separate from main/live.

proposed-publication-v3.json is the ONE operative title/body selection. Review those exact prospective public bytes. Final review cannot assert PR delivery has happened. Proposed title/body explicitly explain large evidence diff, current finite model and all remaining obligations.

If accepting, permit ONLY these future metadata changes with immutable original snapshots and guards: manifest fields semantic_roundtrip.remaining_semantic_delta; graph_contribution.visual_review; verification.independent_review/bandit_check/site_build/site_check. All other manifest fields and current readers remain immutable. Permit own-only suffix appends to the four global journals/MANIFEST and five own task docs, actual accepted reviewer trial/lifecycle/memory/retrieval entries, separate accepted scoped frontier/shadow, new versioned own accepted decision/source-ledger overlay/digest/retrieval/obligation evidence. Old source inventory16 and proof-totalnull remain immutable. Native updates must actually run; none are already accepted by this proposal. No global SGB changes. Future commit/delivery raw records may be added only under this RUN. Publish ONLY the exact selected reviewed title/body, actual draft PR and app attachment, recording exact local/remote/PR heads, OPEN/unmerged and no live claim. User approval scope already exists.

Write ONLY final-reader-review-v3.md and final-reader-receipt-v3.json in this RUN. Receipt actor.task=/root/source_reviewer, verdict accepted|accepted-with-explicit-delta|rejected, report path/rawSHA, actual fixed_input_count, ALL indexed reviewed_files raw hashes plus input-index/report, before_after_raw_hashes_match, inputs_unchanged, required_repairs/required_mathematical_repairs/required_metadata_repairs/required_blocking_reader_repairs arrays, reader_requirement_verdicts R1-R7 EXACT requirements, all13 actual_original_pixel_reviews, seven_slot_verdicts, permitted_future_metadata precisely as proposed or objections, exact proposed_publication title/body hashes and separate remaining-required scope. No other edits, no state promotions, no chapter/Goal acceptance. Return raw report/receipt hashes.
''')

paths = []
for row in load(RUN/'BODY-review-inputs-v2.json')['rows']:
    p = Path(row['path'])
    if sha(p) != row['sha256']:
        assert p.resolve() in {x.resolve() for x in OWN_METADATA}, p
        p = RUN/'snapshots'/('BODY-reviewed--'+p.relative_to(ROOT).as_posix().replace('/','--')+'.raw')
    assert sha(p) == row['sha256'], p
    paths.append(p)
paths += [p for root in [RUN, CONTRACT] for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths += [PUBLIC, CANARY, PDF, Path('BanditRLProof.lean'), Path('Tests.lean')]
paths += [Path('website/content')/p for p in ['readings.json','highlights.json','chapters.json']]
paths += list(Path('research-wiki/retrieval-index').glob('*.json'))
paths += mutable
site = Path('tmp/online-randomized-iid-site-v3')
registry = load(RUN/'registry-v3.json')
paths += [site/'chapters/online-foundations/index.html', site/registry['module_path'], site/'books/registry.json', site/'site-manifest.json']
rows = [dict(path=p, sha256=sha(p)) for p in sorted({p.resolve().as_posix() for p in paths})]
write(RUN/'FINAL-review-inputs-v3.json', dict(schema='abrl.review-inputs.v1', phase='FINAL',
    contract_version=2, rows=rows, fixed_input_count=len(rows), original_CONTRACT_inputs=1143,
    original_BODY_inputs=1582, future_metadata_snapshots='FINAL-metadata-snapshots-v3.json',
    operative_publication='proposed-publication-v3.json', package_accepted=False,
    chapter_complete=False, goal_complete=False))
fixed_integrated()
print('FINAL inputs', len(rows), '; actual pixels recorded, distinct FINAL/native/draft delivery pending.')
