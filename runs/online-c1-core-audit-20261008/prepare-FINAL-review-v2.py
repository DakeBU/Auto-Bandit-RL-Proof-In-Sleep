from common_reader_repair_v2 import *

fixed_integrated()
g=load(RUN/'combined-gates-v1.json');assert g['actual_exit_codes']==[0,0,0]
reg=load(RUN/'registry-v2.json');pixels=load(RUN/'pixel-review-v2.json')
assert pixels['actual_original_images_viewed']==26
assert all(sha(x['path'])==x['sha256'] for x in pixels['images'])
for label in ['contributor-repaired-stacked-v2','contributor-repaired-origin-main-v2','site-check-v2','registry-check-v2']:
    assert load(RUN/(label+'-exit.json'))['exit_code']==0
title='Online Learning C1: audit five legacy core modules and preserve exact assumptions'
body='''Five existing Chapter 1 modules lacked current source-audit contracts in the main-relative contributor gate. This package audits their twelve existing public proofs, documents the exact assumptions, and adds concrete public canaries. Production changes are five reviewed documentation comments; existing Lean statements and proof bodies are preserved. There are no new production theorems or registry nodes.

The audit distinguishes supplied hindsight prefix minimizers from a causal learner, given independence from actual strict-past independence producers, and the legacy pointwise target/global history bounds from the later AE/legal-history APIs. The population mean remains an analysis comparator. The positive-horizon scalar normalization identity is not a convergence theorem. Historical Foundation acceptance is retained.

Validation: focused canaries, twelve complete proposition/proof-value checks, 68 named axiom checks with standard Lean axioms only, 70 compiled dependency nodes with 19 required direct VALUE pairs, unchanged statement/body fences, combined root/Tests/full harness (472 tests; 7 skips), both stacked and origin/main contributor checks, scoped shadow, and an applicable clean local site. All 10935 shared registry IDs, URLs and statement hashes are preserved. Twenty-six current original reader/catalogue panels undergo separate formalizer and source-reviewer inspection. The first archive reproducibility failure is retained; the focused assertion and complete harness passed on an unchanged raw source snapshot. No test, archive builder or anonymous material was changed or waived. Full raw whitespace diagnostics and exact evidence-only exceptions are retained; production, tests, readers, contracts and active helpers pass the scoped check.

Distinct automated decoder and source reviewer performed CONTRACT, BODY and FINAL stages. They have disclosed prior staged history; these are not human/external reviews or runtime/model attestations. Accepted scope is only these five source-module audit obligations after the recorded FINAL/native gates. The original sixteen Chapter 1 source objects and unknown proof total, universal stochastic-kernel/completed-information/AE-factorization coverage, remaining Chapter 1/2, unenumerated Chapters 3–16 and required appendix obligations remain required. The whole-book Goal remains active.

Stacked on OPEN draft, unmerged PR #196 at exact head 6b387a39e401cb1b90003fca6e49d3bdd9ce7a9a. Canonical main and the live site are unchanged. This draft does not authorize merge or deployment. Evidence: docs/contracts/online-c1-core-audit-v1 and runs/online-c1-core-audit-20261008. The worktree is retained for the next required obligation.
'''
write(RUN/'prospective-PR-title-v2.txt',title)
write(RUN/'prospective-PR-body-v2.md',body)
fields=[['semantic_roundtrip','remaining_semantic_delta'],['graph_contribution','visual_review'],
        ['verification','independent_review'],['verification','bandit_check'],
        ['verification','site_build'],['verification','site_check']]
scope=dict(manifest_fields=['.'.join(x) for x in fields],
    own_metadata_only='Append exact own task status suffixes; own task/session rows in journals; actual reviewer trial/lifecycle/memory/retrieval commands; versioned decisions, obligations, ledger, digest, guards and delivery evidence under own RUN/CONTRACT and own retrieval note.',
    conditions=['Freeze all public Lean, canary, Tests root, readers, pins, other manifest fields and every existing receipt/input.',
        'Resolve original CONTRACT93/BODY185 mutable files through the already approved immutable baseline snapshots, not by pretending current RAW hashes match.',
        'Inspect and bind every exact native suffix and task/session ownership; startswith alone is insufficient. A separate post-native audit is required.',
        'Close only five source-module audit obligations (5 to 0), no new production proof; preserve historical Foundation acceptance, original16/null and universal/full chapter obligations.',
        'Reader candidate text is an immutable capture-time boundary. Record later scoped acceptance in own versioned ledger/decision and PR, not by altering frozen readers.',
        'Only the exact prospective title/body after FINAL approval; actual scoped commit/push/draft/app attachment, no predicted delivery/head, no merge/deploy/live/chapter/Goal completion.'])
write(RUN/'FINAL-future-metadata-scope-v2.json',scope)
paths=[MANIFEST,Path('MANIFEST.md'),Path('runs/trials.jsonl'),Path('runs/lifecycle_sessions.jsonl'),Path('runs/lifecycle_memory.jsonl')]
paths += [Path(d)/(TASK+'.md') for d in ['tasks','proof-obligations','proof-blueprints','conversion-windows']]
snapshots=[]
for i,p in enumerate(paths):
    if not p.exists(): continue
    q=RUN/'snapshots'/('FINAL-metadata-'+str(i)+'-v2.raw')
    write(q,p.read_bytes());snapshots.append(dict(live_path=p.resolve().as_posix(),snapshot=q.resolve().as_posix(),sha256=sha(q)))
write(RUN/'FINAL-metadata-snapshots-v2.json',snapshots)
rows={}
def add(p):
    p=Path(p).resolve();assert p.is_file();rows[p.as_posix()]=dict(path=p.as_posix(),sha256=sha(p))
for folder in [RUN,ROOT/CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts: add(p)
for p in MODULES+READERS+[CANARY,Path('Tests.lean'),Path('BanditRLProof.lean'),PDF,
    Path('lean-toolchain'),Path('lakefile.lean'),Path('lake-manifest.json'),MANIFEST]: add(p)
for p in paths:
    if p.exists():add(p)
site=ROOT/'tmp/online-c1-core-audit-site-v2'
for p in ['books/registry.json','site-manifest.json','chapters/online-foundations/index.html']+list(reg['module_HTML_sha256']):add(site/p)
for p in Path('research-wiki/retrieval-index').glob('*.json'):add(p)
index=dict(phase='Repaired FINAL bounded five-module source audit and current reader/site recommendation',
    rows=sorted(rows.values(),key=lambda x:x['path']),original_contract_input_count=93,original_BODY_input_count=185,rejected_FINAL_input_count=419,reader_repair=(CONTRACT/"reader-repair-v3.json").as_posix(),
    source_commit=reg['source_commit'],reader_requirements=load(CONTRACT/'reader-requirements-v1.json'),
    future_metadata_scope=scope,chapter_complete=False,goal_complete=False)
write(RUN/'FINAL-review-inputs-v2.json',index)
write(RUN/'FINAL-review-packet-v2.md','''Review the fixed RAW index before and after. This is F1 repaired FINAL v2. Preserve the rejected419/report/receipt and all old images. Verify original419 bindings through exact FINAL-v1-mutable-reader-repair-bindings-v2 snapshots for only highlights/trials/lifecycle; compare the one math-field delta and own native rejection/repair rows. Inspect all26 fresh original images, especially note4 now displays averaging only at t>0; same all-natural-time independence remains. No mathematical repair or new production proof occurred. Search for mismatch rather than confirming the formalizer. You are the distinct reused source reviewer, not the formalizer, and retain prior staged history. Requested GPT-6 Astra / medium; no runtime attestation.

Personally view all 26 original current images in formula-render-v2.json with view_image original. Inspect full twelve types, actual bodies/comments, actual canaries including seven historical Foundation proofs, reviewer reconstruction, original source PDF/pixels, stronger legacy API bounds, fixed-vs-hindsight comparator and algorithm information order. Separately verify complete gate receipts and actual logs, failed harness and stable rerun, RAW/Git LF dual bindings, actual main-relative and stacked contributors, zero-new-node shared registry and current rendered formulas/folded exact types. The active helpers have no diff exemption; exact raw failed snapshots/log exceptions are evidence only. Original source16/null/global SGB and full universal/source chapter obligations remain required.

Return FINAL accepted | rejected | accepted-with-explicit-delta, seven semantic slots and exact unchanged R1–R8 per-row verdict/evidence. No native acceptance or publication has happened in this review. Examine exact prospective title/body and future metadata scope separately. Reader candidate text is immutable historical capture-time status; later acceptance must be versioned separately. Preserve all old inputs/receipts. Only five audit obligations may close; no proof-count/chapter/program completion. If future metadata scope acceptable, copy it exactly into permitted_future_metadata. Output final-reader-review-v2.md and final-reader-receipt-v2.json with RAW hashes before/after, actual personally viewed pixel rows, fixed input count, no misleading independence/runtime claims, blockers and exact remaining scope. Append the input index/report hashes to reviewed rows; do not alter any input or script.
''')
print('FINAL fixed RAW inputs',len(index['rows']),'native/draft delivery still pending',flush=True)
