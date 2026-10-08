from common_reader_v5 import *

fixed_integrated()
g = load(RUN / 'combined-gates-v1.json')
assert g['actual_exit_codes'] == [0, 0, 0]
assert g['public_sha256'] == sha(PUBLIC) and g['canary_sha256'] == sha(CANARY)
pixels = load(RUN / 'pixel-review-v5.json'); reg = load(RUN / 'registry-v5.json')
assert pixels['actual_original_images_viewed'] == 10
assert all(sha(x['path']) == x['sha256'] for x in pixels['images'])
for label in ['site-build-v5', 'site-check-v5', 'registry-check-v5',
              'contributor-current-stacked-v5', 'contributor-current-origin-main-v5',
              'candidate-frontier-shadow-v1']:
    assert load(RUN / (label + '-exit.json'))['actual_exit'] == 0
write(RUN / 'prospective-PR-title-v1.txt',
      'Online Learning C1: completed-information real versions and causal excess')
write(RUN / 'prospective-PR-body-v1.md',
    'For real predictions measurable on the exact ambient-mu null augmentation of F (sets ambient-mu AE equal to F-measurable sets), this package constructs an actual F-measurable version. If each F_t is below private-seed plus strict-past information and original predictions are [0,1]-valued almost everywhere at EVERY natural time, one globally unit-valued history-policy family agrees with the original process on one event for all times. Under measurable joint-independent targets and a measurable seed independent of the WHOLE infinite target stream it derives ORIGINAL current-target independence; with IID unit targets and AE unit original predictions it proves the exact ORIGINAL expected-fixed excess identity and nonnegativity for every natural horizon, including zero.\n\n'
    'These are four derived formalization targets for Orabona v10 printed1/PDF13 and printed3/PDF15, not four printed theorems. The core uses countable coding of the REAL output and a measurable inverse; it assumes no probability/finiteness/F<=ambient/countability on Omega. Ambient null augmentation is not identified with completion of mu.trim F, and no arbitrary-output version theorem is claimed. Representation is classical and law-relative; original off-null predictions need not be causal or unit. The population mean is analysis-only. The benchmark is minimum EXPECTED fixed unit-comparator loss outside expectation; there is no rate, convergence, pathwise or high-probability upgrade.\n\n'
    'The actual completed-but-not-ordinary canary has a nonempty null branch and is not pointwise predictable or everywhere unit. Its private random seed and positive-variance IID targets give two-round ORIGINAL excess1/2. All four public proofs are instantiated. Validation includes four focused bodies,11named canary proofs, complete public-type proof VALUE witnesses,56named standard-only axiom records,52selected compiled nodes/2614coalesced TYPE_VALUE edges/18required direct VALUE pairs, frozen statement fences, combined root/Tests/full harness, both contributor bases, own shadow, and an applicable clean local site. All10938old complete registry node records are preserved; four new declarations share the Online Learning Book graph. Ten original current reader/catalogue images receive separate formalizer and source-reviewer inspection. Actual Lean/type-printer/receipt-reader/capture-output filename/red-command rendering failures are retained with exact repairs. Distinct staged automated actors have disclosed reused history; no human/external/absolute-blind or runtime-model attestation. FINAL/native/post-native and draft-delivery evidence are separately recorded.\n\n'
    'Only these four derived obligations may close. Original16Chapter1 source objects/null unknown proof total, general causal stochastic-kernel realization, other source-required information/completion constructions, remaining Chapter1/2, unenumerated Chapters3-16 and necessary appendices remain REQUIRED; whole Goal ACTIVE. Stacked on OPEN draft unmerged PR198 exact' + BASE + ', base codex/research-online-ae-causal. Main/live remain unchanged; no merge/deployment. Evidence: docs/contracts/online-completed-causal-v1 and runs/online-completed-causal-20261008. Active worktree retained for the next required bridge.\n')
scope = dict(
    manifest_fields=['semantic_roundtrip.remaining_semantic_delta', 'graph_contribution.visual_review',
        'verification.independent_review', 'verification.bandit_check',
        'verification.site_build', 'verification.site_check'],
    own_metadata_only='Append exact own-task four status suffixes and task/session journal rows; actual reviewer trial/lifecycle/memory/retrieval commands, own versioned accepted ledger/decision/digest/obligations and scoped delivery evidence. No global SGB replacement.',
    conditions=['Freeze public/canary/root/Test/readers/pins and all reviewed receipts/inputs.',
        'Bind exact prechange RAW metadata snapshots, six manifest fields and every parsed owned native suffix; separate post-native review required.',
        'Close only four derived completion obligations4->0; no original source-object/chapter/whole Goal completion.',
        'Keep capture-time candidate readers immutable and record later acceptance separately.',
        'Publish only exact reviewed PR title/body after favorable FINAL/native gates using scoped commit/push/draft/official app attachment evidence; no merge/deploy/live claim.'])
write(RUN / 'FINAL-future-metadata-scope-v1.json', scope)
paths = [MANIFEST, ROOT / 'MANIFEST.md', ROOT / 'runs/trials.jsonl',
    ROOT / 'runs/lifecycle_sessions.jsonl', ROOT / 'runs/lifecycle_memory.jsonl']
paths += [ROOT / d / (TASK + '.md') for d in
          ['tasks', 'proof-obligations', 'proof-blueprints', 'conversion-windows']]
snapshots = []
for i, p in enumerate(paths):
    q = RUN / 'snapshots' / ('FINAL-metadata-' + str(i) + '-v1.raw')
    write(q, p.read_bytes())
    snapshots.append(dict(live_path=p.as_posix(), snapshot=q.as_posix(), sha256=sha(q)))
write(RUN / 'FINAL-metadata-snapshots-v1.json', snapshots)
bindings = []
body_rows = {x['path']: x for x in load(RUN / 'body-review-inputs-v1.json')['rows']}
for p in [ROOT / 'BanditRLProof.lean', ROOT / 'Tests.lean'] + READERS:
    old = body_rows[p.as_posix()]
    row = next(x for x in load(RUN / 'draft-baseline-v1.json')['rows']
               if x['path'] == p.relative_to(ROOT).as_posix())
    assert sha(ROOT / row['snapshot']) == old['sha256']
    bindings.append(dict(live_path=p.as_posix(), original_sha256=old['sha256'],
                         original_snapshot=(ROOT / row['snapshot']).as_posix(), current_sha256=sha(p)))
write(RUN / 'BODY-mutable-integration-bindings-v1.json', dict(rows=bindings,
    exact_approved_root_reader_integration=True, old_reader_entries_preserved=True))
rows = {}
def add(p):
    p = Path(p).resolve(); assert p.is_file()
    rows[p.as_posix()] = dict(path=p.as_posix(), sha256=sha(p))
for row in load(RUN / 'body-review-inputs-v1.json')['rows']: add(row['path'])
for folder in [RUN, CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts: add(p)
for p in paths + [PUBLIC, CANARY, ROOT / 'BanditRLProof.lean', ROOT / 'Tests.lean', PDF] + READERS: add(p)
site = ROOT / 'tmp/online-completed-causal-site-v5'
for rel in ['books/registry.json', 'site-manifest.json', 'chapters/online-foundations/index.html'] + list(reg['module_HTML_sha256']): add(site / rel)
for p in (ROOT / 'research-wiki/retrieval-index').glob('*.json'): add(p)
write(RUN / 'FINAL-review-inputs-v1.json', dict(
    phase='Actual four completed-information proof package/readers/shared Book',
    rows=sorted(rows.values(), key=lambda x: x['path']), fixed_input_count=len(rows),
    original_CONTRACT_count=175, original_BODY_count=285, source_commit=reg['source_commit'],
    original_R1_R7=load(CONTRACT / 'reader-requirements-v1.json'), future_metadata_scope=scope,
    allowed_outputs=['final-reader-review-v1.md', 'final-reader-receipt-v1.json'],
    chapter_complete=False, goal_complete=False))
write(RUN / 'FINAL-review-packet-v1.md',
    'Distinct anti-anchored FINAL: independently hash EVERY indexed RAW file before/after. Reinspect actual four full public types and bodies,11actual canary proofs, decoder/CONTRACT175/BODY285 and original PDF13/15 pixels. Resolve original CONTRACT175 through exact seven stabilized snapshots; original BODY285 through the exact five BODY-mutable-integration-bindings-v1 snapshots for changed root/readers. Do not claim changed live integration files match original RAW.\n\n'
    'Inspect actual combined root/Tests/full harness logs and artifacts, four whole proposition proof VALUE checks,56standard-only axioms,52selected nodes2614coalesced TYPE_VALUE edges18required direct VALUE pairs, exact fences and both contributor bases/own shadow. Personally use view_image original on ALL TEN images in formula-render-v5.json. Review actual v5 browser math/geometry/wrap checks including red unknown-command detection and v5-named outputs; preserve actual v3 success/v1-named output audit-v4 and its failed outer filename lookup. Formalizer original pixel review found red unknown command missed by mjx-merror alone, exact empty-group repair-v5 changes no mathematics and original pixels separately. Check10938old COMPLETE registry node records preserved, exactly4new public declarations,17source cards/four new notes/four old curated links, full four headers and actual same Online Learning graph ownership. No generated _site edited.\n\n'
    'Original R1-R7 must each be reviewed verbatim with verdict/evidence. Search for completion of trim versus ambient-null augmentation confusion, real codomain regularity/instance leakage, supplied version instead of producer, AE versus off-null claim, missing original AEunit at every time, one common all-time event/family, whole-stream seed versus current independence, expected fixed min outsideE versus hindsight min, T0 and unjustified convergence/rate claims. Core no probability/F<=ambient/Omega regularity; policy no probability/ambient seed-target measurability; independence no support/same-law/bounds/integrability.\n\n'
    'Review exact prospective PR title/body and source-card aligned line-break/shorter truthful badge repair and actual two overflow failures and FINAL-future-metadata-scope-v1 independently. Preserve actual proof/type-printer/receipt-schema and actual horizontal-overflow failure versions and disclosed unsaved outer stderr. Native acceptance/post-native/delivery remain FUTURE. Only4derived obligations may close after gates; original16/null/general kernel/other required information constructions/full remaining chapters/appendices remain REQUIRED, whole Goal ACTIVE. Distinct reused automated actors, requested Astra/medium only; no absolute blind/human/external/runtime attestation.\n\n'
    'Write ONLY final-reader-review-v1.md and final-reader-receipt-v1.json. Include independently checked fixed_input_count, reviewed_files, raw_input_checks(path,before_sha256,after_sha256,unchanged), inputs_unchanged, report_sha256, verdict, required_blocking_repairs, reader_requirement_verdicts keyed R1-R7 with exact requirement/verdict/evidence, actual_pixel_review rows(path,sha256,actually_viewed), and permitted_future_metadata exactly the proposed scope ONLY if accepted. Do not edit inputs or execute native/publication actions.\n')
print('Actual FINAL fixed RAW input count:', len(rows), flush=True)
