from publication_guard_v1 import *
fixed()
for label in ['site-build-v1', 'site-check-v1', 'registry-command-v1',
        'reader-file-browser-capture-command-v1', 'contributor-stack-v1', 'contributor-main-v1']:
    assert load(RUN / (label + '.json'))['actual_exit'] == 0, label
reg = load(RUN / 'registry-inspected-v1.json')
browser = load(RUN / 'formula-render-v1-browser.json')
assert reg['source_commit'] == '2b929d03d7ace7c418986e429d0ccf317a2721c6'
assert len(browser['images']) == 15 and not browser['errors'] and not browser['failed']
assert browser['url'].startswith('file:///') and browser['actualSourceGuideMathContainers'] == 12
for row in load(RUN / 'browser-generated-inputs-before-v1.json')['rows']:
    assert sha(row['path']) == row['sha256']
# Run only after /root personally viewed all listed originals with view_image original.
write(RUN / 'root-reader-pixel-review-v1.json', dict(actor='/root',
    images=rows(RUN / n for n in browser['images']), image_count=15, tool='view_image detail original',
    source_commit=reg['source_commit'],
    observations='Personally inspected all15 original screenshots: first viewport, new and legacy source cards, three new and six corrected legacy notes, three new declaration catalogues. Feasible-only finite-part convexity, true EReal minima and both negative ordered residuals match Lean. MinimizER point p=0 is separated from objective minimum values11/64 and1/2; the outside-center statement explicitly refers to−1. Global supports, positive eta for the comparison versus arbitrary eta for order equivalence, both psi derivatives and inherited completeness are visible. Source/causal/attainment/interiority/fixed-variable boundaries remain open. Exact Lean folded in notes; actual built-in catalogue wrapping fits types. No visible clipping in these captures.',
    limits='Actual file URI1440px desktop only; not HTTP/deployment/live/mobile/all-viewports. No new HTTP preview service retried after prior rejection. Distinct FINAL must personally inspect the same originals.',
    chapter_complete=False, whole_Goal_status='ACTIVE'))
retrieval = ROOT / 'research-wiki/retrieval-index' / (TASK + '.md')
own = [ROOT / d / (TASK + '.md') for d in ['tasks', 'proof-obligations']]
write(RUN / 'pre-FINAL-own-metadata-v1.json', dict(rows=[dict(path=p.as_posix(), sha256=sha(p),
    raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [CONTRIBUTION, retrieval, *own]]))
c = load(CONTRIBUTION)
c['verification']['bandit_check'] = 'Actual combined root9110/Tests9280 cached-inclusive jobs and full tools/bandit.py check exit0;472tests/7existing skips/exporter compiled/checkpassed. First current full attempt0; exact new source tracked beforehand. No code/test/rule/pin weakening.'
c['graph_contribution']['visual_review'] = 'Actual selected6nodes (3production,2public canaries,1generated Test auxiliary),1241coalesced direct TYPE_VALUE presences/12required VALUE pairs and two truly selected Eq.mp numeric tails inspected. Complete shared registry11002unchanged records+3source-qualified production nodes. Actual local-file desktop DOM/strict geometry/15originals inspected by root; distinct FINAL pending.'
c['verification']['site_build'] = 'Actual clean isolated SITEv1 build exit0 at2b929d03d7ace7c418986e429d0ccf317a2721c6 after applicable full combined Lean gate. No generated _site editing, later-head fresh build, deployment or live claim.'
c['verification']['site_check'] = 'Actual SITEv1 check/registry exit0;11002complete prior records+3canonical production nodes, no Test/generated-Test/per-Book duplicates. Actual local-file browser12source-guide MathJax containers/zeroerrors, strict desktop geometry/folded Lean/builtin catalogue wrap and15root-inspected originals;4exact generated input bytes unchanged. Distinct FINAL is a separate recorded review.'
c['verification']['independent_review'] += ' Two nonempty contributor bases/site/registry and actual local-file DOM/original pixels passed; distinct bounded FINAL/native/delivery remain pending. No full source/chapter acceptance.'
CONTRIBUTION.write_bytes((json.dumps(c, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
suffix = ('\nIntegrated candidate: clean isolated source2b929d03d7ace7c418986e429d0ccf317a2721c6 site/check/registry and two nonempty contributor bases passed. '
    'All11002 complete old registry records preserved+3shared production theorems. Local-file DOM12formula containers/zeroerrors/strict geometry/15originals personally inspected by root;4generated files unchanged. '
    'R9/L1 versioned reader fixes clarify minimizer p=0 versus values11/64,1/2 and outside center−1. '
    'General source/all8Chapter2forwards REQUIRED/OPEN; distinct FINAL/native/delivery pending, whole16Goal ACTIVE.\n')
for p in [retrieval, *own]:
    p.write_bytes(p.read_bytes() + suffix.encode('utf8'))
write(RUN / 'memory-digest-v3.md', '# ' + TASK + '\n\n'
    'Three frozen extended-loss bridge proofs, no new definitions; two full public infinity canaries and one generated Test auxiliary inventoried separately. '
    'Proper/global supports produce feasible finite-part convexity; actual EReal objective minimum transports through shared order API then actual real proximal comparison retains both negative residuals. '
    'Five full public VALUEs/ten standard axioms/five frozen headers and safe native guards. Selected6nodes/1241coalesced direct presences/12VALUEpairs; both truly selected numeric tails Eq.mp with actual extended helper. '
    'Two focused proof failures and two selector inspection failures retained; no type weakening. Body4 and selector-v2/data-v3 are final. Four local style warnings and existing dependency warnings retained. '
    'Distinct CONTRACT/BODY/canary accepted; reader-v1/v2 rejected, v3 accepted with explicit eight legacy wording fields and correct minimum/minimizer/center descriptions. '
    'Root9110/Tests9280/full harness472tests7existing skips/exporter/checkpassed first current attempt0, tracked source beforehand. Own shadowmismatches[]/would_mutatefalse/globalSGB unchanged. '
    'Two contributor bases and clean isolated site source2b929d03d7ace7c418986e429d0ccf317a2721c6,11002old registry records+3canonical production nodes. Actual local-file desktop12formula containers/zeroerrors/15root-inspected originals;4generated input files unchanged. '
    'Current-package full whitespace0, no exceptions; parent historical RAW reports untouched. Native commands/compiler/semantic/site gates separately evidenced, not one runtime enforcement claim. '
    'Full source X/interior/ambient extension locality/attained current-loss causal recursion/interiority/sharp same-run fixed-variable telescopes and all8forwards OPEN, chapter proof denominatornull/Chapter2partial, whole16Goal ACTIVE; FINAL/native/postnative/delivery pending.\n')
event('integrated-candidate-native-v1', 'candidate', dict(
    scope='Only3extended-loss bridge proofs and2public canaries; full source OPEN',
    full_harness_sha256=sha(RUN / 'full-harness-inspected-v1.json'), site_check_sha256=sha(RUN / 'site-check-v1.json'),
    registry_sha256=sha(RUN / 'registry-inspected-v1.json'), browser_sha256=sha(RUN / 'formula-render-v1-browser.json'),
    root_pixels_sha256=sha(RUN / 'root-reader-pixel-review-v1.json'), FINAL_pending=True,
    chapter_complete=False, goal_complete=False))
indices = {sha(p): dict(path=p.as_posix(), encoding='raw-file') for d in [RUN, CONTRACT]
    for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
def walk(obj, p, trail=''):
    if isinstance(obj, dict):
        for k, v in obj.items():
            if k in ['raw_base64', 'historical_raw_base64'] and isinstance(v, str):
                raw = base64.b64decode(v)
                indices[hashlib.sha256(raw).hexdigest()] = dict(path=p.as_posix(), encoding='embedded-exact-raw-base64', field=trail+'/'+k)
            else:
                walk(v, p, trail+'/'+k)
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            walk(v, p, trail+'/'+str(i))
for d in [RUN, CONTRACT]:
    for p in d.rglob('*.json'):
        walk(load(p), p)
resolutions = []
for name in ['contract-review-v1.json', 'BODY-canary-contract-review-v1.json',
        'canary-BODY-publication-review-v1.json', 'canary-BODY-publication-review-v2.json', 'canary-BODY-publication-review-v3.json']:
    changes = []
    for row in load(RUN / name)['raw_input_checks']:
        p = Path(row['path'])
        old = row.get('before_sha256') or row.get('expected_sha256') or row['sha256']
        if sha(p) != old:
            assert old in indices, (name, p, old)
            changes.append(dict(path=p.as_posix(), historical_sha256=old, current_sha256=sha(p), exact_historical_snapshot=indices[old]))
    resolutions.append(dict(review=name, review_sha256=sha(RUN / name), changed_live_rows=changes, all_other_current_inputs_unchanged=True))
write(RUN / 'FINAL-historical-binding-resolution-v1.json', dict(reviews=resolutions,
    scope='Actual approved staged five-file and OWN metadata transitions; no false current-live unchanged RAW claim for historical reviews.'))
stage = load(RUN / 'candidate-stage-plan-v1.json')['stage']
capture('FINAL-stage-v1', 'git', 'add', *stage)
capture('FINAL-full-package-diff-v1', 'git', 'diff', '--cached', BASE, '--check')
write(RUN / 'FINAL-diff-audit-v1.json', dict(actual_full_exit=0, current_package_RAW_exceptions=[],
    no_production_Test_reader_contract_exemptions=True, distinct_FINAL_adjudication_pending=True))
capture('FINAL-parent-PR209-v1', 'gh', 'pr', 'view', '209', '--json', 'number,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt,url')
write(RUN / 'FINAL-packet-v1.md', '''# Bounded extended-loss bridge FINAL

Audit three frozen production bridge proofs, no new definitions, two complete public infinity canaries and one compiler-generated Test auxiliary inventoried separately. Properness and every-feasible-point GLOBAL supports imply feasible finite values and ConvexOn V of toReal; global toReal convexity is explicitly refuted by both canaries. No naive instantiation of globally-real Theorem2.21. Actual penalized EReal minimum uses shared finite-part order API; explicit hp/finiteness and inherited CompleteSpace remain. Eta arbitrary for order equivalence (including0/negative), positive for the one-step. The latter retains BOTH psi ambient derivatives, actual supplied EReal minimum, convex V, proper global supports, all feasible comparators and BOTH negative ordered residuals. Center may be outside V/loss domain. No loss derivative/psi convexity/closedness/boundedness/attainment theorem. First bridge has no CompleteSpace/FiniteDimensional. Three derived helpers are not three printed results or a source erratum.

Not full Algorithm15.8/Theorem15.30, a causal trajectory or cumulative regret. Source X/interior/ambient-extension locality, actual attained current-loss recursion/interior invariants and same-run sharp fixed/variable telescopes including main-text fixed-step exercise REQUIRED/OPEN. All8Chapter2forwards open, chapter partial/proof denominatornull, whole16Goal ACTIVE; no Chapter6/15 acceptance.

Run publication_guard_v1.fixed and independently rehash all current FINAL RAW before/after. Prior staged reviews immutable, approved five-file/OWN metadata deltas resolved with exact before snapshots, including pre-stabilization raw metadata. Verify all3production+2canary normalized statement hashes/full contexts, separate raw header SHA conventions, actual five public VALUEs/ten standard-only axiom outputs/five guards. Selected compiled graph6nodes=3production+2canaries+1generatedTestaux,1241coalesced direct TYPE_VALUE presences/12actual VALUE pairs, not occurrences/full transitive/source/registry denominator. BOTH numeric tails genuinely selected with id-wrapper peeling/local let substitution/rightmost And.intro, Eq.mp heads retain actual extended helper, no theorem unfolding or proof-irrelevance normalization. Earlier id/And.casesOn outputs do not establish selected-tail use; those failures and proof repairs retained. Final body4/minimum and support producers actual, no assumed desired canary conclusion.

Minimizer point p=0 differs from objective minimum values11/64 and1/2 at centers1/2 and−1 (unit step). The latter CENTER−1 is outside V and loss domain. Nonquadratic divergences9/64 and11/64, abs nondifferentiability, actual extended minima/global supports/top-outside/feasible convexity AND not-global convexity are complete canary conclusions. v1/v2 reader rejections and version3 exact repair retained. Same five old paths only; current highlights add3notes and explicitly correct6oldnotes; readings adds1card and explicitly corrects2fields of the legacy Bregman card. All other old fields/IDs/formulas/links/Books/old proofs/contracts/receipts and unrelated T0 text unchanged. Older immutable prose may use compressed minimum0; this package explicitly corrects the current public wording without rewriting history.

Actual root9110/Tests9280/full harness472tests/7existing skips/exporter compile/checkpassed, first current full attempt0, tracked source beforehand. Four local style warning messages and existing parent warnings unsuppressed. Own shadow mismatches[]/would_mutatefalse/globalSGB untouched. Two nonempty contributor bases. Clean isolated site at source2b929d03d7ace7c418986e429d0ccf317a2721c6 sourceDirtyfalse;11002complete old registry records preserved+3canonical production theorems=11005, no Test/generated-Test/per-Book duplicates. Nine source cards; no later-head fresh-site claim.

Personally inspect ALL15 original images from formula-render-v1-browser.json using view_image original: viewport/new+legacy source cards/3new+6corrected old notes/3new catalogue declarations. Root pixel review does not discharge yours. Actual local-file1440desktop/12source-guide MathJax containers/zeroerrors/strict geometry/folded Lean/builtin catalogue wrap;4exact generated inputs unchanged. No HTTP service rejection retried/alternate launcher; file capture is not HTTP/live/mobile/all-viewports. No generated website/_site edits.

Current-package full diff actual0 without exceptions. Parent immutable RAW trailing spaces are unchanged history, not current exclusions. Preserve raw/Git CRLF differences by exact snapshots. Compiler/native-command/semantic/site gates are separate; no single-runtime enforcement claim. Requested Astra/medium, reused staged automated roles; no independent human/external/absolute-blind/runtime attestation.

Create-only FINAL-review-v1.md/json with report/input SHAs, independent RAW before/after checks, personal15pixel hashes and separate semantic/proof/reader/registry/visual/scope/package verdicts/requiredrepairs. Native bounded accepted counter3->0 means these3bridge proofs only, not source theorem/chapter/wholeGoal closure. Exact allowed subsequent existing OWN metadata edits should be listed: contribution semantic_roundtrip.remaining_semantic_delta, verification.independent_review and graph_contribution.visual_review ONLY; own task/proof-obligations/retrieval-index closure records; OWN lifecycle/trials/journal files. New memory/postnative/delivery evidence files may be created. Production/Test/root/reader/source/contract inputs immutable after FINAL. No additional contribution verification.site_build edit is planned. Subsequent ordinary scoped commit/push/draftPR depends on OPENdraftunmerged PR209 exact65e21be78abfbd4255798e54265ce418651ef70f; postnative and actualdelivery need distinct reviews. No merge/deploy/retirement/main/live/CI claim.
''')
paths = {p for d in [RUN, CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([PUBLIC, CANARY, CONTRIBUTION, retrieval, PDF, ROOT / 'BanditRLProof.lean', ROOT / 'Tests.lean',
    *[ROOT / d / (TASK + '.md') for d in ['tasks', 'proof-obligations', 'conversion-windows']],
    *[ROOT / n for n in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'website/scripts/build_site.py', 'website/scripts/check_site.py', 'tools/check_contributor_contract.py']],
    *[ROOT / 'website/content' / n for n in ['chapters.json', 'readings.json', 'highlights.json']],
    *[Path(r['path']) for r in load(RUN / 'browser-generated-inputs-before-v1.json')['rows']]])
fixed()
write(RUN / 'FINAL-inputs-v1.json', dict(rows=rows(paths), source_commit=reg['source_commit'],
    phase='Distinct bounded FINAL; native/delivery pending', production_proofs=3, new_definitions=0,
    public_canaries=2, generated_Test_auxiliaries=1, new_registry_nodes=3,
    chapter_proof_total=None, chapter_complete=False, whole_Goal_status='ACTIVE'))
print('Bounded exact FINAL packet ready; distinct review pending.')
