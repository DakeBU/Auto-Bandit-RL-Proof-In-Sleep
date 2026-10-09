from publication_guard_v2 import *
fixed()
for label in ['site-build-v2', 'site-check-v2', 'registry-command-v2',
        'reader-file-browser-capture-command-v2', 'contributor-stack-v2', 'contributor-main-v2']:
    assert load(RUN / (label + '.json'))['actual_exit'] == 0, label
reg = load(RUN / 'registry-inspected-v2.json')
browser = load(RUN / 'formula-render-v2-browser.json')
site_binding = load(RUN / 'clean-candidate-site-binding-v2.json')
assert reg['source_commit'] == site_binding['actual_head']
assert reg['total_nodes'] == 11015 and reg['retained_complete_old_nodes'] == 11005
assert len(browser['images']) == 22 and not browser['errors'] and not browser['failed']
assert browser['url'].startswith('file:///') and browser['actualSourceGuideMathContainers'] == 13
for row in load(RUN / 'browser-generated-inputs-before-v2.json')['rows']:
    assert sha(row['path']) == row['sha256']
# Run only after /root personally viewed every listed original using view_image original.
write(RUN / 'root-reader-pixel-review-v1.json', dict(actor='/root',
    images=rows(RUN / n for n in browser['images']), image_count=22, tool='view_image detail original',
    source_commit=reg['source_commit'],
    observations='Personally inspected all22 original screenshots: first viewport, new source card, ten new notes and ten production declaration catalogues. Source target/base orientation, current whole-loss before prediction, classical partial selection and mathematical nonattainment, local actual-state attainment premise, T0, actual two consecutive states, proper/global supports, both generator derivatives and both signed residuals are adjacent to exact formulas and natural proofs. Generic normed-space versus final complete inner-product context is explicit. Four concrete canary boundaries and full-source/sharp cumulative obligations remain visible. Exact Lean folded; actual builtin catalogue wrapping fits types. The repaired completion formula visibly includes every reached-state attainment premise and its terminal conclusion. Original SITEv1 silent gathered alignment loss is preserved and not accepted. No visible clipping in these captures.',
    limits='Actual file URI1440px desktop only; not HTTP/deployment/live/mobile/all-viewports. No new HTTP preview service retried after prior rejection. Distinct FINAL must personally inspect the same originals.',
    chapter_complete=False, whole_Goal_status='ACTIVE'))
retrieval = ROOT / 'research-wiki/retrieval-index' / (TASK + '.md')
own = [ROOT / d / (TASK + '.md') for d in ['tasks', 'proof-obligations']]
write(RUN / 'pre-FINAL-own-metadata-v1.json', dict(rows=[dict(path=p.as_posix(), sha256=sha(p),
    raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [CONTRIBUTION, retrieval, *own]]))
c = load(CONTRIBUTION)
c['graph_contribution']['visual_review'] = 'Actual selected14nodes(10production=8proofs/2defs,4publicTests),2027coalesced direct TYPE_VALUE presences/12canary VALUE pairs plus6production pairs and two truly selected Eq.mp numeric tails. Complete shared registry11005unchanged records+10canonical production nodes. Actual local-file desktop DOM/strict geometry/22originals inspected by root; distinct FINAL pending.'
c['verification']['site_build'] = 'Actual clean isolated repaired SITEv2 build exit0 at ' + reg['source_commit'] + ' after applicable full combined Lean gate. No generated _site editing, later-head fresh build, deployment or live claim.'
c['verification']['site_check'] = 'Actual repaired SITEv2 check/registry exit0;11005complete prior records+10canonical production nodes(8proofs/2defs), no Test/generated-Test/per-Book duplicates. Actual local-file browser13source-guide MathJax containers/zeroerrors, strict desktop geometry/folded Lean/builtin catalogue wrap and22root-inspected originals;4exact generated input bytes unchanged. Distinct FINAL separate.'
c['verification']['independent_review'] += ' Two nonempty contributor bases/site/registry and actual local-file DOM/original pixels passed; distinct bounded FINAL/native/delivery pending. No full source/chapter acceptance.'
CONTRIBUTION.write_bytes((json.dumps(c, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
suffix = ('\nIntegrated candidate: clean isolated source ' + reg['source_commit'] +
    ' site/check/registry and two nonempty contributor bases passed. All11005 complete old registry records preserved+10shared production nodes(8proofs/2defs). '
    'Local-file DOM13formula containers/zeroerrors/strict geometry/22originals personally inspected by root;4generated files unchanged. '
    'Full source/sharp same-run fixed-variable endpoints including main-text exercise and all8Chapter2forwards REQUIRED/OPEN; distinct FINAL/native/delivery pending, whole16Goal ACTIVE.\n')
for p in [retrieval, *own]:
    p.write_bytes(p.read_bytes() + suffix.encode('utf8'))
write(RUN / 'memory-digest-v3.md', '# ' + TASK + '\n\n' +
    (RUN / 'memory-digest-v2.md').read_text(encoding='utf8') + suffix +
    '\nOriginal SITEv1 automatic checks passed but root/source reviewer found missing attainment premise in original note7; native repair recorded. Exact one-new-note math bigl/bigr repair-v3 independently accepted, Lean/fullharness inputs unchanged. Clean repaired SITEv2/check/registry and actual stronger MathML/pixels now supplied. Original DOM/images/failed inspections retained.\nCurrent-package full whitespace0/no exceptions. Native/compiler/semantic/site gates separately evidenced; no single-runtime enforcement claim. No later evidence-head fresh site or merge/deploy/main/live/CI claim.\n')
event('integrated-candidate-native-v1', 'candidate', dict(
    scope='Only8derived proofs/2partial definitions/4public canaries; fullsource OPEN',
    full_harness_sha256=sha(RUN / 'full-harness-inspected-v1.json'), site_check_sha256=sha(RUN / 'site-check-v2.json'),
    registry_sha256=sha(RUN / 'registry-inspected-v2.json'), browser_sha256=sha(RUN / 'formula-render-v2-browser.json'),
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
for name in ['contract-review-v1.json', 'BODY-canary-contract-review-v1.json', 'canary-BODY-publication-review-v1.json', 'render-repair-review-v3.json']:
    changes = []
    for row in load(RUN / name)['raw_input_checks']:
        p = Path(row['path'])
        old = row.get('before_sha256') or row.get('expected_sha256') or row['sha256']
        if sha(p) != old:
            assert old in indices, (name, p, old)
            changes.append(dict(path=p.as_posix(), historical_sha256=old, current_sha256=sha(p), exact_historical_snapshot=indices[old]))
    resolutions.append(dict(review=name, review_sha256=sha(RUN / name), changed_live_rows=changes, all_other_current_inputs_unchanged=True))
write(RUN / 'FINAL-historical-binding-resolution-v1.json', dict(reviews=resolutions,
    scope='Actual approved staged five-file and OWN metadata transitions resolved with exact before bytes; historical RAW reviews do not assert current-live unchanged.'))
stage = load(RUN / 'candidate-stage-plan-v2.json')['stage']
capture('FINAL-stage-v1', 'git', 'add', *stage)
capture('FINAL-full-package-diff-v1', 'git', 'diff', '--cached', BASE, '--check')
write(RUN / 'FINAL-diff-audit-v1.json', dict(actual_full_exit=0, current_package_RAW_exceptions=[],
    no_production_Test_reader_contract_exemptions=True, distinct_FINAL_adjudication_pending=True))
capture('FINAL-parent-PR210-v1', 'gh', 'pr', 'view', '210', '--json', 'number,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt,url')
write(RUN / 'FINAL-packet-v1.md', '''# Bounded prescient partial Bregman FINAL

Review repaired SITEv2 after root caught lost completion premise in SITEv1: gathered optional alignment consumed the bracket. Failure DOM/pixels retained; exact one-new-note math bigl/bigr repair distinctly reviewed, proof/contract/fullLean inputs unchanged. Review eight exact frozen derived production proofs and two exact mathematical partial definitions, four full public canary conjunctions; no generated Test auxiliary in the selected graph. Source Definition6.4 has target X/base interiorX. Ambient-extension locality uses actual EqOn and interior neighborhoods; no boundary derivative validity, positivity or selected-trajectory invariance. Generic definitions/specs use arbitrary real normed spaces without completeness/finite dimension. The final actual-transition comparison inherits complete real inner-product context exactly; no standalone incompatible NormedSpace parameter. Generic eta may be0/negative, V empty, objectives improper/infinite; some means a feasible attained minimum, none is mathematical nonattainment, not timeout/nonuniqueness. Noncomputable classical choice is not an executable optimizer or measurable selection.

The whole current loss is received before the played prediction: source roundt+1=Lean losst/state(t+1). Prefix equality concerns whole loss functions and steps strictly belowt. There is no future/horizon/comparator input into the producer. Absorbing failure includesk0. Completion assumes local minimum attainment for every actually reached predecessor belowT; T0 can return infeasiblex0. No unconditional attainment/interiority. The signed comparison uses actual consecutive some states, derives the actual objective minimum from successor extraction, identifies the predecessor and reuses the accepted EReal producer. Keep convexV, positive currenteta, proper loss/global ambient supporting subgradients at every feasible point, BOTH actual psi derivatives, finite-value justification/all feasible comparators, BOTH ordered negative residuals. No assumed desired one-step inequality.

Four complete canaries: (1) restricted absolute then different affine-5z/8 on[-1,1], psi=z4/4+z2/2, actual states.5->0->.5 and movement11/64,9/64, universal two-round bound and numeric-.5<=-5/16; actual minima/uniqueness/conditional completion/successor extraction/prefix/newoneStep consumed. (2) restricted linear[0,1], quadraticpsi, initialcenter-1outsideV ANDlossdomain, actual unique chosen0, objective minimum.5, movement.5, universal/newcomparison and-.5<=.5. (3) V=Iic0,X=R,f=z,psiexp: proper/supports/sourceclosed thresholdsublevels/strictness/differentiability, objectiveexpz-1, everyp admits lowerp-1, actualnone and all positive iteratesnone. No complete generated source run/source erratum. (4) X=Ici0,psi=z2+z,phi=z2+absz: agreement/interiorbase1target2 equality1 throughnewlocality, boundarybase0TOTAL-fderivvalues4vs6 plusactualnondifferentiability. Boundary values diagnostic, not source-valid divergence.

Eight derived proofs/two definitions are not eight printed results, full Algorithm15.8/Theorem15.30 or source erratum. Source X/interior regularity transport into valid generated run, source interior conditions and sharp same-run fixed/variable cumulative bounds including fixed-step main-text exercise remain REQUIRED/OPEN. All8Chapter2forwards OPEN, Chapter2partial/proofdenominatornull, wholeChapters1-16GoalACTIVE; no Chapter6/15 acceptance.

Run publication_guard_v2.fixed and independently rehash all current FINAL RAW before/after. Historical approved five-file/OWN metadata transitions have exact before snapshots; do not claim historical-live rows always unchanged. Verify8production/4canary frozen normalized statement hashes,2whole definition hashes/full contexts and distinct raw-hash conventions. Actual12complete public proof VALUEs,26standard-only axiom outputs including2defs,12header/nativeguards. Selected14nodes=10canonicalproduction(8proofs/2defs)+4publicTests;2027coalesced direct TYPE_VALUE presences/12requiredcanaryVALUEpairs plus6separateproductionpairs, not occurrences/fulltransitive/source/registrydenominator. BOTH numeric tails separately selected with locallet substitution/metadata+idpeeling/rightmostAnd.intro; Eq.mpheads retain actualiterate_one_step. No unfolding/proof-irrelevance normalization. All failed proof/API/audit/discovery attempts retained. Finalproduction/Test no own warnings; parentwarnings replayed.

Read observed actual root/Tests/fullharness compiler/jobs/unittests/skips/exporter/check markers in inspected receipts; do not infer compiled from exit0 alone. New sources tracked beforegate. OWNshadowmismatches[]/would_mutatefalse/globalSGBunchanged. Two nonempty contributor bases. Exact approved five old paths only: append one rootimport and oneTestsimport; online-ogd module/goal/completionsuffix/card;10newnotes. Every old field/link/ID/formula/Books preserved. All11005 complete old registry records remain equal, plus10canonicalproduction=11015(8proofs/2defs), noTest/generatedTest/perBookduplicates. Ten sourcecards. Clean isolated repaired SITEv2 source commit in binding, sourceDirtyfalse; no later-evidence-head fresh-site claim.

Personally inspect ALL22 originals from formula-render-v2-browser.json with view_image original: viewport/sourcecard/10notes/10cataloguedeclarations. Root viewing does not discharge yours. Actual file URI1440desktop/13sourceguideMathJaxcontainers/zeroerrors/strictgeometry/foldedLean/builtincataloguewrap;4exactgeneratedinputs unchanged. No new HTTPservice retry/alternate launcher; notHTTP/live/mobile/all-viewports. No generatedwebsite/_site edit.

Current-package full diff0/noexceptions; preserve RAW/GitCRLF differences as exact snapshots. Compiler/native/semantic/site gates separately evidenced, no single-runtime enforcement claim. Distinct reused staged automated roles, related history disclosed; requestedAstra/medium, no human/external/absolute-blind/runtimeattestation.

Create-only FINAL-review-v1.md/json: report/inputSHAs, independentRAWbefore/afterchecks, personal22pixelhashes and separate semantic/proof/reader/registry/visual/scope/package verdicts/requiredrepairs. List exact allowed subsequent existing OWN metadata edits: contribution semantic_roundtrip.remaining_semantic_delta, verification.independent_review, graph_contribution.visual_review ONLY; own task/proof-obligations/retrieval-index closure suffixes; OWNlifecycle/trials/journal. Newmemory/postnative/delivery evidence may be created. Production/Test/root/reader/source/contract immutable afterFINAL. Boundednative8proofs->0 counts these8proofs only, neverfullsource/chapter/Goal. Postnative and actualdelivery distinct reviews. Scopedcommit/push/draftPR stacks on OPENdraftunmerged PR210 exact41f1fb26915b3bf7f84035393080991c38aeba64. No merge/deploy/retirement/main/live/CIclaim.
''')
paths = {p for d in [RUN, CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([PUBLIC, CANARY, CONTRIBUTION, retrieval, PDF, ROOT / 'BanditRLProof.lean', ROOT / 'Tests.lean',
    *[ROOT / d / (TASK + '.md') for d in ['tasks', 'proof-obligations', 'conversion-windows']],
    *[ROOT / n for n in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'website/scripts/build_site.py', 'website/scripts/check_site.py', 'tools/check_contributor_contract.py']],
    *[ROOT / 'website/content' / n for n in ['chapters.json', 'readings.json', 'highlights.json']],
    *[Path(r['path']) for r in load(RUN / 'browser-generated-inputs-before-v2.json')['rows']]])
fixed()
write(RUN / 'FINAL-inputs-v1.json', dict(rows=rows(paths), source_commit=reg['source_commit'],
    phase='Distinct bounded FINAL; native/delivery pending', production_proofs=8, new_definitions=2,
    public_canaries=4, generated_Test_auxiliaries=0, new_registry_nodes=10,
    chapter_proof_total=None, chapter_complete=False, whole_Goal_status='ACTIVE'))
print('Bounded exact FINAL packet ready; distinct review pending.')
