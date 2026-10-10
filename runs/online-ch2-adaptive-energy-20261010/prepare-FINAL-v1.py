from common import *

assert Path.cwd() == ROOT
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], encoding='utf8').strip() == '3e5669e4b4e73a01d5c301e37aaa2eef07bd289b'
integration = load(CONTRACT/'exact-integration-plan-v2.json')['rows']
changed = {x['path']: x for x in integration}
for row in load(RUN/'baseline-v1.json')['rows']:
    expected = changed[row['path']]['after_sha256'] if row['path'] in changed else row['sha256']
    assert sha(row['path']) == expected, row['path']
write(RUN/'pre-FINAL-baseline-inspected-v1.json', dict(
    baseline_rows=35392, approved_old_changes=6, other_old_RAW_unchanged=35386,
    integration_plan_sha256=sha(CONTRACT/'exact-integration-plan-v2.json'),
    candidate_head='3e5669e4b4e73a01d5c301e37aaa2eef07bd289b',
    scope='Actual comparison with the pre-package RAW baseline and six exact reviewed AFTER hashes.'))

documents = ['tasks/'+TASK+'.md', 'conversion-windows/'+TASK+'.md',
    'proof-obligations/'+TASK+'.md', 'research-wiki/retrieval-index/'+TASK+'.md']
manifest = 'research-wiki/contribution-contracts/'+TASK+'.json'
mutable = [manifest]+documents+[(RUN/x).relative_to(ROOT).as_posix()
    for x in ['trials.jsonl', 'lifecycle-sessions.jsonl', 'lifecycle-state.json']]
originals = RUN/'native-acceptance-originals-v1.json'
write(originals, dict(rows=[dict(path=(ROOT/x).as_posix(), sha256=sha(ROOT/x),
    RAW_base64=base64.b64encode((ROOT/x).read_bytes()).decode('ascii')) for x in mutable]))
boundary = load(ROOT/manifest)['truth_boundary']
suffix = ('\n## Bounded energy prerequisite accepted locally\n\n'
    'Three exact frozen production proposition obligations are closed (3 -> 0); '
    'this is ONE source energy-display family, not three source results or a chapter denominator. '
    'Two separately validated FULL canaries retain all 8 and 3 conjuncts. '
    'Distinct FINAL review: `{FINAL_SHA}`. Actual combined root/Tests/full harness, public axioms, '
    'compiled VALUE branches, frozen fences, shared registry and six original reader images are recorded in '
    '`runs/online-ch2-adaptive-energy-20261010/`. Clean local site source: `{SITE_HEAD}`. '
    'Native candidate/acceptance events transport prior actual evidence retrospectively; '
    'they do not imply one runtime enforces the whole scientific workflow. '
    'Distinct post-native and actual delivery reviews remain pending.\n\n'+boundary+'\n')
replacements = {
    'semantic_roundtrip/remaining_semantic_delta':
        load(ROOT/manifest)['semantic_roundtrip']['remaining_semantic_delta'].replace(
            'integration/combined/site/FINAL/native/delivery pending.',
            'exact integration, combined gates, local site and FINAL accepted; '
            'FINAL {FINAL_SHA}; scoped native append follows this frozen plan; post-native/delivery pending.'),
    'graph_contribution/visual_review':
        'Actual local clean site {SITE_HEAD}; six ORIGINAL images personally viewed by root and distinct FINAL reviewer. '
        'Complete11055oldregistryobjects retained plus3canonical production proof nodes=11058;16cards/19MathJax. '
        'All3complete statement panels and source/teaching formulas visible without clipping. FINAL {FINAL_SHA}. '
        'No live/deployment or chapter closure claim.',
    'verification/bandit_check':
        'Actual combined root0 (9117 cached inclusive jobs), Tests0 (9294 jobs), full tools/bandit.py check0 '
        '(472tests/7skips; actual ProofGraphExport/check passed); source/pins bound by full-harness-inspected-v1.json. '
        'Nonempty contributor stack/main and OWN candidate shadow0. FINAL {FINAL_SHA}.',
    'verification/site_build':
        'Actual --lean-verified isolated local build0 from clean candidate {SITE_HEAD}, after applicable combined gate; '
        'site-build-v1.json and clean-candidate-site-binding-v1.json. Generated website/_site untouched. No deployment.',
    'verification/site_check':
        'Actual isolated check_site0; registry-command-v1/registry-inspected-v1 plus browser-command-v1 and six ORIGINAL '
        'pixel reviews;11055old+3production=11058,16sourcecards/19MathJax,0browser errors/clipping. FINAL {FINAL_SHA}.',
    'verification/independent_review':
        'Distinct reused staged automated CONTRACT, production BODY, FULL canary CONTRACT/BODY, exact integration, '
        'metadata format repair and FINAL reviews. FINAL {FINAL_SHA}; no external/human/absolute-blind attestation. '
        'Scoped native candidate/accepted transport3frozenpropositions->0; ONEsourcefamily. Post-native/delivery pending.'}
assert len(replacements) == 6
assert 'integration/combined/site/FINAL/native/delivery pending.' not in replacements['semantic_roundtrip/remaining_semantic_delta']
write(RUN/'native-acceptance-plan-v1.json', dict(
    originals=originals.as_posix(), originals_sha256=sha(originals), mutable_paths=mutable,
    document_paths=documents, document_suffix_template=suffix,
    manifest_replacements_template=replacements, boundary=boundary,
    declarations=load(ROOT/manifest)['declarations'],
    trial_notes_template='Distinct FINAL {FINAL_SHA}; exactly three frozen production proposition obligations3->0, '
        'ONE source display family; two FULL canaries independently checked. '+boundary,
    helpers=rows([RUN/'native_acceptance_guard_v1.py', RUN/'record-native-acceptance-v1.py']),
    global_frontier_mutation=False, chapter_complete=False, whole_Goal='active'))

packet = RUN/'FINAL-packet-v1.md'
write(packet, '# FINAL review: bounded adaptive energy prerequisite\n\n'
    'Review the current production, complete canaries, source, exact integration, actual compiler/axiom/VALUE/fence '
    'and combined gates, local registry and all six ORIGINAL image files. Personally view every original image '
    'at original detail. The source is the unnumbered display after Lemma4.13 and before Eq4.4, printed40/PDF52. '
    'Three proofs represent ONE display family; no algorithm, regret theorem, Chapter4 or Chapter2 closure.\n\n'
    'Inspect all indexed RAW inputs. Earlier manifest hashes describe historical bytes; explicit EOF, CRLF and '
    'native-doc-LF transition plans/receipts preserve originals. No mathematical header/BODY changed in those repairs. '
    'Candidate v1 whitespace and v2 index-RAW failures are retained; only v3 actually committed and built a clean site. '
    'Actual source candidate is 3e5669e4b4e73a01d5c301e37aaa2eef07bd289b; current untracked files are OWN evidence. '
    'Registry baseline is actual earlier clean site6c935087, not stacked base873039. '\
    'Production/canary failures and descriptive fence annotation repair remain recorded.\n\n'
    'Review the UNEXECUTED native-acceptance-plan-v1 and two helpers. Eight exact OWN paths may change: '
    'six manifest fields, append suffix to four documents, append one accepted3->0 production trial, '
    'append retrospective candidate and accepted events plus exact state transition. Two canaries remain separately '
    'validated, not part of the3production obligation denominator. Global SGB frontier and all other RAW inputs '
    'must remain unchanged. Post-native and actual delivery reviews are separate and still required.\n\n'
    'Write ONLY FINAL-review-v1.md/json. Include verdict, required_repairs, report/report_sha256, '
    'input_manifest/input_manifest_sha256, actual RAW checks, original image review, explicit source delta, '
    'approved_native_plan_sha256 and approved_native_helper_hashes (absolute path/sha256 rows). '
    'No native command, commit, push, merge or deployment in this review.\n\n'+boundary+'\n')
paths = [Path(x['path']) for x in load(RUN/'integration-inputs-v1.json')['rows']]
paths += list(RUN.rglob('*'))+list(CONTRACT.rglob('*'))
paths += [ROOT/x for x in mutable]+[PUBLIC, ROOT/'Tests/OnlineAdaptiveEnergyCanary.lean', PDF]
write(RUN/'FINAL-inputs-v1.json', dict(rows=rows(paths), scope='Current RAW inputs, including historical repair evidence; FINAL output excluded.'))
print('FINAL packet and native plan frozen; native execution remains pending distinct review.', flush=True)
