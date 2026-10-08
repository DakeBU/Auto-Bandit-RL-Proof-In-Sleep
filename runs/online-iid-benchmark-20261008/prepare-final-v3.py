from common_integrated_v2 import *
from commit_owned_v2 import current_owned_paths

fixed_integrated()
assert load(RUN / 'pixel-review-v9.json')['all_14_individually_viewed']
assert load(RUN / 'integrated-gates-v2.json')['affected_production_paths'] == 5
assert load(RUN / 'registry-v9.json')['new_registry_nodes'] == 10
for label in ['combined-root-v2', 'combined-Tests-v2', 'full-harness-v2', 'candidate-frontier-shadow-v2',
    'contributor-committed-exact-base-v2', 'site-build-v9', 'site-check-v9', 'registry-check-v9', 'current-reader-capture-v9']:
    assert load(RUN / (label+'-exit.json'))['exit_code'] == 0, label
paths = current_owned_paths()
assert all(p.startswith(RUN.relative_to(ROOT).as_posix()+'/') for p in paths)
for start in range(0, len(paths), 48):
    r = subprocess.run(['git', '-c', 'core.autocrlf=false', 'add', '--']+paths[start:start+48], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert r.returncode == 0
for p in paths:
    assert subprocess.check_output(['git', 'show', ':'+p]) == Path(p).read_bytes()
gate('scoped-diff-pre-FINAL-v10', sys.executable, '-B', '-X', 'utf8', RUN/'check-scoped-diff-v7.py', 'pre-FINAL-v10')

mutable = [MANIFEST, Path('MANIFEST.md'), Path('runs/trials.jsonl'), Path('runs/lifecycle_sessions.jsonl'), Path('runs/lifecycle_memory.jsonl')]
mutable += [Path(folder)/(TASK+'.md') for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index']]
snapshots = []
for p in mutable:
    snapshot = RUN/'snapshots'/('FINAL-review-v3-'+p.as_posix().replace('/', '--')+'.raw')
    write(snapshot, p.read_bytes())
    snapshots.append(dict(live_path=p.as_posix(), snapshot=snapshot.as_posix(), sha256=sha(snapshot),
        future_update='Only own acceptance/delivery evidence fields and exact own-task journal/document appends; no source, proof, type, root, reader or other-task changes.'))
assert len(snapshots) == 10
write(RUN/'FINAL-metadata-snapshots-v3.json', snapshots)
write(RUN/'prospective-pr-title-v3.txt', 'Produce the expected fixed minimum and causal IID square-loss excess')
write(RUN/'prospective-pr-body-v3.md', '''Chapter1 distinguishes the minimum of expected fixed cumulative loss from expected hindsight loss. This package produces the feasible population-mean minimizer and actual IsLeast, identifies the real infimum as T times variance, and derives nonnegative excess for the actual strict-past history policy and first-half meanPredict. Almost-sure unit support produces integrability; joint target independence produces current-target independence. The supplied-independent-prediction lemma is only an intermediate consumer.

Eight derived proofs and two definitions support this bounded deterministic finite-history core; they are not eight printed theorems or new rates. Policies need feasibility only on legal histories. Same-law fixed minimization needs no independence. T0 is an empty extension without uniqueness; averages require positive T. The constant population mean is a known-law oracle. Randomized/general-filtration coverage and the source asymptotic-success equivalence remain REQUIRED; no whole-source, chapter, or whole-book completion follows.

Validation: eight actual public bodies;28 named canaries, five whole fixtures and two probability instances;53 standard-axiom kernel checks, exact arbitrary-universe type/definition identities,36 native header guards and26 compiled VALUE pairs. Shared root9097jobs, Tests9253jobs, harness472tests/7skips and committed contributor five-production-path/one-contract gate pass. A genuine fair IID product gives T2 fixed expected minimum1/2 versus expected hindsight minimum1/4, actual meanPredict excess1/4 and a deliberately illegal future-aware trace with excess-1/2. Applicable clean local v9 site preserves10913old registry IDs/URLs/statement hashes and adds ten shared nodes; fourteen current images are reviewed. A rejected FINALv2 exposed reversed reader min/expectation wording and a missing t>0 qualifier; reader-only repair and fresh FINAL preserve that failure. Distinct staged automated decoder/source-reviewer CONTRACT/BODY/FINAL records and all failure evidence are in runs/online-iid-benchmark-20261008; no human, external, or model-runtime attestation is claimed. Full unexcluded whitespace check remains exit2 on twelve individually hashed evidence/protocol files; scoped check passes with no production, Tests, reader, contract or other-helper exemption. Two frozen protocol-helper EOF-only exceptions are explicitly reviewed.

Stacked on OPENdraft/unmerged PR193 exact bf9f896cdfebb2b836dacb01f3d4b209466c2100 (base codex/research-online-benchmarks). Original16Chapter1source items/proof-totalnull and five inherited main-relative module audits remain unwaived. Chapter1open, Chapter2incomplete, Chapters3–16unenumerated and necessary appendices required; total GoalACTIVE. No main/live, merge, deploy or retirement claim.
''')
write(RUN/'proposed-publication-v3.md', '''After actual distinct FINAL and separate native acceptance of only the eight frozen v2 terminals, commit scoped acceptance evidence, re-run the nonvacuous contributor check, and publish the exact prospective-pr-title/body-v2 as a reviewable DRAFT on codex/research-online-iid, stacked on OPENdraft/unmerged PR193/base codex/research-online-benchmarks exact bf9f896cdfebb2b836dacb01f3d4b209466c2100. Reverify base and current remote/REST exact head/state; attach every created PR officially. User approval authorizes scoped commit/push/draft PR, not merge/deploy/retirement/Goal completion. Only per-command credential helper; no token/global config changes.

Original CONTRACT186/BODY583 raw rows and five original task-metadata resolutions stay immutable. FINAL snapshots cover exactly ten future own-metadata paths; source/targets/bodies/root/readers are not waived. Twelve individual raw-evidence/protocol whitespace exceptions preserve actual failures; the two frozen protocol helpers have only EOF blank findings and need separate FINAL judgment. The af28b5d layout/evidence commit actually occurred after a failed whitespace check on two browser stdout files; this is disclosed, never a passing-check claim. Fresh full unexcluded v7 remains exit2; exact v7 scoped exclusion gate passes. All staging/log-race, proof/canary/type/kind and browser/layout failures are retained. The first page-label inference was incomplete; actual759.59px nowrap status badge was separately diagnosed and shortened, with no formula/source change. Original af28b5d v6 site passed geometry but FINALv2 rejected reader semantics; reader-only repair/new v9 is required; same unchanged Lean hashes are covered by actual combined gates. Five inherited main-relative source-module failures remain REQUIRED. Shared store/runtime/links and active checkout remain for the next mandatory totalGoal obligation.''')
requirements = load(CONTRACT/'reader-requirements-v2.json')
assert requirements == load(RUN/'stabilized-contract-v2.json')['original_reader_requirements']
packet = '''# Required anti-anchored FINAL: actual expected-fixed / causal IID core

Reuse distinct /root/source_reviewer, requested GPT-6 Astra/medium; disclosed previous staged automated-role history, no human/external/absolute-blind/runtime attestation. Search for mismatch. Rehash EVERY final-reader-inputs-v3.json row before/after. Preserve CONTRACT186/BODY583 inputs using only their original five exact task-metadata snapshot resolutions; also inspect BODY binding audit. All eight frozen v2 actual headers/bodies, two full public definitions,28actual canary proofs/five fixtures/two probability proofs, old source modules/pins and source PDF13–14/printed1–2 stay fixed. Explicit v1-to-v2 legal-input feasibility correction occurred before proving, not terminal weakening during proof repair.

Independently inspect current reader JSON, source card/eight notes/full catalogue types and ACTUALLY VIEW ALL14 current v9 images at original detail. ROOT pixel-review-v9 is evidence, not your review. Generated HTML/catalogue provides exact types/source links, not generated proof-term code. No generated site edit. Source v10 PDF SHA is fixed. Distinguish outside-expectation comparator, almost-sure support, actual IsLeast before csInf, same-law vs causal IID, supplied-L2/independence consumer vs actual producers, known-mean oracle and first1/2strict-past learner. Eight derived results are not eight source theorems/new rates. The broader randomized/filtration and asymptotic success source assertions remain REQUIRED.

Actual53kernelchecks standard axioms only:44theorem-kind including2probability proofs/9definitions;8neutral-to-draft+8draft-to-ACTUAL arbitrary-universe Prop identities,28closed canary Props/9whole definitions,36nativeheaderguards/26compiledVALUEpairs. Exact actual fair IID infinite real-coordinate product/non-pointwise support/legal-only unbounded-offcube lastPolicy, T2fixedminimum1/2 versus expectedhindsightminimum1/4, meanPredict excess1/4, knownmean0 and illegalfuturetrace-1/2. Root9097/Tests9253/fullharness472tests7skips, ownshadow and actual committed contributor5productionpaths1contract passed separately. Header guard exit0 is not compilation; no single runtime enforces all ABRL stages. Five inherited main-relative modules remain actually FAILED/unwaived, not a chapter gate pass.

Fresh FULL UNEXCLUDED whitespace check actually exit2. Exactly12 individually SHA-bound exception files in diff-raw-bound-exceptions-v7.json; preserve original seven. TWO are frozen reviewed protocol helpers common_v1.py/common_reviewed_v2.py, ONLY blank EOF findings: explicitly judge whether this preserved-byte exception is acceptable and whether any executable defect exists. Remaining are immutable decoder/raw verifier/browser/failed-check stdout. NO production/test/reader/contract/other-helper exception. Explicitly assess source layout/evidence commit af28b5d occurring after failed pre-status diff; no pass was claimed. Scoped v7/v8 actual exit0. Staging-before-writer-completion repair and all actual proof/type/canary/kind failures are retained. Initial sitev2overflow failed; page-label v4 alone still failed, prior diagnosis incomplete; actualnowrap759.59px badge repaired separately; Previous clean af28b5d v6 browser passed geometry but was semantically rejected; current v9 must pass both. ONLY new source-card page/status labels changed, all formula/model/source/oldcards unchanged. Applicable Lean inputs remained identical.

Current v9 site source_dirty=false,lean_verified=true from its exact clean reader-repair commit, independently checked; all10913oldshared IDs/URLs/hashes preserved+10publicnodes (8proofs2definitions), sourcecards11old+1new,8notes,4curatedlinks retained. All14 actual PNGs, DOM/math errors/wrapping checks separate from raw source. Candidate-stage 'gates pending' text is conservative, not fullchapter acceptance. Original16sourceitems/proof-totalnull, full C1/C2open,3–16unenumerated/necessaryappendices/old5audits/GoalACTIVE. Exact OPENdraft/unmerged PR193 basebf9f896... stack not main/live. Only this bounded deterministic IID subobligation may close; randomized/general-filtration and asymptotic equivalence remain required.

Review prospective PR title/body and proposed-publication-v3 CONDITIONALLY on actual FINAL/native acceptance. PR not yet created; do not report publication done. Exactly10 futuremutable metadata snapshots allow ONLY acceptance evidence fields/native own-task journal/appended own documents, no mathematical/readers waiver. No merge/deploy/retirement/Goalcomplete authorization. Final metadata may update only semantic_roundtrip.remaining_semantic_delta, graph_contribution.visual_review, verification.independent_review/bandit_check/site_build/site_check in manifest; other nine paths exact own append.

REPAIR REVIEW: rejected FINALv2 report4430558222eef89fc4d481643a4c2e2cfe8b816aad07cd0d6d3ffb562dd3e0e3/receiptf414064aa437d80a275e5d172748a1795c9589e1445faedd81d3d3cf6b0dd78c remain immutable. Actual F1 reversed min/expectation wording in eight Intuition fields; F2 lacked t>0 in note6 formula. ROOT original pixel review missed both. Reader-semantic-repair-v9 snapshots original highlights bytes and changes ONLY these nine fields; all statements/bodies/source/CONTRACT/BODY unchanged. New v9 site and ALL14 fresh pixels must be independently reviewed, with explicit repair_verdicts.F1/F2. Do not resolve rejection by formulas elsewhere. Old FINAL778 bindings for original reader JSON are historical and resolve through reader-before-semantic-repair-v6.json.raw; no other old input change allowed except documented future own metadata. Exact repair-diff review is required. Old native acceptance-v2/common_accepted_v2 helper was PREPARED but NOT EXECUTED after rejection; no native accepted trial exists yet.

Write ONLY final-reader-review-v3.md and final-reader-receipt-v3.json. actor.task=/root/source_reviewer; verdict accepted|accepted-with-explicit-delta|rejected; report path+SHA;fixed_input_count;reviewed_files ALL input rows+manifest+report. reader_requirement_verdicts.R1..R9 each EXACT original requirement with verdict satisfied OR blockingrepair. required_repairs/required_mathematical_repairs/required_metadata_repairs/required_blocking_reader_repairs arrays. Explicit12whitespace exception judgment/two helper EOF findings; input before/after hash evidence; actual ALL14 original views; source-package only; chapter_complete=false,goal_complete=false; native/PR pending. Return actual raw hashes. No other edits.

## Exact original reader requirements

'''
packet += '\n'.join(row['id']+': '+row['requirement'] for row in requirements)+'\n'
write(RUN/'final-reader-packet-v3.md', packet)
paths = [p.resolve().as_posix() for root in [CONTRACT, RUN] for p in sorted(root.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
paths += [p.resolve().as_posix() for p in [PUBLIC, CANARY, Path('BanditRLProof.lean'), Path('Tests.lean'),
    Path('website/content/readings.json'), Path('website/content/highlights.json'), Path('website/content/chapters.json'), PDF]+mutable]
paths += [Path(p).resolve().as_posix() for p in load(RUN/'draft-baseline-v1.json')['fixed_files']]
registry = load(RUN/'registry-v9.json'); site = Path('tmp/online-iid-benchmark-site-v9')
paths += [(site/p).resolve().as_posix() for p in ['site-manifest.json', 'books/registry.json', 'chapters/online-foundations/index.html', registry['module_path']]]
paths = list(dict.fromkeys(paths)); rows = [dict(path=p, sha256=sha(p)) for p in paths]
write(RUN/'final-reader-inputs-v3.json', dict(stage='FINAL', rows=rows, fixed_input_count=len(rows),
    original_CONTRACT_rows=186, original_BODY_rows=583, future_metadata_snapshots='FINAL-metadata-snapshots-v3.json',
    applicable_integrated='integrated-gates-v2.json', applicable_registry='registry-v9.json', applicable_pixels='pixel-review-v9.json',
    package_accepted=False, chapter_complete=False, goal_complete=False))
for row in rows:
    assert sha(row['path']) == row['sha256'], row['path']
fixed_integrated()
print('FINAL actual raw rows:', len(rows), '; distinct source/reader review pending.')
