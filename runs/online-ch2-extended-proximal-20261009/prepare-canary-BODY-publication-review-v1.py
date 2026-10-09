from common import *
import gzip
fixed()
c = load(RUN / 'complete-candidate-inspected-v1.json')
p = ROOT / 'Tests/OnlineBregmanExtendedCanary.lean'
assert sha(PUBLIC) == c['production_sha256'] and sha(p) == c['test_sha256']
assert c['both_selected_numeric_tails_retain_public_helper'] and c['selected_nodes'] == 6
assert c['coalesced_direct_TYPE_VALUE_presences'] == 1241
for row in load(RUN / 'BODY-canary-contract-review-inputs-v1.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
prior = ROOT / 'tmp/online-ch2-bregman-site-v1/books/registry.json'
receipt = ROOT / 'runs/online-ch2-bregman-20261009/registry-inspected-v1.json'
r = load(receipt)
assert sha(prior) == r['actual_current_registry_sha256']
old = load(prior)
assert len(old['nodes']) == 11002 and old['lean_verified']
assert old['source_commit'] == '69aeeeaf58364177a06bbc10329ea328c3c13b3c'
compressed = gzip.compress(prior.read_bytes(), mtime=0)
write(RUN / 'registry-baseline-v1.json.gz', compressed)
write(RUN / 'registry-baseline-binding-v1.json', dict(
    prior_source=prior.as_posix(), prior_complete_raw_sha256=sha(prior),
    compressed_snapshot_sha256=hashlib.sha256(compressed).hexdigest(),
    prior_actual_registry_receipt_sha256=sha(receipt), source_commit=old['source_commit'],
    total_shared_nodes=len(old['nodes']), identity=old['identity'],
    expected_new_canonical_ids=['declaration:' + t['declaration'] for t in load(CONTRACT / 'stabilized-v1.json')['targets']],
    expected_new_definitions=0, expected_new_theorems=3, Test_probes_and_generated_Test_auxiliaries_not_canonical_nodes=True,
    boundary='Prior accepted local PR209 source registry; no current combined or main/live acceptance.',
    chapter_complete=False, whole_Goal_status='ACTIVE'))
write(RUN / 'canary-BODY-publication-review-packet-v1.md', '''# Infinity canary BODY and exact publication plan review

Independently rehash all bound RAW inputs and all 2925 baseline paths before/after; common.fixed must pass. Original BODY/CONTRACT 112 current rows remain unchanged. Production SHA and all five exact public headers/context remain frozen. Review both complete Test bodies (12/11 conjuncts) and the actual compiler-generated Test auxiliary separately; no new explicit helper/definition. Properness, every-feasible-point global supports tested at every ambient y, actual top outside V, feasible convexity and genuine global finitePart nonconvexity at endpoints 0/2 midpoint 1 are proved. Actual minima transport through the public minimum iff, not supplied desired assumptions. Reused previous Test facts are the exact strictness/minimum/divergence/nondifferentiability components, with actual psi derivatives proved locally.

Two focused proof failures retained: IsMinOn presentation and uninstantiated real-inner rewrite. Third body compiled 3309 cached-inclusive jobs, but the original numeric selector stopped at an id wrapper around the entire conjunction. Explicit id peeling then revealed a top-level And.casesOn from obtaining an old conjunction, so that selector also did NOT isolate a numerical proof. Fourth body replaces the same old conjunction destructuring by exact component projections; no mathematics/header change, final Eq.mp unchanged. Fourth focused build actual0/Built new Test/3309 jobs. Fresh complete public VALUEs/four standard-only axiom outputs/two safe guards actual0. Four local tactic style warnings plus previous dependency warnings are retained, no suppression.

Read audit-numeric-tail-v2.lean and actual numeric-tail-data-v3.json: inline local lets, peel explicit id and metadata, then descend rightmost And.intro. No theorem unfolding or proof-irrelevance normalization. BOTH truly selected numeric branches now have Eq.mp heads and directly retain proximal_one_step_extended. Earlier outputs with id/And.casesOn heads are failure history and supply no selected-tail evidence. Selected compiled graph is SIX nodes: three production theorems, two public Test conjunctions and one referenced generated Test _simp_1_2 auxiliary; 1241 coalesced direct TYPE_VALUE constant presences and 12 required actual VALUE pairs. Not occurrence counts, full transitive graph, shared registry or source theorem denominator. Public Tests and auxiliary are NOT canonical Book nodes.

Separately assess exact-publication-plan-v1.json: only FIVE old paths prospectively mutate, raw root/Testroot prefix preserved plus one import each; only online-ogd appends one module/goal/completion suffix and one source-qualified card; highlights append exactly three production notes. No actual roots/readers have changed yet. Check R1–R8 from prior BODY review against exact proposed bytes, all source-vs-Lean seven slots and existing links/other Books preserved. Global support vs feasible support, finitePart only-on-V vs global conversion, arbitrary eta for min iff vs positive eta for comparison, inherited completeness, both psi derivatives, actual supplied EReal minimum, both negative ordered residuals and outside-center/domain example must remain clear. Three derived bridges are not three printed source results or an erratum. Shared complete prior registry 11002 records cached, expect exactly three added canonical production IDs, no per-Book proof tree.

Only authorize exact five-file materialization after separate BODY_verdict/materialization_verdict decision. No native acceptance, chapter/source/Goal completion, merge/deploy/main/live/CI claim. Source X/interior/ambient extension locality, actual attained current-loss causal recursion/interiority and sharp fixed/variable same-run telescopes including the main-text fixed-step exercise remain REQUIRED/OPEN; all eight Chapter2 forwards stay open. Combined root/Tests/full harness, shadow/fence/registry/site/DOM/pixels/FINAL/native/postnative/delivery are separate future gates. No HTTP service policy retry; later browser uses existing approved file URI route.

Create-only canary-BODY-publication-review-v1.md/json, one final LF and no trailing whitespace. Include verdict, BODY_verdict, materialization_verdict, required_repairs, exact allowed five-path fingerprints, production/Test SHA, input/report SHA, seven-slot deltas and read-only raw before/after checks. Verify every baseline path but receipt may store the count and SHA of the complete verified baseline rows rather than repeat 2925 baseline entries; retain explicit RAW checks for this input manifest. Requested GPT-6 Astra/medium, reused staged distinct automated role; no independent human/external/absolute-blind/runtime attestation. Do not modify existing inputs or run native acceptance.
''')
excluded = {'lifecycle-state.json', 'lifecycle-sessions.jsonl', 'own-artifact-journal.md', 'trials.jsonl'}
paths = [PUBLIC, p] + [x for x in RUN.iterdir() if x.is_file() and x.name not in excluded] + list(CONTRACT.glob('*'))
paths += [Path(row['path']) for row in load(RUN / 'contract-review-inputs-v1.json')['rows']]
write(RUN / 'canary-BODY-publication-review-inputs-v1.json', dict(rows=rows(paths),
    production_sha256=sha(PUBLIC), Test_sha256=sha(p), exact_plan_sha256=sha(CONTRACT / 'exact-publication-plan-v1.json'),
    baseline_count=2925, all_old_paths_currently_unchanged=True,
    allowed_new_outputs=['canary-BODY-publication-review-v1.md', 'canary-BODY-publication-review-v1.json'],
    package_accepted=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
print('Actual infinity canary BODY, selected numerical tails and exact five-path publication plan ready for distinct review.')
