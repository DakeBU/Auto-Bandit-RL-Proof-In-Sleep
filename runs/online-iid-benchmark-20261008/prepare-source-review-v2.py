from common_v1 import *

fixed()
assert load(RUN / 'draft-type-verification-v2.json')['status'] == 'passed'
blind = load(RUN / 'blind-receipt-v2.json')
assert blind['actor']['task'] == '/root/osd_blind' and not blind['ambiguities']
assert sha(blind['report']['path']) == blind['report']['sha256_raw_bytes']
reviewed = {row['path']:row.get('sha256', row.get('sha256_raw_bytes')) for row in blind['reviewed_files']}
for row in load(RUN / 'neutral-inputs-v2.json')['rows']:
    assert sha(row['path']) == row['sha256'] == reviewed[row['path']]
metadata = []
for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index']:
    live = Path(folder) / (TASK + '.md')
    snapshot = RUN / 'snapshots' / ('CONTRACT-review-' + live.as_posix().replace('/', '--') + '.raw')
    write(snapshot, live.read_bytes())
    metadata.append(dict(live_path=live.resolve().as_posix(), snapshot=snapshot.resolve().as_posix(), sha256=sha(live),
        scope='Only exact existing own-task prefix; subsequent stage notes may append, never overwrite this reviewed text.'))
write(RUN / 'CONTRACT-metadata-snapshots-v2.json', metadata)
write(RUN / 'source-review-packet-v2.md', '''# Anti-anchored CONTRACT review, version2

Requested GPT-6 Astra/medium, distinct reused staged automated source reviewer; prior packet histories disclosed. No absolute blindness, human/external or runtime-model attestation. Formalizer cannot self-certify this stage. Search for mismatches and rejection grounds, not confirmation.

Pin source Orabona arXiv1912.13213v10/2026-06-21, PDF SHAcef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17 in ../research-online-ogd/tmp/pdfs/orabona-v10.pdf. READ and VIEW both complete printed1/PDF13 and printed2/PDF14, original new RUN cached PNG/TXT plus fresh pinned extraction. Caches are provenance-preserving copies, not fresh rerenders. Printed1 mean/variance optimum, cumulative1.1/nonnegative excess, average1.2; printed2 explicitly minimum of EXPECTED FIXED loss outside expectation. Prior pathwise square-minimum package is NOT this benchmark.

Active proposal CONTRACT/targets-v2.json (eight raw headers), public-context-v1.lean (two new complete definitions), source-card/fingerprint-v2, contract-v2.md, initial-DAG-v2, chapter-one-source-ledger-draft-v2. v1 is retained, never stabilized/accepted; formalizer removed unnecessary all-real-tuple policy-bound assumption ONLY I005/I008. v2 now bounds outputs on LEGAL unit-interval strict-history tuples; same conclusions/six other raw headers/complete definitions/PDF. Review this versioned change explicitly; it is stronger coverage, not proof-target weakening. Actual v1 decoder and separate v2 reconstruction/receipt preserved; compare v2 blind reconstruction to actual v2 Lean and source.

Semantic slots per complete definition and each I001–I008: objects/spaces; quantifiers/order; assumptions/regularity; conclusion/metric; constants/normalization/indexing; probability/information; boundary/source delta. In particular: a.s. support and derived integrability, probability normalization, same-law but no independence needed for FIXED minimum, real loss-image IsLeast must be produced, T0 empty/no uniqueness. I004 is only an independent-prediction consumer with two real pending producers. I005 derives current-target independence from ONLY strict-past measurable policy; its feasible inputs hold a.s. and cannot be supplied by all-future algorithm. I006 actual initial-half meanPredict, deriving L2 from a.s. support rather than invoking older pointwise-bound API. Distribution mean comparator/oracle is not computed by an unknown-law algorithm. Deterministic history scope is partial source coverage: randomized/abstract-filtration extension and source asymptotic-success equivalence remain REQUIRED separate audits. Neither may be excluded to claim full source/chapter completion.

Actual draft eight closed Props and four whole definitions are equal to neutral context at the same ARBITRARY universe u; actual APIs/type files compile. This is NOT public theorem-body compilation. Original v1 closed-Prop comparison failed because universe instances were left unconstrained; exact failure/repair and corrected arbitrary-u comparison retained, no restriction to Type0. Preparation v1 failed at missing own retrieval-index after four task appends; operational resume adds only that missing file before executing unchanged retrieval/compiler tail. Source aliases, headers, definitions and PDF never changed by those repairs.

Read exact current reused shared source modules: OnlineLearningStochastic (expected_square_decomposition/independent_prediction_square), History (history_policy_independent/normalized_excess), Information (meanPredict_independent), IID (measurable; old pointwise-bound APIs explicitly not sufficient to strengthen the current a.s. contract), FTL/Mean (actual first-half strict-past predictor/feasibility). Existing declaration scans/types are retrieval evidence, not whole-module acceptance; FIVE old main-relative source module audits remain unwaived. No new dependencies/toolchain/project or proof bodies yet. Actual source-only/focused type gate and contract version freeze precede proving I001.

Review original R1–R9 separately. At CONTRACT stage distinguish target-fidelity satisfaction from required future actual bodies/canaries/kernel/combined/root/Tests/harness/currentreader/site/FINAL/native/PR discharge. Recommend accepted-with-explicit-delta only if active targets preserve the source hinge honestly; identify typed mathematical/header/metadata blockers otherwise. Eight derived producer/representation/adapters are not eight printed source theorems. One source hinge is bounded, not chapter completion. Original16C1items/proof-totalnull, C1/C2 open,3–16unenumerated/necessaryappendicesrequired, totalGoalACTIVE, exact OPENdraft/unmergedPR193 stack; no main/live/merge/deploy/retirement claim.

Only write source-contract-review-v2.md and source-contract-receipt-v2.json in this RUN. Bind every exact row of source-review-inputs-v2.json with raw SHA before/after, manifest and report SHA, actual distinct actor, actual verdict/required_repairs/required_blocking_repairs, per-target seven-slot differences, reader requirements and future gates. Keep all inputs/previous receipts unchanged. No theorem bodies/source corrections permitted. Semantics approval cannot substitute for kernel compilation or publication.
''')
paths = []
for folder in [RUN, CONTRACT.resolve()]:
    paths += [p.resolve() for p in folder.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths += [Path(p).resolve() for p in load(RUN / 'draft-baseline-v1.json')['fixed_files']]
paths += [Path(row['live_path']) for row in metadata]
paths.append(PDF.resolve())
paths = sorted(set(paths), key=lambda p:p.as_posix())
write(RUN / 'source-review-inputs-v2.json', dict(fixed_input_count=len(paths), contract_version=2,
    rows=[dict(path=p.as_posix(), sha256=sha(p)) for p in paths], chapter_complete=False, goal_complete=False))
fixed()
print('CONTRACT v2 reviewer inputs frozen:', len(paths), '; no public proofs or source acceptance yet.')
