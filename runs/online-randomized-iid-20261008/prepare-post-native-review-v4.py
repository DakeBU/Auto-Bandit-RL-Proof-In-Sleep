from common_accepted_v3 import *

accepted_fixed()
paths = [Path(x['live_path']) for x in load(RUN/'FINAL-metadata-snapshots-v3.json')]
paths += [Path(x['snapshot']) for x in load(RUN/'FINAL-metadata-snapshots-v3.json')]
paths += [p for pattern in ['accepted-*v3*','*metadata*v4*','metadata-audit-v3-failed-replay*',
    'record-acceptance-v4.py','common_accepted_v3.py','native-acceptance-overlay-v3.json',
    'memory-digest-accepted-v3.md','proof-obligations-accepted-v3.json'] for p in RUN.glob(pattern) if p.is_file()]
paths += [CONTRACT/'chapter-one-source-ledger-accepted-v3.json', CONTRACT/'chapter-one-source-ledger-draft-v2.json',
    RUN/'final-reader-receipt-v3.json', RUN/'final-reader-review-v3.md']
write(RUN/'post-native-review-packet-v4.md', '''# Required actual suffix audit after bounded FINAL recommendation

Reuse distinct /root/source_reviewer, Astra/medium. This is only the future metadata audit required by actual FINAL. Rehash indexed actual before/after. Compare exact10 metadata current/snapshot bindings and actual-accepted-metadata-audit-v4.json: five own docs append exactly the one accepted digest; original MANIFEST is unchanged; two actual global JSONL appends belong only to this task/session; lifecycle_memory unchanged because actual memory-record --output writes the selected own RUN JSON. Manifest ONLY six permitted fields. All old 16 maintext objects and proof-totalnull remain immutable, new bounded ledger only.

Native trial/lifecycle/frontier/shadow/memory/retrieval commands actually executed with exit0. Only seven frozen terminals7->0; native scope is not C1/whole source/Goal. The distinct decoder reconstructs; CONTRACT/BODY/FINAL source reviews provide accepted-with-explicit-delta. No human/external/runtime attestation. Inspect the metadata-audit v3 assertion failure and v4 repair: original failed helper preserved and actual failed replay stdout retained, no native repeats or proof changes, no fake global-memory append. All original kernel/asymptotic/oldfive/fullC1/C2/3-16/appendix obligations still required. Proofs/readers/site remain immutable under prior FINAL bindings, no fresh math/site recertification claimed.

Write ONLY post-native-review-v4.md and post-native-receipt-v4.json. Actor/task and verdict accepted|accepted-with-explicit-delta|rejected; bind all indexed hashes/input index/report, fixed_input_count, inputs_unchanged/before_after_raw_hashes_match, required_repairs array, actual10 suffix/manifest judgments, actual-native-record judgments, remaining required scope. This cannot assert draft PR created. Exact prior FINAL-approved prospective title/body remain selected for authorized commit/push/draft PR; no merge/deploy/retirement or chapter/Goal completion. Return raw hashes.
''')
paths += [RUN/'post-native-review-packet-v4.md']
rows = [dict(path=p,sha256=sha(p)) for p in sorted({p.resolve().as_posix() for p in paths})]
write(RUN/'post-native-review-inputs-v4.json', dict(rows=rows,fixed_input_count=len(rows),
    phase='Actual bounded native metadata/suffix audit only',chapter_complete=False,goal_complete=False))
print('Actual suffix review inputs',len(rows))
