from common_accepted_v5 import *

accepted_fixed()
assert load(RUN/'native-acceptance-overlay-v1.json')['status'].startswith('actual native commands passed')
old={r['path']:r['sha256'] for r in load(RUN/'FINAL-review-inputs-v1.json')['rows']}
rows={}
def add(p):
    p=Path(p).resolve();assert p.is_file()
    rows[p.as_posix()]=dict(path=p.as_posix(),sha256=sha(p))
for folder in [RUN,CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts and p.as_posix() not in old:add(p)
for r in load(RUN/'accepted-metadata-bindings-v1.json')['rows']:add(r['path']);add(r['original_snapshot'])
for p in [PUBLIC,CANARY,ROOT/'Tests.lean',ROOT/'BanditRLProof.lean',ROOT/'lean-toolchain',ROOT/'lakefile.lean',ROOT/'lake-manifest.json',ROOT/'runs/active_frontier.json']+READERS:add(p)
write(RUN/'post-native-review-inputs-v1.json',dict(phase='Actual executed own native suffix and acceptance guard audit',
    rows=sorted(rows.values(),key=lambda r:r['path']),fixed_input_count=len(rows),
    approved_FINAL_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),
    derived_obligations_before=4,derived_obligations_after=0,original16_and_null_total_preserved=True,
    chapter_complete=False,goal_complete=False,PR_delivery_completed=False))
write(RUN/'post-native-review-packet-v1.md',
    'Independently hash this current index before/after and resolve original FINAL current exact input count only through exact approved metadata snapshots/bindings. Audit actual accepted reviewer trial, accepted lifecycle, own frontier/shadow, verified_lemma memory record and retrieval record, exact6manifestfields and four identical owned task suffixes. Inspect actual all parsed journal rows/task ownership, not merely startswith. All public/canary/root/readers/pins/originalreceipts/pixels/globalSGB immutable. Source ledger retains original16/null and required general kernel/other information constructions/remainingchapters/appendices; only4derivedcompletionproof obligations4->0.\n\n'
    'Review new actual acceptance helpers/guard, exact selected PR title/body v1 and permitted scoped commit/push/draft/app attachment. No delivery or merge/deployment has happened. Return post-native-review-v1.md / post-native-receipt-v1.json with all RAW before/after, actual count/reportSHA, verdict, required_blocking_repairs, parsed metadata/guard findings and exact delivery boundary. No input edits/native/publication actions. Reused automated actor disclosed, Astra/medium requested only; whole Goal ACTIVE.\n')
print('Post-native current fixed RAW inputs:',len(rows),flush=True)
