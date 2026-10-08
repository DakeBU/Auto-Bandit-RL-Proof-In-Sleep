from common_reader_FINAL_repair_v2 import *

fixed_integrated()
repair = load(CONTRACT/'publication-prose-repair-v2.json')
assert sha(RUN/'prospective-PR-body-v2.md') == repair['repaired_body_sha256']
assert (RUN/'prospective-PR-body-v2.md').read_bytes() == (
    repair['new_prefix'].encode() + (RUN/'prospective-PR-body-v1.md').read_bytes()[len(repair['old_prefix'].encode()):])
scope = load(RUN/'FINAL-future-metadata-scope-v1.json')
write(RUN/'FINAL-future-metadata-scope-v2.json', scope)
snapshots = []
for i, r in enumerate(load(RUN/'FINAL-metadata-snapshots-v1.json')):
    p = Path(r['live_path']); q = RUN/'snapshots'/('FINAL-metadata-'+str(i)+'-v2.raw')
    write(q, p.read_bytes())
    snapshots.append(dict(live_path=p.as_posix(), snapshot=q.as_posix(), sha256=sha(q)))
write(RUN/'FINAL-metadata-snapshots-v2.json', snapshots)

rows = {}
def add(p):
    p = Path(p).resolve(); assert p.is_file()
    rows[p.as_posix()] = dict(path=p.as_posix(), sha256=sha(p))
for r in load(RUN/'FINAL-review-inputs-v1.json')['rows']: add(r['path'])
for folder in [RUN, CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts: add(p)
write(RUN/'FINAL-review-inputs-v2.json', dict(
    phase='F1 repaired FINAL: explicit original AE unit feasibility in PR opening',
    rows=sorted(rows.values(), key=lambda r:r['path']), fixed_input_count=len(rows),
    original_CONTRACT_count=118, original_BODY_count=236, rejected_FINAL_count=444,
    original_FINAL_mutable_bindings=(RUN/'FINAL-v1-prose-repair-mutable-bindings-v2.json').as_posix(),
    original_R1_R6=load(CONTRACT/'reader-requirements-v1.json'), future_metadata_scope=scope,
    source_commit=load(RUN/'registry-v4.json')['source_commit'],
    selected_PR_title=(RUN/'prospective-PR-title-v2.txt').as_posix(),
    selected_PR_body=(RUN/'prospective-PR-body-v2.md').as_posix(),
    allowed_outputs=['final-reader-review-v2.md','final-reader-receipt-v2.json'],
    chapter_complete=False, goal_complete=False))
write(RUN/'FINAL-review-packet-v2.md',
    'Distinct staged source reviewer: independently hash all current fixed RAW rows before/after; preserve rejected FINAL444/report/receipt. Resolve only original trials/lifecycle through FINAL-v1-prose-repair-mutable-bindings-v2 exact snapshots and inspect each actual owned rejection/repair entry. No proof, canary, root, reader, pin, HTML, registry or original image changed.\n\n'
    'F1 repair is precisely a new prospective PR opening that explicitly requires original predictions to be [0,1]-valued almost everywhere at every natural time, in addition to relative AE measurability. Check the exact prefix delta against constant2 counterexample and frozen L1 hpb; title unchanged and rest of PR bytes unchanged. Select ONLY v2 title/body for future publication. All three exact mathematical targets retain contract v1.\n\n'
    'Retain anti-anchored scrutiny of complete three types/bodies, 14 canary proofs/one definition, original source and decoder/CONTRACT118/BODY236, all-time information/benchmark/T0/source boundaries. Review original R1-R6 verbatim with per-row verdict/evidence. Eight personally inspected original v4 pixels and actual v1-named browser/DOM outputs remain byte-identical; reuse your actual prior pixel inspections explicitly without claiming fresh capture. Current actual combined gates/42 axioms/39 selected graph nodes2136 coalesced edges12 VALUE pairs/10935 old+3 new shared Book nodes and exact mapping repair remain applicable. Preserve all failed attempts and raw limitations.\n\n'
    'Return accepted|accepted-with-explicit-delta|rejected, F1 disposition, seven slots, exact R1-R6, all RAW rows/hashes before/after, report SHA and exact permitted_future_metadata if favorable. Three derived obligations only may close AFTER favorable FINAL/native/post-native gates. Original16/null/remaining completion/kernel/whole-source/chapters/appendix obligations remain required; whole Goal active. Reused distinct automated actor disclosed, requested Astra/medium only, no absolute blindness/human/external/runtime attestation. Write ONLY final-reader-review-v2.md and final-reader-receipt-v2.json; no native or publication actions.\n')
print('Repaired FINAL current fixed RAW inputs:', len(rows), 'three obligations still pending.', flush=True)
