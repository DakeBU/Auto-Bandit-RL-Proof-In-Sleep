from common_nonsmooth_roots_v1 import *

fixed()
paths=[RUN/'nonsmooth-canary-publication-review-v1.md',RUN/'nonsmooth-canary-publication-review-v1.json',
    RUN/'nonsmooth-reader-proposal-v1.json',RUN/'nonsmooth-reader-proposal-v2.json',
    CONTRACT/'nonsmooth-future-publication-scope-v1.json',CONTRACT/'nonsmooth-future-publication-scope-v2.json',
    RUN/'nonsmooth-reader-intuition-repair-delta-v2.json',CONTRACT/'nonsmooth-materialized-future-bytes-v1.json',
    CONTRACT/'nonsmooth-exact-import-plan-v1.json',RUN/'nonsmooth-root-integration-v1.json',
    PUBLIC,CANARY,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean']
paths += [Path(r['after_snapshot']) for r in load(CONTRACT/'nonsmooth-materialized-future-bytes-v1.json')['rows']]
paths += [ROOT/'website/content'/p for p in ['chapters.json','readings.json','highlights.json']]
paths += [Path(p['snapshot']) for p in load(CONTRACT/'nonsmooth-exact-import-plan-v1.json')['rows']]
write(RUN/'nonsmooth-reader-repair-review-input-v2.json',dict(files=rows(paths),
    scope='Narrow repair of R-ABS-INTUITION only; independent judgment of exact reader v2 and materialized publication bytes. Three production and five canary BODY acceptances reused at unchanged complete hashes.',
    original_reader_verdict='rejected; retained exact v1 report/inputs',
    exact_AST_delta='Only notes[0].intuition; scope v2 only rebinds repaired reader proposal SHA.',
    actual_root_delta='Already applied exactly the two separately approved RAW-prefix appends. Current old-v1 reviewer root inputs intentionally differ only by that approved stage; no assertion that all old54inputs remain current-RAW-equal.',
    requested_review='Verify only the intended reader correction, all other proposal fields unchanged, actual future AST additions and exact root prefixes, then approve or reject v2 future-publication scope and materialized byte hashes. No new math/chapter/full gate/CI/main/merge/delivery acceptance.',
    original_review_receipt_sha256=sha(RUN/'nonsmooth-canary-publication-review-v1.json'),
    chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Narrow reader repair plus exact publication-byte review input ready; canonical readers remain unchanged.')
