from common_accepted_v1 import *
accepted_fixed()
previous=load(RUN/'pr-payload-v1.json');previous['body_file']=(RUN/'PR-body-v2.md').as_posix()
write(RUN/'pr-payload-v2.json',previous)
paths=[RUN/'publication-repair-review-v3.md',RUN/'publication-repair-receipt-v3.json',RUN/'PR-body-v1.md',RUN/'PR-body-v2.md',RUN/'pr-payload-v2.json',RUN/'committed-raw-audit-v2.json',RUN/'full-harness-final-v1-exit.json',RUN/'final-reader-receipt-v1.json',PUBLIC,CANARY]
receipt=load(paths[1]);assert receipt['verdict'] not in ['accepted','accepted-with-explicit-delta'] or receipt.get('required_repairs')
write(RUN/'publication-repair-review-inputs-v4.json',dict(scope='Separate bounded PR prose repair review: explicitly seed-expected regret, decoder only reconstructs and source reviewer accepts. All original v3 bindings/failure/FINAL preserved; public/canary/root/readers unchanged. No new theorem or proof progress.',previous_review_sha256=sha(paths[0]),previous_receipt_sha256=sha(paths[1]),rows=[dict(path=p.resolve().as_posix(),sha256=sha(p)) for p in paths],requested_model='GPT-6 Astra',requested_reasoning_effort='medium',runtime_attested=False,chapter_complete=False,goal_complete=False))
print('Frozen',len(paths),'bounded PR prose repair bindings')
