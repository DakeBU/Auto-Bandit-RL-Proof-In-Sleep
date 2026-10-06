from common_v2 import *
fixed(True);assert load(RUN/'body-binding-audit-v1.json')['status']=='passed-at-review-boundary'
p=Path('MANIFEST.md');raw=p.read_bytes();assert b'ONLINE-AFFINE-SUBGRADIENT-MIGRATION-20261007' not in raw
write(RUN/'manifest-before-affine-entry-v1.txt',raw)
p.write_bytes(raw+b'\n\n## ONLINE-AFFINE-SUBGRADIENT-MIGRATION-20261007\n\nOrabona v10 Theorem2.28 printed18/PDF30: one retained public full-image inclusion, seven unchanged scalar canary proofs/two TEST definitions; zero new mathematical/registry nodes. Current CONTRACT/BODY accepted and focused proof/kernel/fence evidence bound in runs/online-affine-subgradient-migration-20261007; combined project/site/FINAL/native acceptance and actual PR pending at this historical entry. Same shared Lean project/Book registry. Chapter2 and Chapters1-16 Goal incomplete; legacy1->0 after realPR is not chapter completion.\n')
write(RUN/'manifest-entry-v1.json',dict(candidate_historical_entry=True,original_prefix_preserved=True,original_raw_sha256=hashlib.sha256(raw).hexdigest(),after_sha256=sha(p),chapter_complete=False,goal_complete=False))
print('Additive candidate-historical MANIFEST entry, original full prefix preserved.')
