from common import *
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('--phase', required=True)
args = parser.parse_args()
assert args.phase.replace('-', '').isalnum()
review_path = RUN/'fresh-delivery-scripts-review-20261011-v3.json'
assert sha(review_path) == '0ca170a0052b34cb6ce984de9e05fb2f736f363ed6f0248a425235e55d085240'
review = load(review_path)
assert review['verdict'] == 'accepted-scoped-execution-subset'
assert review['blocking_repairs'] == []
manifest_path = RUN/'delivery-scripts-prepared-20261011-v3.json'
assert sha(manifest_path) == review['approved_scripts_manifest_raw_sha256']
manifest = load(manifest_path)
for row in review['approved_scripts']:
    assert sha(row['path']) == row['sha256'], row['path']
for row in manifest['config']:
    assert sha(row['path']) == row['sha256'], row['path']
assert sha(RUN/'common.py') == 'f426be53126c83b41c92c20b7238b3c993ae2d73c6279a492df50559dfbc0be0'
write(RUN/('reviewed-execution-hashes-'+args.phase+'.json'), dict(
    phase=args.phase, review=rows([review_path])[0], manifest=rows([manifest_path])[0],
    approved_scripts=review['approved_scripts'], configuration=manifest['config'],
    common=rows([RUN/'common.py'])[0], hashes_match=True,
    note='Timing is the explicit phase name; no retroactive pre-execution claim.'))
print('Exact approved scripts and configuration hashes match:', args.phase, flush=True)
