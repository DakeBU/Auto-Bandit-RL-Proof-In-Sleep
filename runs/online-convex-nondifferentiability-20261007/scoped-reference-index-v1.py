"""Run the current reference-index implementation with explicitly scoped output paths."""
from common_v2 import *
import argparse
sys.path.insert(0,str(ROOT));from tools import bandit
directory=RUN/'retrieval-snapshot-v1';assert not directory.exists()
original_manifest=sha('MANIFEST.md')
original_index={p.as_posix():sha(p) for p in Path('research-wiki/retrieval-index').glob('*.json')}
bandit.RETRIEVAL_INDEX_DIR=directory
bandit.MANIFEST=RUN/'reference-index-manifest-v1.md'
assert bandit.cmd_reference_index(argparse.Namespace())==0
assert sha('MANIFEST.md')==original_manifest
for p,h in original_index.items():assert sha(p)==h,p
files=sorted(directory.glob('*.json'));assert len(files)==8
write(RUN/'reference-index-scope-v1.json',dict(status='passed',implementation='tools.bandit.cmd_reference_index (same current CLI implementation, explicit Python output-directory/manifest adapter)',original_parser_has_no_scoped_output_option=True,canonical_indexes_unchanged=True,canonical_MANIFEST_unchanged=True,scope='Readonly retrieval inventory snapshot; not a second Book registry, Lean graph or accepted theorem library.',rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in files]))
print('Actual current reference-index implementation generated eight scoped retrieval snapshots; canonical indexes and MANIFEST unchanged.')
