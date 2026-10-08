from common_v1 import *

fixed()
original = RUN / 'prepare-contract-v1.py'
targets = load(CONTRACT / 'targets-v1.json')
assert len(targets['rows']) == 8
for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints']:
    assert 'Draft exact IID benchmark contract v1' in (Path(folder) / (TASK + '.md')).read_text(encoding='utf8')
missing = Path('research-wiki/retrieval-index') / (TASK + '.md')
assert not missing.exists()
write(RUN / 'contract-preparation-repair-v2.json', dict(failed_script=original.as_posix(), failed_script_sha256=sha(original),
    actual_exit_code=1, observed_exception='FileNotFoundError: research-wiki/retrieval-index/ONLINE-IID-BENCHMARK-20261008.md',
    stage='Four own task documents already appended; native new-task/blueprint does not create a retrieval-index file.',
    repair='Create only missing own retrieval-index document, then execute untouched remaining native retrieval/compiler tail.',
    targets_sha256=sha(CONTRACT / 'targets-v1.json'), public_context_sha256=sha(CONTRACT / 'public-context-v1.lean'),
    source_fingerprint_sha256=sha(CONTRACT / 'source-fingerprint-v1.json'), target_context_source_not_changed=True,
    mathematical_proof_failure=False, chapter_complete=False, goal_complete=False))
write(missing, '## Draft exact IID benchmark contract v1\n\n' + (CONTRACT / 'contract-v1.md').read_text(encoding='utf8') +
    '\nFrozen eight prospective headers: ' + sha(CONTRACT / 'targets-v1.json') + '; source/draft-type/body acceptance pending.\n')
source = original.read_text(encoding='utf8')
start = "write(RUN / 'native-reference-index-v1.py',"
assert source.count(start) == 1
exec(compile(start + source.split(start, 1)[1], str(original) + ':operational-resume-v2', 'exec'))
