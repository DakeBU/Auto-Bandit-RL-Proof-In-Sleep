from common_v1 import *

fixed()
write(RUN / 'preparation-failure-v1.json', dict(stage='draft', command='python -B -X utf8 runs/online-randomized-iid-20261008/prepare-contract-v1.py',
    exit_code=1, error='FileNotFoundError: old public-context-v2.lean does not exist; only draft headers v2 had changed',
    before_compile=True, no_semantic_target_change=True, original_helper_retained=True,
    repair='Locate actual public-context-v1.lean; restart helper with exact-equality create guard for already-created draft files.'))
original_write = write


def write(p, value):
    p = Path(p)
    data = value if isinstance(value, bytes) else (value.rstrip('\n') + '\n' if isinstance(value, str)
        else json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf8')
    if p.exists():
        assert p.read_bytes() == data, p
    else:
        original_write(p, value)


source = (RUN / 'prepare-contract-v1.py').read_text(encoding='utf8')
source = source.replace('from common_v1 import *\n', '', 1)
assert source.count('online-iid-benchmark-v1/public-context-v2.lean') == 1
source = source.replace('online-iid-benchmark-v1/public-context-v2.lean',
    'online-iid-benchmark-v1/public-context-v1.lean')
exec(compile(source, str(RUN / 'prepare-contract-v1.py'), 'exec'), globals())
