from common import *

config = load(RUN/'delivery-preparation-config-20261011-v1.json')
scope = config['owned_canonical_scope'] + [
    RUN.relative_to(ROOT).as_posix(), CONTRACT.relative_to(ROOT).as_posix(),
    'tasks/'+TASK+'.md', 'conversion-windows/'+TASK+'.md',
    'proof-obligations/'+TASK+'.md', 'research-wiki/retrieval-index/'+TASK+'.md']
capture('preflight-scoped-stage-20261011-v1', 'git', 'add', '--', *scope)
code, out = capture('preflight-whitespace-20261011-v1', 'git', 'diff', '--check', BASE, required=False)
changed = subprocess.check_output(['git','diff','--cached','--name-only','-z',BASE]).decode('utf8').split('\0')
mismatches = []
staged = []
for relative in filter(None, changed):
    assert any(relative == s or relative.startswith(s+'/') for s in scope), relative
    blob = subprocess.check_output(['git','show',':'+relative])
    raw = (ROOT/relative).read_bytes()
    row = dict(path=relative, index_sha256=hashlib.sha256(blob).hexdigest(),
        raw_sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw), index_equals_raw=blob==raw)
    staged.append(row)
    if blob != raw: mismatches.append(row)
write(RUN/'preflight-staged-RAW-20261011-v1.json', dict(
    scope=scope, staged=staged, raw_index_mismatches=mismatches,
    whitespace_actual_exit=code, whitespace_lines=out.splitlines(),
    candidate_commit=False, gate_result='preflight only; any repair requires separate retained plan'))
print('Preflight staged files:', len(staged), 'RAW/index mismatches:', len(mismatches),
    'whitespace exit:', code, 'diagnostic lines:', len(out.splitlines()), flush=True)
for row in mismatches: print('RAW/index mismatch:', row['path'], flush=True)
for line in out.splitlines()[:24]: print(line, flush=True)
