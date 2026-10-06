"""Prepare immutable hash-bound PR helpers, without changing accepted evidence."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
old=Path('runs/online-subgradient-basic-migration-20261006/create-pr-v1.py')
text=old.read_text(encoding='utf-8')
replacements={
 'PR166':'PR167','pulls/166':'pulls/167',
 '283e359e2b85740ad557574d337d6f4a1d55fe8f':'b7b72d2c587128ddb639b2fd40c27016f20555bc',
 'codex/research-online-subgradient-basic-migration':'__CURRENT_BRANCH__',
 'codex/research-online-closed-proper-migration':'codex/research-online-subgradient-basic-migration',
 'codex%2Fresearch-online-subgradient-basic-migration':'codex%2Fresearch-online-subgradient-interior-migration'}
for before,after in replacements.items():
 assert before in text,before
 text=text.replace(before,after)
text=text.replace('__CURRENT_BRANCH__','codex/research-online-subgradient-interior-migration')
p=run/'create-pr-v1.py';assert not p.exists()
p.write_bytes(text.encode('utf-8'))
names=['create-pr-v1.py','prepare-delivery-v1.py','commit-owned-v1.py','check-scoped-diff-v1.py']
rows=[dict(path=(run/n).as_posix(),sha256=hashlib.sha256((run/n).read_bytes()).hexdigest()) for n in names]
p=run/'delivery-helpers-before-use-v1.json';assert not p.exists()
p.write_bytes((json.dumps(dict(rows=rows,prepared_from=dict(path=old.as_posix(),sha256=hashlib.sha256(old.read_bytes()).hexdigest()),read_only_diagnostic='PowerShell rg literal *overlay* pathname returned123; subsequent reads use actual rg --files and -g filter. No mutation or gate change.'),indent=2)+'\n').encode('utf-8'))
print('Four exact helpers bound before use; draft REST creation still pending.')
