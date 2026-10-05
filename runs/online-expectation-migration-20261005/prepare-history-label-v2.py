from pathlib import Path
import hashlib,json
run=Path(__file__).parent;original=run/'verify-history-bindings-v1.py';target=run/'verify-history-bindings-v2.py'
assert not target.exists() and not (run/'history-binding-audit-v1.json').exists()
text=original.read_text(encoding='utf-8').replace('only_online_optimality_subtree_changed','only_online_expectation_subtree_changed').replace('selected optimality subtree only','selected expectation subtree only')
with target.open('w',encoding='utf-8',newline='\n') as handle:handle.write(text)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out=run/'auxiliary-history-label-version-v2.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as handle:
 json.dump(dict(original=original.as_posix(),original_sha256=sha(original),versioned=target.as_posix(),versioned_sha256=sha(target),delta='Two descriptive labels only, before first execution. Original v1 retained byte-exact; no mathematical/source/proof change.'),handle,indent=2);handle.write('\n')
print('Versioned two history descriptive labels before execution; original v1 preserved.')
