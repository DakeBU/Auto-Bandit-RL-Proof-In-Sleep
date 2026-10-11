from pathlib import Path
import ast,hashlib,json
P=Path(__file__).resolve().parent;R=P.parent.parent
def rec(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
python=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe')
v6=R/'tmp/online-b4-vector-adapter-alpha-comparator-20261012/v6/pins-v6.json'
ast.parse((P/'capture-v2.py').read_text(encoding='utf-8'))
obj=dict(status='PREPARED_SYNTAX_CHECK_ONLY_NOT_EXECUTED',python=rec(python),operative_v6_pins=rec(v6),capture=rec(P/'capture-v2.py'),release='No Lean release supplied at preparation. Each later run must quote actual parent release. BODY requires separately provided header actual0 receipt path and SHA. IMPORT requires complete separately pinned input manifest and actual BODY olean/source binding.',normalization='Frozen header extracted literally LF; no proof/source rewrites.',limitations='This runner captures focused execution and immutable inputs. Genuine compiler module-origin and imported TYPE/VALUE/provider audits require their own probe and evidence; this preparation does not claim them.')
with (P/'capture-pins-v2.json').open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,indent=2);f.write('\n')
print(json.dumps(rec(P/'capture-pins-v2.json')))
