import datetime,hashlib,json,subprocess,sys
from pathlib import Path
r=Path('E:/ABRL/worktrees/research-online-book')
b=r/'tmp/online-support-reader-tool-preparation-20261012'
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
helper=b/'capture-support-reader-v8.cjs'
spec=b/'input-spec-execution-browser-v4.json'
assert digest(helper)=='e09ce710f9643fea30fd6d360dc763fcd584ff0c041038543452b604a5d89b2d'
assert digest(spec)=='6b60b8cb0a6d0a25b96e3443a4d414b65b834ff8776c91a3977294ad1bbebd77'
old=json.loads((b/'input-spec-execution-browser-v3.json').read_bytes())
new=json.loads(spec.read_bytes())
expected=json.loads(json.dumps(old));expected['browser_helper_sha256']=digest(helper);expected['execution_helpers']['browser']=helper.name
assert expected==new
prev=Path(__file__).parent/'browser-execution-v3-result.json'
assert json.loads(prev.read_bytes())['actual_exit']==1
argv=json.loads(prev.read_bytes())['argv'][:]
argv[1]=str(helper);argv[3]=str(b/'actual-render-v4');argv[4]=str(b/'isolated-profile-v4');argv[-2]=str(spec);argv[-1]=digest(spec)
assert not Path(argv[3]).exists() and not Path(argv[4]).exists()
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'argv':argv,'source_head':new['head'],'predecessor':'actual-render-v3 FAILED actual1: intentional MathJax own-overflow incorrectly classified as clipping','only_spec_changes':'browser helper name/hash; source/gates/structural bindings unchanged','started':True,'actual_exit':None}
with (Path(__file__).parent/'browser-execution-v4-start.json').open('x',encoding='utf-8') as f:json.dump(record,f,indent=2)
proc=subprocess.run(argv,cwd=r)
record['actual_exit']=proc.returncode;record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (Path(__file__).parent/'browser-execution-v4-result.json').open('x',encoding='utf-8') as f:json.dump(record,f,indent=2)
sys.exit(proc.returncode)
