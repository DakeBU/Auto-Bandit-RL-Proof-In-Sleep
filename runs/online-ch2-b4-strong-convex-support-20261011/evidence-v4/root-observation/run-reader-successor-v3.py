import datetime,hashlib,json,subprocess,sys
from pathlib import Path
r=Path('E:/ABRL/worktrees/research-online-book')
b=r/'tmp/online-support-reader-tool-preparation-20261012'
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
helper=b/'capture-support-reader-v7.cjs'
spec=b/'input-spec-execution-browser-v3.json'
assert digest(helper)=='6a6e42693ed63d769095380e51ec989583465f0e16cd143e50d42f75d4cf7495'
assert digest(spec)=='4620373e3c0d2f17540cc195eac1160a9bb3b9f42dc6bd8bdb440cc555eea478'
old=json.loads((b/'input-spec-execution-browser-v2.json').read_bytes())
new=json.loads(spec.read_bytes())
expected=json.loads(json.dumps(old));expected['browser_helper_sha256']=digest(helper);expected['execution_helpers']['browser']=helper.name
assert expected==new
oldargv=json.loads((Path(__file__).parent/'browser-execution-argv-v2.json').read_bytes())['argv']
argv=oldargv[:]
argv[1]=str(helper)
argv[3]=str(b/'actual-render-v3')
argv[4]=str(b/'isolated-profile-v3')
argv[-2]=str(spec);argv[-1]=digest(spec)
assert not Path(argv[3]).exists() and not Path(argv[4]).exists()
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'argv':argv,'source_head':new['head'],'predecessor':'actual-render-v2 FAILED actual1: case-sensitive check of CSS uppercase status','only_spec_changes':'browser helper name/hash; source/gates/structural bindings unchanged','started':True,'actual_exit':None}
out=Path(__file__).parent/'browser-execution-v3-start.json'
with out.open('x',encoding='utf-8') as f:json.dump(record,f,indent=2)
proc=subprocess.run(argv,cwd=r)
record['actual_exit']=proc.returncode
record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (Path(__file__).parent/'browser-execution-v3-result.json').open('x',encoding='utf-8') as f:json.dump(record,f,indent=2)
sys.exit(proc.returncode)
