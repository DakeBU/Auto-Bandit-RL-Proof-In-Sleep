import datetime,hashlib,json,subprocess,sys
from pathlib import Path
r=Path('E:/ABRL/worktrees/research-online-book')
b=r/'tmp/online-support-reader-tool-preparation-20261012'
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
helper=b/'capture-support-reader-v9.cjs';spec=b/'input-spec-execution-browser-v5.json'
assert digest(helper)=='239108918627409d1f7e981299853c1a24f703bf7de5c75ec5d92e1991a853a4'
assert digest(spec)=='48053e0dd5368c1bf467b639e73795bbf3285dcc3b99fa9fa7889f09773692df'
old=json.loads((b/'input-spec-execution-browser-v4.json').read_bytes());new=json.loads(spec.read_bytes())
expected=json.loads(json.dumps(old));expected['browser_helper_sha256']=digest(helper);expected['execution_helpers']['browser']=helper.name
assert expected==new
prev=json.loads((Path(__file__).parent/'browser-execution-v4-result.json').read_bytes());assert prev['actual_exit']==1
argv=prev['argv'][:];argv[1]=str(helper);argv[3]=str(b/'actual-render-v5');argv[4]=str(b/'isolated-profile-v5');argv[-2]=str(spec);argv[-1]=digest(spec)
assert not Path(argv[3]).exists() and not Path(argv[4]).exists()
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'argv':argv,'source_head':new['head'],'predecessor':'actual-render-v4 FAILED actual1: CSS uppercase algorithm-kind label','only_spec_changes':'browser helper name/hash; source/gates/structural bindings unchanged','started':True,'actual_exit':None}
with (Path(__file__).parent/'browser-execution-v5-start.json').open('x',encoding='utf-8') as f:json.dump(record,f,indent=2)
proc=subprocess.run(argv,cwd=r);record['actual_exit']=proc.returncode;record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (Path(__file__).parent/'browser-execution-v5-result.json').open('x',encoding='utf-8') as f:json.dump(record,f,indent=2)
sys.exit(proc.returncode)
