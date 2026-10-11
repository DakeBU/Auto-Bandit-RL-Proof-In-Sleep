import datetime,hashlib,json,subprocess,sys
from pathlib import Path
r=Path('E:/ABRL/worktrees/research-online-book');b=r/'tmp/online-support-reader-tool-preparation-20261012'
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
helper=b/'capture-support-reader-v10.cjs';spec=b/'input-spec-execution-browser-v6.json'
assert digest(helper)=='eb957dd5163c0191b896735caedf1dfa03d558da2c000ecbdded9eba3b351fca'
assert digest(spec)=='b076734c662847a673ff43aaae1f6163a9a78c0b81290183a20122db3abf9769'
old=json.loads((b/'input-spec-execution-browser-v5.json').read_bytes());new=json.loads(spec.read_bytes());expected=json.loads(json.dumps(old))
expected['browser_helper_sha256']=digest(helper);expected['execution_helpers']['browser']=helper.name;assert expected==new
prev=json.loads((Path(__file__).parent/'browser-execution-v5-result.json').read_bytes());assert prev['actual_exit']==1
argv=prev['argv'][:];argv[1]=str(helper);argv[3]=str(b/'actual-render-v6');argv[4]=str(b/'isolated-profile-v6');argv[-2]=str(spec);argv[-1]=digest(spec)
assert not Path(argv[3]).exists() and not Path(argv[4]).exists()
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'argv':argv,'source_head':new['head'],'predecessor':'actual-render-v5 FAILED actual1: inline MathJax zero clientWidth incorrectly classified as unscrollable clipping','only_spec_changes':'browser helper name/hash; source/gates/structural bindings unchanged','started':True,'actual_exit':None}
with (Path(__file__).parent/'browser-execution-v6-start.json').open('x',encoding='utf-8') as f:json.dump(record,f,indent=2)
proc=subprocess.run(argv,cwd=r);record['actual_exit']=proc.returncode;record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (Path(__file__).parent/'browser-execution-v6-result.json').open('x',encoding='utf-8') as f:json.dump(record,f,indent=2)
sys.exit(proc.returncode)
