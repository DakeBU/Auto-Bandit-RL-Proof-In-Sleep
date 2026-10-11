from common import *
import argparse,re,gzip
assert sha(RUN/'common.py')=='f426be53126c83b41c92c20b7238b3c993ae2d73c6279a492df50559dfbc0be0','Imported common.py changed'
CONFIG=load(RUN/'delivery-preparation-config-20261011-v1.json')
PLAN=Path(CONFIG['plan']['path'])
def arguments():
    p=argparse.ArgumentParser()
    p.add_argument('--review',type=Path,required=True)
    p.add_argument('--review-sha',required=True)
    p.add_argument('--tag',required=True)
    p.add_argument('--allow-dirty-local-site',action='store_true')
    a=p.parse_args()
    assert re.fullmatch(r'[a-zA-Z0-9_-]+',a.tag)
    return a

def approve(a):
    assert sha(PLAN)==CONFIG['plan']['sha256']
    assert sha(a.review)==a.review_sha
    r=load(a.review)
    assert r.get('verdict') in ['accepted','accepted-with-explicit-delta']
    assert not r.get('blocking_repairs',r.get('required_repairs',[]))
    assert r.get('approved_plan_sha256',r.get('approved_plan_raw_sha256'))==sha(PLAN),'Review must explicitly approve exact plan hash'
    return r

def fixed(a,require_index=False):
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,encoding='utf8').strip()==BRANCH
    approve(a)
    plan=load(PLAN)
    for row in plan['rows']:
        assert sha(row['before_snapshot'])==row['before_sha256']
        assert sha(row['after_snapshot'])==row['after_sha256']==sha(row['path']),row['path']
    for row in plan['production_and_tests']: assert sha(row['path'])==row['sha256'],row['path']
    mr=plan['prospective_manifest'][0]
    assert sha(mr['path'])==mr['sha256']==sha(ROOT/plan['new_manifest'])
    if require_index:
        for relative in CONFIG['owned_canonical_scope']:
            p=ROOT/relative
            result=subprocess.run(['git','show',':'+relative],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            assert result.returncode==0,'Parent must explicitly stage all owned sources before harness: '+relative
            assert result.stdout==p.read_bytes(),'Git index differs from reviewed RAW: '+relative
    return plan

def source_binding():
    candidates=[ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',ROOT/'lean-toolchain',ROOT/'lakefile.lean',ROOT/'lake-manifest.json',ROOT/'.gitattributes']
    for folder,suffix in [('BanditRLProof','.lean'),('Tests','.lean'),('tools','.py'),('tools','.lean'),('website/scripts','.py'),('website/content','.json')]:
        candidates += [p for p in (ROOT/folder).rglob('*'+suffix) if p.is_file()]
    candidates += [ROOT/'docs/contracts/online-book-v1/coverage.json',ROOT/'research-wiki/contribution-contracts'/(TASK+'.json')]
    return rows(candidates)

def same_binding(binding):
    assert source_binding()==binding,'Complete source path set or source bytes changed since gate'

def output_of(path):
    d=load(path);raw=base64.b64decode(d['stdout_base64'])
    assert hashlib.sha256(raw).hexdigest()==d['stdout_sha256'] and d['actual_exit']==0
    return d,raw.decode('utf8',errors='replace')

def require_roots():
    checked=[]
    for filename,target in zip(CONFIG['root_receipts'],['BanditRLProof','Tests']):
        path=RUN/filename;d,out=output_of(path)
        assert d['command']==['lake','build',target] and d['cwd']==ROOT.as_posix()
        jobs=re.findall(r'Build completed successfully \((\d+) jobs\)',out)
        assert jobs and 'error: build failed' not in out
        checked.append(dict(target=target,receipt=rows([path])[0],cached_inclusive_jobs=list(map(int,jobs))))
    return checked
