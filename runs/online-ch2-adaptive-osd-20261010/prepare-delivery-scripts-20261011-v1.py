from common import *
import ast
scripts={}
scripts['delivery_guard_20261011_v1.py']=r'''from common import *
import argparse,re,gzip
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
    assert r.get('approved_plan_sha256')==sha(PLAN),'Review must explicitly approve exact plan hash'
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
    for folder,suffix in [('BanditRLProof','.lean'),('Tests','.lean'),('tools','.py'),('website/scripts','.py'),('website/content','.json')]:
        candidates += [p for p in (ROOT/folder).rglob('*'+suffix) if p.is_file()]
    candidates += [ROOT/'docs/contracts/online-book-v1/coverage.json',ROOT/'research-wiki/contribution-contracts'/(TASK+'.json')]
    return rows(candidates)

def same_binding(binding):
    for row in binding: assert sha(row['path'])==row['sha256'],row['path']

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
'''
scripts['run-full-harness-prepared-20261011-v1.py']=r'''from delivery_guard_20261011_v1 import *
a=arguments();fixed(a,require_index=True);roots=require_roots();binding=source_binding()
label='full-harness-'+a.tag
code,out=capture(label,sys.executable,'-B','-X','utf8','tools/bandit.py','check',required=False)
# Always retain command output before interpreting success/failure.
assert code==0,out[-12000:]
jobs=re.findall(r'Build completed successfully \((\d+) jobs\)',out)
tests=re.findall(r'Ran (\d+) tests in ([\d.]+)s',out)
assert jobs and tests and re.search(r'\nOK(?: \(skipped=\d+\))?\s',out)
assert 'check passed' in out and 'tools/ProofGraphExport.lean' in out
assert all(x not in out for x in ['error: build failed','Lean exited with code 1','forbidden placeholder scan failed'])
fixed(a,require_index=True);same_binding(binding)
write(RUN/('full-harness-inspected-'+a.tag+'.json'),dict(actual_exit=0,actual_check_passed=True,actual_ProofGraphExport_compile_present=True,root_receipts=roots,command_receipt=rows([RUN/(label+'.json')])[0],source_binding=binding,cached_inclusive_build_jobs=list(map(int,jobs)),unittest_runs=tests,skip_markers=re.findall(r'OK \(skipped=(\d+)\)',out),review=rows([a.review]),native_package_chapter_acceptance=False,site_and_delivery='pending'))
'''
scripts['run-contributor-gates-prepared-20261011-v1.py']=r'''from delivery_guard_20261011_v1 import *
a=arguments();fixed(a,require_index=True);binding=source_binding()
receipts=[]
for label,base in [('stack',CONFIG['base']),('main',CONFIG['origin_main_at_preparation'])]:
    changed=subprocess.check_output(['git','diff','--name-only',base],cwd=ROOT,encoding='utf8').splitlines()
    for name in ['OnlineAdaptivePotential','OnlineAdaptiveOSD','OnlineAdaptiveBenchmark']:
        assert 'BanditRLProof/'+name+'.lean' in changed,'Nonempty substantive diff required'
    code,out=capture('contributor-'+label+'-'+a.tag,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base,required=False)
    assert code==0 and 'not applicable' not in out.lower(),out
    receipts.append(dict(base=base,receipt=rows([RUN/('contributor-'+label+'-'+a.tag+'.json')])[0]))
fixed(a,require_index=True);same_binding(binding)
write(RUN/('contributor-inspected-'+a.tag+'.json'),dict(checks=receipts,source_binding=binding,nonempty_substantive_diff=True,origin_main_is_pinned_historical_snapshot=True,boundary='No native/package/chapter or merge acceptance'))
'''
scripts['summarize-axioms-prepared-20261011-v1.py']=r'''from delivery_guard_20261011_v1 import *
a=arguments();fixed(a);declarations={};inputs=[]
for name in CONFIG['axiom_receipts']:
    path=RUN/name;d,out=output_of(path)
    assert d['command'][:3]==['lake','env','lean'] and d['cwd']==ROOT.as_posix()
    matches=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",out)
    assert matches,name
    for decl,raw in matches:
        axioms=set(raw.split(', ')) if raw else set()
        assert axioms.issubset({'propext','Classical.choice','Quot.sound'}),(decl,axioms)
        assert decl not in declarations
        declarations[decl]=dict(axioms=sorted(axioms),receipt=path.as_posix())
    inputs+=rows([path])
assert len(declarations)==39
mapping=load(load(PLAN)['mapping'][0]['path'])
production={x['name'] for x in mapping['canonical_declarations'] if x['kind']=='theorem'}
assert len(production)==30 and production.issubset(declarations)
write(RUN/('axiom-summary-'+a.tag+'.json'),dict(source_binding=source_binding(),inputs=inputs,public_theorem_count=39,production_theorems=30,canary_theorems=9,actual_prior_public_output_revalidated=True,fresh_compiler_run=False,declarations=declarations,boundary='Revalidation of actual captured public probes at unchanged source hashes; standard axioms only, not semantic/chapter or new compiler evidence'))
'''
scripts['build-local-site-prepared-20261011-v1.py']=r'''from delivery_guard_20261011_v1 import *
a=arguments();fixed(a);gate=load(RUN/('full-harness-inspected-'+a.tag+'.json'))
assert gate['actual_exit']==0 and gate['actual_check_passed'] and gate['actual_ProofGraphExport_compile_present']
r=gate['command_receipt'];assert sha(r['path'])==r['sha256'];d,out=output_of(r['path'])
assert d['command'][-2:]==['tools/bandit.py','check'] and 'check passed' in out
same_binding(gate['source_binding'])
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,encoding='utf8').strip()
status=subprocess.check_output(['git','status','--porcelain=v1','-z'],cwd=ROOT)
assert not status or a.allow_dirty_local_site,'Default requires clean source at site start; parent must explicitly choose dirty local preview'
site=ROOT/'tmp'/('online-ch2-adaptive-osd-site-'+a.tag)
assert not site.exists(),'Create-only output directory required'
# No commit, staging, acceptance or deployment command is present here.
capture('site-build-'+a.tag,sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site)
m=load(site/'site-manifest.json')
assert m['lean_verified'] and m['source_commit']==head
assert m['source_dirty']==bool(status)
fixed(a);same_binding(gate['source_binding'])
capture('site-check-'+a.tag,sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
write(RUN/('site-binding-'+a.tag+'.json'),dict(site=site.as_posix(),head=head,source_dirty=bool(status),lean_verified=True,full_harness=rows([RUN/('full-harness-inspected-'+a.tag+'.json')]),source_binding=gate['source_binding'],manifest=rows([site/'site-manifest.json']),deployed=False,boundary='Local preview only; rendered-pixel and postcommit exact-head delivery review separate; dirty local build never claimed clean'))
'''
scripts['verify-registry-prepared-20261011-v1.py']=r'''from delivery_guard_20261011_v1 import *
a=arguments();fixed(a);binding=load(RUN/('site-binding-'+a.tag+'.json'));site=Path(binding['site']);same_binding(binding['source_binding'])
c=CONFIG['registry_compressed'];assert sha(c['path'])==c['sha256']
raw=gzip.decompress(Path(c['path']).read_bytes());old=json.loads(raw)
assert hashlib.sha256(raw).hexdigest()==CONFIG['registry_baseline']['registry']['sha256']
current=load(site/'books/registry.json');manifest=load(site/'site-manifest.json')
assert current['source_commit']==manifest['source_commit']==binding['head'] and current['lean_verified'] and manifest['lean_verified']
assert current['identity']==old['identity']
ob={n['id']:n for n in old['nodes']};nb={n['id']:n for n in current['nodes']}
assert len(ob)==len(old['nodes'])==CONFIG['registry_baseline']['nodes']
assert len(nb)==len(current['nodes'])==CONFIG['expected_total']
for key,value in ob.items(): assert nb[key]==value,key
assert set(nb)-set(ob)==set(CONFIG['new_registry_ids'])
modules={}
for key in CONFIG['new_registry_ids']:
    n=nb[key];assert n['identity_basis']=='source-qualified-name'
    url=n['url'].split('#')[0];p=site/url;assert p.is_file();modules[url]=sha(p)
assert not any('OnlineAdaptiveOSDCanary' in key or 'OnlineAdaptivePotentialCanary' in key for key in nb)
reading=next(r for r in load(ROOT/'website/content/readings.json')['readings'] if r['slug']=='online-ogd')
assert len(reading['source_theorems'])==CONFIG['expected_source_cards']
write(RUN/('registry-inspected-'+a.tag+'.json'),dict(source_commit=binding['head'],source_dirty=binding['source_dirty'],lean_verified=True,baseline_nodes=len(ob),retained_complete_old_objects=True,new_nodes=40,structural_breakdown=CONFIG['structural_counts'],total_nodes=len(nb),source_cards=len(reading['source_theorems']),module_HTML_sha256=modules,registry=rows([site/'books/registry.json']),chapter_proof_total=None,chapter_complete=False,deployed=False,pixel_review='separate required gate'))
'''
scripts['inspect-exact-head-delivery-prepared-20261011-v1.py']=r'''from delivery_guard_20261011_v1 import *
a=arguments();fixed(a,require_index=True)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,encoding='utf8').strip()
assert head!=BASE,'A future parent-authorized source commit is required; this script never commits'
status=subprocess.check_output(['git','status','--porcelain=v1','-z'],cwd=ROOT)
assert not status,'Exact-head delivery inspection requires clean worktree at start'
files=[]
for relative in CONFIG['owned_canonical_scope']:
    blob=subprocess.check_output(['git','show','HEAD:'+relative],cwd=ROOT)
    assert blob==(ROOT/relative).read_bytes(),relative
    files.append(dict(path=relative,sha256=hashlib.sha256(blob).hexdigest(),head_blob_equals_raw=True))
binding=load(RUN/('site-binding-'+a.tag+'.json'))
assert binding['head']==head and not binding['source_dirty'] and binding['lean_verified']
same_binding(binding['source_binding'])
write(RUN/('exact-head-delivery-inspection-'+a.tag+'.json'),dict(head=head,clean_at_start=True,owned_HEAD_blobs=files,site_binding=rows([RUN/('site-binding-'+a.tag+'.json')]),independent_exact_head_delivery_review='required separately',native_final_acceptance='required separately; not invoked',post_native_exact_head_review='required separately',merged=False,deployed=False,worktree='retained'))
'''
for name,text in scripts.items():
    ast.parse(text,filename=name)
    write(RUN/name,text)
write(RUN/'delivery-scripts-prepared-20261011-v1.json',dict(config=rows([RUN/'delivery-preparation-config-20261011-v1.json']),scripts=rows([RUN/name for name in scripts]),ast_parse=True,executed=False,requirements=['Exact favorable review must expose verdict, approved_plan_sha256, blocking_repairs/required_repairs.', 'Parent stages reviewed sources/index RAW; scripts do not stage.', 'Use matching --tag across all commands and parent-reviewed exact version.', 'Full harness runs after exact metadata apply and completed root/Tests.', 'Site uses full-harness source binding; clean default, dirty preview only explicit flag.', 'Native final acceptance, postnative/semantic FINAL and independent exact-head review remain separate; scripts do not execute them.']))
print('Prepared and AST-checked',len(scripts),'scripts; none executed.')
