from pathlib import Path
import argparse,base64,hashlib,json,os,stat,subprocess,sys
ROOT=Path('E:/ABRL/worktrees/research-online-book')
RUN=ROOT/'runs/online-ch2-adaptive-osd-20261010'
CONTRACT=ROOT/'docs/contracts/online-ch2-adaptive-osd-v1'
H0='39e4bc0102227fce549c692bd5f18f20cc4b9983'
BRANCH='codex/research-online-ch2-adaptive-osd'
TASK='ONLINE-CH2-ADAPTIVE-OSD-20261010'
MESSAGE='Record reviewed adaptive OSD acceptance and validation evidence'
DOCS=[folder+'/'+TASK+'.md' for folder in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index']]
PREFIXES=[RUN.relative_to(ROOT).as_posix()+'/',CONTRACT.relative_to(ROOT).as_posix()+'/']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf8'))
def git(*args):return subprocess.check_output(['git']+list(args),cwd=ROOT)
def paths(data):return [x.decode('utf8') for x in data.split(b'\0') if x]
def allowed(p):return p in DOCS or any(p.startswith(x) for x in PREFIXES)
def tree(rev):
    out={}
    for entry in git('ls-tree','-rz','--full-tree',rev).split(b'\0'):
        if not entry:continue
        meta,name=entry.split(b'\t',1);mode,kind,oid=meta.split();out[name.decode()]=(mode.decode(),kind.decode(),oid.decode())
    return out
def index():
    out={}
    for entry in git('ls-files','--stage','-z').split(b'\0'):
        if not entry:continue
        meta,name=entry.split(b'\t',1);mode,oid,stage=meta.split();assert stage==b'0','Unmerged index'
        out[name.decode()]=(mode.decode(),'blob',oid.decode())
    return out
def raw_file(rel):
    p=ROOT/rel
    assert p.exists() and not p.is_symlink() and stat.S_ISREG(p.stat().st_mode),rel
    assert p.resolve()==p.absolute(),'No links/junctions in evidence paths: '+rel
    return p.read_bytes()
def blob(raw):return hashlib.new(FMT,b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
def status_scope():
    tokens=git('status','--porcelain=v1','-z','--untracked-files=all').split(b'\0')
    result=set()
    for row in filter(None,tokens):
        assert row[2:3]==b' ' and len(row)>3,'Malformed/rename status'
        code=row[:2].decode();relative=row[3:].decode('utf8')
        assert not any(c in code for c in 'RDCTU!'),'Delete/rename/type/conflict status: '+code
        assert code in [' M','M ','MM','A ','AM','??'],'Unexpected status: '+code
        assert allowed(relative),'Out of scope status: '+relative
        result.add(relative)
    changed=set(paths(git('diff','--name-only','--no-renames','-z',H0)))
    untracked=set(paths(git('ls-files','--others','--exclude-standard','-z')))
    assert all(allowed(x) for x in changed|untracked)
    assert result==changed|untracked,'Status/diff path disagreement'
    return sorted(result)

# Only the immutable finite 979-path audit permits checkout normalization differences.
def normalization_inputs(args,script_review_key,owned,source_paths):
    assert sha(args.normalization_audit)=='9d572dd1639994ade743a5ba4cb20b30099132bc3855c35e542bfd45ec861b83'
    assert sha(args.normalization_review)==args.normalization_review_sha
    nr=load(args.normalization_review)
    assert nr['verdict']=='accepted' and nr['blocking_repairs']==[]
    assert nr['approved_normalization_audit_sha256']=='9d572dd1639994ade743a5ba4cb20b30099132bc3855c35e542bfd45ec861b83'
    assert nr[script_review_key]==sha(Path(__file__).resolve())
    na=load(args.normalization_audit)
    assert na['H0']=='39e4bc0102227fce549c692bd5f18f20cc4b9983' and na['source_count']==1175
    assert na['all_exact_CRLF_to_LF_only'] is True and len(na['mismatches'])==979
    exceptions={row['path']:row for row in na['mismatches']}
    assert len(exceptions)==979 and set(exceptions).issubset(source_paths)
    assert len(owned)==12 and not set(owned).intersection(exceptions)
    assert all(row['exact_CRLF_to_LF_only'] is True for row in exceptions.values())
    return exceptions

def preserved_source_blob(relative,raw,expected_oid,git_format):
    if relative in NORMALIZATION_EXCEPTIONS:
        row=NORMALIZATION_EXCEPTIONS[relative]
        assert hashlib.sha256(raw).hexdigest()==row['raw_sha256']
        assert len(raw)==row['raw_bytes'] and raw.count(b'\r\n')==row['raw_CRLFs']
        normalized=raw.replace(b'\r\n',b'\n')
        assert raw!=normalized and len(normalized)==row['H0_blob_bytes']
        assert hashlib.sha256(normalized).hexdigest()==row['H0_blob_sha256']
        assert hashlib.new(git_format,b'blob '+str(len(normalized)).encode()+b'\0'+normalized).hexdigest()==expected_oid
        return False
    assert hashlib.new(git_format,b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==expected_oid,relative
    return True

def source_check(binding):
    assert len(binding)==1175
    guard.same_binding(binding)
    idx=index();out=[]
    for row in binding:
        p=Path(row['path']);rel=p.relative_to(ROOT).as_posix();raw=p.read_bytes()
        assert sha(p)==row['sha256'] and rel in TREE and rel in idx
        assert TREE[rel]==idx[rel] and TREE[rel][1]=='blob',rel
        exact=preserved_source_blob(rel,raw,TREE[rel][2],FMT)
        out.append(dict(path=rel,raw_sha256=row['sha256'],git_blob=TREE[rel][2],H0_index_Git_equal=True,unchanged_RAW_source_binding=True,RAW_equals_Git_blob=exact,normalization_exception=None if exact else NORMALIZATION_EXCEPTIONS[rel]))
    return out
def changes_check(names,state):
    idx=index();out=[]
    for rel in names:
        assert allowed(rel) and rel not in SOURCE_PATHS
        raw=raw_file(rel);before=git('show',H0+':'+rel) if rel in TREE else None
        if rel in TREE:assert TREE[rel][0]=='100644' and TREE[rel][1]=='blob',rel
        if rel in idx:assert idx[rel][0]=='100644' and idx[rel][1]=='blob',rel
        if before is not None:
            if rel==state['allowed_path']:
                assert hashlib.sha256(before).hexdigest()==state['H0_before_sha256']
                assert hashlib.sha256(raw).hexdigest()==state['actual_after_sha256']
                assert base64.b64decode(state['H0_before_RAW_base64'])==before
                assert base64.b64decode(state['actual_after_RAW_base64'])==raw
            else:assert raw.startswith(before),'Nonprefix historical evidence mutation: '+rel
        out.append(dict(path=rel,before_sha256=None if before is None else hashlib.sha256(before).hexdigest(),after_sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),transition='reviewed-single-state' if rel==state['allowed_path'] else 'new' if before is None else 'exact-prefix-append'))
    assert state['allowed_path'] in names and sum(x['transition']=='reviewed-single-state' for x in out)==1
    return out
ap=argparse.ArgumentParser();ap.add_argument('--review',type=Path,required=True);ap.add_argument('--review-sha',required=True);ap.add_argument('--execute',action='store_true',required=True);ap.add_argument('--receipt',type=Path,required=True);ap.add_argument('--normalization-audit',type=Path,required=True);ap.add_argument('--normalization-review',type=Path,required=True);ap.add_argument('--normalization-review-sha',required=True);a=ap.parse_args()
assert Path.cwd()==ROOT and git('branch','--show-current').decode().strip()==BRANCH
assert git('rev-parse','HEAD').decode().strip()==H0
output=a.receipt.resolve();assert ROOT/'tmp' in output.parents and not output.exists()
assert subprocess.run(['git','check-ignore','--no-index','-q','--',output.relative_to(ROOT).as_posix()],cwd=ROOT).returncode==0
assert subprocess.run(['git','ls-files','--error-unmatch','--',output.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE).returncode!=0
assert a.review.resolve()==RUN/'fresh-postnative-design-review-20261011-v1.json'
assert a.review_sha=='70540621b2c3cf40cae3a42b3341ffea3023180e80b77eacd5f00f276746931e'
assert sha(a.review)==a.review_sha;review=load(a.review)
assert review['verdict']=='accepted' and review['blocking_repairs']==[]
statepath=RUN/'S3-single-state-transition-proposed-20261011-v2.json'
actual=RUN/'native-package-actual-transition-20261011-v2.json'
s3=RUN/'inspect-exact-head-delivery-prepared-20261011-v5.py'
for p,key in [(statepath,'approved_state_proposal_sha256'),(actual,'approved_actual_transition_sha256'),(s3,'approved_inspector_sha256')]:assert sha(p)==review[key]
state=load(statepath);assert state['allowed_path']==PREFIXES[0]+'lifecycle-state.json' and state['no_blanket_allow'] is True
assert state['site_head_H0']==review['site_head_H0']==H0
assert state['H0_before_sha256']==review['approved_H0_state_sha256']
assert state['actual_after_sha256']==review['approved_actual_state_sha256']
assert review['whole_H0_to_actual_state_chain_reviewed'] is True
for row in state['actual_native_transition']+state['native_plan']+state['FINAL']:assert sha(row['path'])==row['sha256']
assert load(actual)['source_binding_unchanged'] and load(actual)['source_manifest_reader_coverage_unchanged']
# Hash trusted shared support before importing it; never modify those files.
guardpath=RUN/'delivery_guard_20261011_v3.py'
assert sha(guardpath)=='a446a3b51c5909d4267ae8e13e4455923ab68d6a25671b97004d4e81774ace8b'
assert sha(RUN/'common.py')=='f426be53126c83b41c92c20b7238b3c993ae2d73c6279a492df50559dfbc0be0'
sys.path.insert(0,str(RUN));import delivery_guard_20261011_v3 as guard
site=load(RUN/'site-binding-20261011-v2.json');assert site['head']==H0 and site['lean_verified'] and not site['source_dirty']
FMT=git('rev-parse','--show-object-format').decode().strip();assert FMT in ['sha1','sha256']
TREE=tree(H0);SOURCE_PATHS={Path(x['path']).relative_to(ROOT).as_posix() for x in site['source_binding']}
NORMALIZATION_EXCEPTIONS=normalization_inputs(a,'approved_H1_helper_sha256',guard.CONFIG['owned_canonical_scope'],SOURCE_PATHS)
receipt=dict(normalization_audit_sha256=sha(a.normalization_audit),normalization_review_sha256=sha(a.normalization_review),normalization_exception_count=979,exact_RAW_Git_source_count=196,helper_sha256=sha(Path(__file__).resolve()),review_sha256=a.review_sha,H0=H0,commit_message=MESSAGE,commands=[],result='not started',H1=None)
def command(args):
    p=subprocess.run(args,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    receipt['commands'].append(dict(command=args,actual_exit=p.returncode,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode()))
    return p
try:
    receipt['source_rows']=source_check(site['source_binding'])
    names=status_scope();receipt['evidence_rows']=changes_check(names,state)
    assert names,'No evidence change to commit'
    assert git('rev-parse','HEAD').decode().strip()==H0
    # Literal individual reviewed-scope paths only, no git add -A or repository-wide pathspec.
    result=command(['git','add','--']+names);assert result.returncode==0
    assert status_scope()==names and changes_check(names,state)==receipt['evidence_rows'],'Worktree changed while staging'
    assert sorted(paths(git('diff','--cached','--name-only','--no-renames','-z',H0)))==names
    idx=index()
    for row in receipt['evidence_rows']:
        rel=row['path'];raw=raw_file(rel);assert idx[rel]==('100644','blob',blob(raw)),rel
    source_check(site['source_binding'])
    check=command(['git','diff','--cached','--check',H0]);assert check.returncode==0 and check.stdout==b'','Unexpected whitespace diagnostics: exact output retained; no waiver'
    assert sha(a.review)==a.review_sha
    assert status_scope()==names and changes_check(names,state)==receipt['evidence_rows']
    assert git('rev-parse','HEAD').decode().strip()==H0
    commit=command(['git','commit','-m',MESSAGE]);assert commit.returncode==0
    h1=git('rev-parse','HEAD').decode().strip();receipt['H1']=h1
    assert h1!=H0 and git('rev-parse',h1+'^').decode().strip()==H0
    assert len(git('rev-list','--parents','-n','1',h1).decode().split())==2
    assert git('show','-s','--format=%s',h1).decode().strip()==MESSAGE
    assert sorted(paths(git('diff','--name-only','--no-renames','-z',H0,h1)))==names
    newtree=tree(h1);idx=index()
    for row in receipt['evidence_rows']:
        rel=row['path'];assert sha(ROOT/rel)==row['after_sha256'];assert newtree[rel]==idx[rel]==('100644','blob',blob(raw_file(rel)))
    for rel in SOURCE_PATHS:assert newtree[rel]==TREE[rel]
    source_check(site['source_binding'])
    assert git('status','--porcelain=v1','-z','--untracked-files=all')==b'','Worktree not clean after commit'
    receipt.update(actual_exit=0,result='committed reviewed bounded evidence',clean=True,source_count=1175,site_build_head_H0=H0,site_built_at_H1=False)
except BaseException as error:
    receipt.update(actual_exit=1,result='failed; no rollback or retry attempted',error_type=type(error).__name__,error=str(error))
    raise
finally:
    receipt['actual_head_after']=git('rev-parse','HEAD').decode().strip()
    actual_status=git('status','--porcelain=v1','-z','--untracked-files=all')
    receipt['actual_status_after_base64']=base64.b64encode(actual_status).decode()
    receipt['actual_clean_after']=(actual_status==b'')
    output.parent.mkdir(parents=True,exist_ok=True)
    with output.open('xb') as stream:stream.write((json.dumps(receipt,indent=2)+'\n').encode())
