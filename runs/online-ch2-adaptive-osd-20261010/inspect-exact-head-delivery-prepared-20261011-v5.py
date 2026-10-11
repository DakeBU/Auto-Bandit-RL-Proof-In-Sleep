from pathlib import Path
import sys,importlib.util
ROOT_FIXED=Path('E:/ABRL/worktrees/research-online-book')
RUN_FIXED=ROOT_FIXED/'runs/online-ch2-adaptive-osd-20261010'
sys.path.insert(0,str(RUN_FIXED))
from delivery_guard_20261011_v3 import *
# Separate S3 inspector. This never builds a site, commits, stages, accepts or deploys.
parser=argparse.ArgumentParser()
parser.add_argument('--review',type=Path,required=True)
parser.add_argument('--review-sha',required=True)
parser.add_argument('--tag',required=True,help='Actual site-binding tag')
parser.add_argument('--native-tag',required=True)
parser.add_argument('--evidence-head',required=True,help='Full actual committed H1; must equal git HEAD')
for name in ['native-plan','native-final','state-proposal','postnative-inputs','postnative-review','native-guard']:
    parser.add_argument('--'+name,type=Path,required=True)
parser.add_argument('--postnative-review-sha',required=True)
a=parser.parse_args()
assert ROOT==ROOT_FIXED and RUN==RUN_FIXED
assert re.fullmatch(r'[a-zA-Z0-9_-]+',a.tag) and re.fullmatch(r'[a-zA-Z0-9_-]+',a.native_tag)
assert sha(a.postnative_review)==a.postnative_review_sha
review=load(a.postnative_review)
assert review['verdict']=='accepted' and review['blocking_repairs']==[]
assert review['approved_inspector_sha256']==sha(Path(__file__).resolve())
for arg,key in [('state_proposal','approved_state_proposal_sha256'),('native_guard','approved_native_guard_sha256'),('native_plan','approved_native_plan_sha256'),('native_final','approved_FINAL_sha256'),('postnative_inputs','approved_postnative_inputs_sha256')]:
    path=getattr(a,arg).resolve();assert RUN in path.parents, arg
    assert sha(path)==review[key],arg
assert a.state_proposal.resolve()==RUN/('S3-single-state-transition-proposed-'+a.native_tag+'.json')
assert a.postnative_inputs.resolve()==RUN/('postnative-package-inputs-'+a.native_tag+'.json')
assert review['whole_H0_to_actual_state_chain_reviewed'] is True
spec=importlib.util.spec_from_file_location('reviewed_native_guard',a.native_guard.resolve())
native=importlib.util.module_from_spec(spec);spec.loader.exec_module(native)
native_plan,native_final=native.final_guard(a.native_plan,a.native_final,after=True)
assert native_plan['tag']==a.native_tag
native_transition=native.transition_check(native_plan,a.native_final)
postinputs=load(a.postnative_inputs)
same_binding(postinputs['source_binding'])
for row in postinputs['rows']:
    path=Path(row['path']);assert path.is_file() and sha(path)==row['sha256'],str(path)
state_proposal=load(a.state_proposal)
state_relative=RUN.relative_to(ROOT).as_posix()+'/lifecycle-state.json'
assert state_proposal['allowed_path']==state_relative and state_proposal['no_blanket_allow'] is True
for key,path in [('native_plan',a.native_plan),('FINAL',a.native_final)]:
    assert any(Path(row['path']).resolve()==path.resolve() and row['sha256']==sha(path) for row in state_proposal[key])
for row in state_proposal['actual_native_transition']:native.bound(row)

fixed(a,require_index=True)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,encoding='utf8').strip()
assert a.evidence_head==head and re.fullmatch(r'[0-9a-f]{40}|[0-9a-f]{64}',head),'Actual explicit H1 must equal HEAD'
assert review['evidence_head_H1']==head
assert head!=BASE,'Parent-authorized source/evidence commit required; no commit is made here'
assert subprocess.check_output(['git','status','--porcelain=v1','-z'],cwd=ROOT)==b'','Clean start required'
site_path=RUN/('site-binding-'+a.tag+'.json')
binding=load(site_path)
site_head=binding['head']
assert site_head=='39e4bc0102227fce549c692bd5f18f20cc4b9983'
assert native_plan['site_head']==state_proposal['site_head_H0']==review['site_head_H0']==site_head
assert state_proposal['evidence_head_H1'] in [None,head]
assert head!=site_head,'Postnative evidence H1 must be later than site H0'
assert binding['lean_verified'] and not binding['source_dirty'],'Only a recorded clean candidate site is eligible'
assert subprocess.run(['git','merge-base','--is-ancestor',site_head,head],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE).returncode==0,'Evidence HEAD must descend from site candidate HEAD'
same_binding(binding['source_binding'])
site=Path(binding['site']);manifest_path=site/'site-manifest.json'
manifest=load(manifest_path)
assert manifest['source_commit']==site_head and manifest['lean_verified'] and not manifest['source_dirty']
assert any(Path(r['path'])==manifest_path and sha(manifest_path)==r['sha256'] for r in binding['manifest'])
# Compare exact current HEAD, index and raw bytes for every path in the complete source set.
# Git blob identity hashes the literal byte length/header and content; no text filter is applied.
fmt=subprocess.check_output(['git','rev-parse','--show-object-format'],cwd=ROOT,encoding='utf8').strip()
assert fmt in ['sha1','sha256']
def tree_map(revision):
    data=subprocess.check_output(['git','ls-tree','-rz','--full-tree',revision],cwd=ROOT)
    result={}
    for entry in filter(None,data.split(b'\0')):
        meta,path=entry.split(b'\t',1);mode,kind,oid=meta.split(b' ')
        if kind==b'blob': result[path.decode('utf8')]=(mode.decode(),oid.decode())
    return result
head_tree=tree_map(head);site_tree=tree_map(site_head)
index={}
for entry in filter(None,subprocess.check_output(['git','ls-files','--stage','-z'],cwd=ROOT).split(b'\0')):
    meta,path=entry.split(b'\t',1);mode,oid,stage=meta.split(b' ')
    assert stage==b'0','Unmerged index entry'
    index[path.decode('utf8')]=(mode.decode(),oid.decode())
source_rows=[]
for row in binding['source_binding']:
    p=Path(row['path']);relative=p.relative_to(ROOT).as_posix();raw=p.read_bytes()
    oid=hashlib.new(fmt,b'blob '+str(len(raw)).encode('ascii')+b'\0'+raw).hexdigest()
    assert hashlib.sha256(raw).hexdigest()==row['sha256']
    assert relative in head_tree and relative in site_tree and relative in index,relative
    assert head_tree[relative]==index[relative]==site_tree[relative],relative
    assert head_tree[relative][1]==oid,'Raw bytes differ from HEAD/index blob: '+relative
    source_rows.append(dict(path=relative,raw_sha256=row['sha256'],git_object=oid,HEAD_index_site_HEAD_RAW_equal=True))
# Only own versioned evidence and append-only task documentation may differ between H0 and H1.
run_prefix=RUN.relative_to(ROOT).as_posix()+'/'
contract_prefix=CONTRACT.relative_to(ROOT).as_posix()+'/'
doc_paths={folder+'/'+TASK+'.md' for folder in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index']}
source_paths={r['path'] for r in source_rows}
changed=[p.decode('utf8') for p in subprocess.check_output(['git','diff','--name-only','--no-renames','-z',site_head,head],cwd=ROOT).split(b'\0') if p]
evidence=[]
for relative in changed:
    assert relative not in source_paths,'Owned mathematics/reader/source changed: '+relative
    assert relative.startswith(run_prefix) or relative.startswith(contract_prefix) or relative in doc_paths,'Out-of-scope evidence change: '+relative
    assert relative in head_tree,'Deleted evidence is prohibited: '+relative
    assert head_tree[relative][0]=='100644','Only ordinary evidence files allowed: '+relative
    after=subprocess.check_output(['git','show',head+':'+relative],cwd=ROOT)
    before=None
    if relative in site_tree:
        assert site_tree[relative][0]=='100644'
        before=subprocess.check_output(['git','show',site_head+':'+relative],cwd=ROOT)
        if relative==state_relative:
            assert hashlib.sha256(before).hexdigest()==state_proposal['H0_before_sha256']
            assert hashlib.sha256(after).hexdigest()==state_proposal['actual_after_sha256']
            assert base64.b64decode(state_proposal['H0_before_RAW_base64'])==before
            assert base64.b64decode(state_proposal['actual_after_RAW_base64'])==after
            assert review['approved_H0_state_sha256']==state_proposal['H0_before_sha256']
            assert review['approved_actual_state_sha256']==state_proposal['actual_after_sha256']
        else:
            assert after.startswith(before),'Historical evidence changed instead of an exact-prefix append: '+relative
    # Existing files must be exact prefix appends; new files are independently versioned evidence.
    assert (ROOT/relative).read_bytes()==after and index[relative]==head_tree[relative],relative
    evidence.append(dict(path=relative,transition='reviewed-exact-state-hashpair' if relative==state_relative else 'added' if before is None else 'exact-prefix-append',before_sha256=None if before is None else hashlib.sha256(before).hexdigest(),after_sha256=hashlib.sha256(after).hexdigest()))
assert state_relative in changed and state_relative in site_tree,'Only existing reviewed lifecycle state can receive exception'
assert sum(row['transition']=='reviewed-exact-state-hashpair' for row in evidence)==1
native.final_guard(a.native_plan,a.native_final,after=True);native.transition_check(native_plan,a.native_final)
fixed(a,require_index=True);same_binding(binding['source_binding'])
assert subprocess.check_output(['git','status','--porcelain=v1','-z'],cwd=ROOT)==b'','Worktree changed during read-only inspection'
output=ROOT/'tmp'/('online-ch2-adaptive-osd-delivery-'+a.native_tag)/'exact-head-inspection-v5.json'
relative_output=output.relative_to(ROOT).as_posix()
assert not output.exists()
assert subprocess.run(['git','check-ignore','--no-index','-q','--',relative_output],cwd=ROOT).returncode==0,'Output must be Git-ignored'
assert subprocess.run(['git','ls-files','--error-unmatch','--',relative_output],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE).returncode!=0,'Output must not be tracked'
write(output,dict(site_build_head_H0=site_head,evidence_head_H1=head,H1_descends_H0=True,site_was_built_at_H1=(head==site_head),source_dirty_at_site_start=False,clean_at_inspection_start_and_before_receipt=True,whole_source_path_set_and_bytes_equal=True,HEAD_index_site_HEAD_RAW=source_rows,evidence_only_transition=evidence,site_binding=rows([site_path]),site_manifest=rows([manifest_path]),inspector=rows([Path(__file__).resolve(),RUN/'delivery_guard_20261011_v3.py',RUN/'common.py']),output_is_git_ignored=True,independent_exact_head_review='required separately; this is an inspection, not that review',native_final_acceptance='Prior actual acceptance checked via final_guard(after=True) and transition_check; no action invoked',postnative_review=rows([a.postnative_review]),state_proposal=rows([a.state_proposal]),native_plan=rows([a.native_plan]),FINAL=rows([a.native_final]),native_guard=rows([a.native_guard]),postnative_inputs=rows([a.postnative_inputs]),merged=False,deployed=False,worktree='retained',boundary='Site remains attributed to H0. H1 is only a descendant evidence head with identical complete source bytes and bounded added/append-only evidence plus exactly one independently approved lifecycle-state byte transition. No assertion that H1 was rebuilt unless H0=H1.'))
print(output.as_posix(),flush=True)
