from delivery_guard_20261011_v3 import *
# Separate S3 inspector. This never builds a site, commits, stages, accepts or deploys.
a=arguments()
fixed(a,require_index=True)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,encoding='utf8').strip()
assert head!=BASE,'Parent-authorized source/evidence commit required; no commit is made here'
assert subprocess.check_output(['git','status','--porcelain=v1','-z'],cwd=ROOT)==b'','Clean start required'
site_path=RUN/('site-binding-'+a.tag+'.json')
binding=load(site_path)
site_head=binding['head']
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
        assert after.startswith(before),'Historical evidence changed instead of an exact-prefix append: '+relative
    # Existing files must be exact prefix appends; new files are independently versioned evidence.
    assert (ROOT/relative).read_bytes()==after and index[relative]==head_tree[relative],relative
    evidence.append(dict(path=relative,transition='added' if before is None else 'exact-prefix-append',before_sha256=None if before is None else hashlib.sha256(before).hexdigest(),after_sha256=hashlib.sha256(after).hexdigest()))
fixed(a,require_index=True);same_binding(binding['source_binding'])
assert subprocess.check_output(['git','status','--porcelain=v1','-z'],cwd=ROOT)==b'','Worktree changed during read-only inspection'
output=ROOT/'tmp'/('online-ch2-adaptive-osd-delivery-'+a.tag)/'exact-head-inspection-v4.json'
relative_output=output.relative_to(ROOT).as_posix()
assert not output.exists()
assert subprocess.run(['git','check-ignore','--no-index','-q','--',relative_output],cwd=ROOT).returncode==0,'Output must be Git-ignored'
assert subprocess.run(['git','ls-files','--error-unmatch','--',relative_output],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE).returncode!=0,'Output must not be tracked'
write(output,dict(site_build_head_H0=site_head,evidence_head_H1=head,H1_descends_H0=True,site_was_built_at_H1=(head==site_head),source_dirty_at_site_start=False,clean_at_inspection_start_and_before_receipt=True,whole_source_path_set_and_bytes_equal=True,HEAD_index_site_HEAD_RAW=source_rows,evidence_only_transition=evidence,site_binding=rows([site_path]),site_manifest=rows([manifest_path]),inspector=rows([Path(__file__).resolve(),RUN/'delivery_guard_20261011_v3.py',RUN/'common.py']),output_is_git_ignored=True,independent_exact_head_review='required separately; this is an inspection, not that review',native_final_acceptance='separate required evidence; not invoked or inferred',postnative_review='required separately',merged=False,deployed=False,worktree='retained',boundary='Site remains attributed to H0. H1 is only a descendant evidence head with identical complete source bytes and bounded added/append-only evidence. No assertion that H1 was rebuilt unless H0=H1.'))
print(output.as_posix(),flush=True)
