from delivery_guard_20261011_v1 import *
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
