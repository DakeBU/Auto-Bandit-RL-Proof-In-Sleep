from common_v1 import *
fixed()
modules = ['OnlineLearningFoundations','OnlineLearningHistory','OnlineLearningIID',
    'OnlineLearningInformation','OnlineLearningStochastic']
rows=[]
for n in modules:
    p=Path('BanditRLProof')/(n+'.lean')
    text=p.read_text(encoding='utf8')
    declarations=[]
    import re
    for m in re.finditer(r'^(?:(?:noncomputable|private) )?(?:theorem|lemma|def|structure)\s+(\S+)',text,re.M):
        declarations.append(dict(name=m.group(1),line=text[:m.start()].count('\n')+1))
    rows.append(dict(path=p.as_posix(),sha256=sha(p),declarations=declarations,
        actual_CI='missing changed contributor manifest relative to origin/main',
        required_audit_status='unreviewed/unwaived; dependency presence or previous root compile is not source acceptance'))
write(RUN/'five-old-modules-read-only-inventory-v1.json',dict(modules=rows,
    current_package_owns_these_proofs=False,source_contract_review_required=True,
    any_audit_closed=False,gate_bypassed=False,goal_complete=False))
prior=load('docs/contracts/online-randomized-iid-v1/chapter-one-source-ledger-accepted-v3.json')
draft=load(CONTRACT/'chapter-one-source-ledger-draft-v1.json')
assert draft['maintext_items']==prior['maintext_items']
assert len(draft['maintext_items'])==16 and draft['required_proof_leaf_total'] is None
assert all(i.get('required_maintext') for i in draft['maintext_items'])
write(RUN/'chapter-ledger-invariant-v1.json',dict(source_objects=16,exact_old_items_retained=True,
    proof_leaf_total=None,own_overlay_draft=True,chapter_complete=False,goal_complete=False))
gate('fetch-current-main-v1','git','-C','E:/ABRL/research','fetch','origin','main')
gate('canonical-state-v1','git','-C','E:/ABRL/research','status','--porcelain=v1')
assert (RUN/'canonical-state-v1.log').read_bytes()==b''
remote=subprocess.check_output(['git','ls-remote','origin','refs/heads/main'],encoding='utf8').split()[0]
assert remote=='6847b678a73db68dee5101d6f05c2453c1405afc'
write(RUN/'canonical-remote-main-v1.json',dict(exact_ls_remote_sha=remote,
    source_main_clean=True,source_main_edited=False,oldPR195stillstacked_unmerged=True))
fixed()
print('Read-only five-module inventory and unchanged16object ledger; no source audit or proof closure.')
