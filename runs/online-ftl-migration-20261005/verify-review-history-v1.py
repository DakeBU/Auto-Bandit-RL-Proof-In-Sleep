"""Resolve prior immutable reviews via explicit exact-raw supersession snapshots."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import _strip_lean_comments
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
snap={r['path']:r for r in load(run/'historical-raw-supersession-v1.json')['rows']}
receipts=[run/'source-contract-receipt-v1.json',run/'public-body-receipt-v1.json',
    Path('runs/online-ogd-migration-20261005/final-reader-receipt-v2.json')]
rows=[]
for p in receipts:
    x=load(p);assert sha(x['report'])==x['report_sha256'],p
    for r in x['reviewed_files']:
        current=sha(r['path']);original=r['sha256'];resolved=r['path'];delta='none'
        if current!=original:
            assert r['path'] in snap,(p,r['path'])
            s=snap[r['path']];assert sha(s['snapshot'])==original==s['raw_sha256'],(p,r['path'])
            resolved=s['snapshot'];delta=s['authorized_delta']
        rows.append(dict(receipt=p.as_posix(),path=r['path'],raw_sha256=original,
            resolved_raw_file=resolved,current_sha256=current,explicit_delta=delta))
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),
    ('website/content/highlights.json','highlights','chapter')]:
    old=load(snap[p]['snapshot']);new=load(p)
    assert set(old)==set(new),(p,'top-level keys')
    # Other reader routes and all IDs/links remain identical structured data.
    assert [x for x in old[k] if x.get(key)!='online-ftl-failure']==[x for x in new[k] if x.get(key)!='online-ftl-failure'],p
    for topkey in set(old)-{k}:assert old[topkey]==new[topkey],(p,topkey)
token=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert token(Path('BanditRLProof/OnlineFTLFailure.lean').read_text(encoding='utf-8'))==token((run/'original-public-module.lean.txt').read_text(encoding='utf-8'))
result=dict(status='passed',raw_rows_verified=len(rows),rows=rows,only_FTL_reader_subtrees_changed=True,
    old_OGD_reader_subtree_unchanged=True,FTL_all_code_tokens_unchanged=True,
    prior_accepted_OGD_report_receipt_bytes_unchanged=True,
    boundary='Only current FTL source/body and previous OGD final-reader bindings resolved here; earlier OGD historical supersession remains in its accepted audit, not re-certified by a new blanket verdict.')
with (run/'review-history-audit-v1.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
print('Exact current/prior final review bindings resolved:',len(rows),'raw rows; only FTL reader subtrees and code-free comment changed.')
