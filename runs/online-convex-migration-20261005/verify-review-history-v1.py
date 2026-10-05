"""Resolve immutable review bindings through explicit raw snapshot chains."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import _strip_lean_comments
run=Path(__file__).parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
snapshots={}
for p in [Path('runs/online-ogd-migration-20261005/historical-raw-supersession-v2.json'),Path('runs/online-ftl-migration-20261005/historical-raw-supersession-v1.json'),run/'historical-raw-supersession-v1.json']:
    x=load(p)
    for r in x['rows']:
        assert sha(r['snapshot'])==r['raw_sha256']
        snapshots[(r['path'],r['raw_sha256'])]=r
receipts=[run/'source-contract-receipt-v1.json',run/'public-body-receipt-v1.json',
    Path('runs/online-ftl-migration-20261005/source-contract-receipt-v1.json'),
    Path('runs/online-ftl-migration-20261005/public-body-receipt-v1.json'),
    Path('runs/online-ftl-migration-20261005/final-reader-receipt-v1.json'),
    Path('runs/online-ogd-migration-20261005/final-reader-receipt-v2.json')]
rows=[]
for p in receipts:
    x=load(p);assert sha(x['report'])==x['report_sha256'],p
    for r in x['reviewed_files']:
        current=sha(r['path']);original=r['sha256'];resolved=r['path'];delta='none'
        if current!=original:
            s=snapshots[(r['path'],original)];resolved=s['snapshot'];delta=s.get('authorized_delta',s.get('reason','explicit historical snapshot'))
            assert sha(resolved)==original
        rows.append(dict(receipt=p.as_posix(),path=r['path'],raw_sha256=original,resolved_raw_file=resolved,current_sha256=current,explicit_delta=delta))
snap={r['path']:r for r in load(run/'historical-raw-supersession-v1.json')['rows']}
selected={'online-convex','online-convex-closures'}
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
    old=load(snap[p]['snapshot']);new=load(p)
    assert set(old)==set(new)
    assert [x for x in old[k] if x.get(key) not in selected]==[x for x in new[k] if x.get(key) not in selected],p
    for t in set(old)-{k}:assert old[t]==new[t]
token=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
freeze=load(run/'draft-freeze-v1.json')
for p in freeze['modules']:assert token(Path(p).read_text(encoding='utf-8'))==token((run/('original-'+Path(p).stem+'.lean.txt')).read_text(encoding='utf-8')),p
for p,h in freeze['canaries'].items():assert sha(p)==h,p
result=dict(status='passed',raw_rows_verified=len(rows),rows=rows,only_two_convex_reader_subtrees_changed=True,all_Lean_code_tokens_unchanged=True,
    previous_FTL_OGD_reader_subtrees_unchanged=True,previous_accepted_reports_receipts_not_rewritten=True,
    boundary='Only listed current/prior bindings rehashed and explicitly resolved; earlier accepted supersession audits remain historical, not blanket re-certified.')
with (run/'review-history-audit-v1.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
print('Exact source/body/prior-final review bindings resolved:',len(rows),'raw rows; only selected convex reader subtrees/comment changes.')
