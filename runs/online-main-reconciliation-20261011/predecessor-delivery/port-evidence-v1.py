"""Append exact local gate/reader/review bytes to RUN, after final review only."""
from pathlib import Path
import hashlib, json, subprocess, datetime
ROOT=Path('E:/ABRL/worktrees/research-online-book')
HEAD='7b372d79fcd3228d8d2cece73ad0181f94a70cf1'
RUN=ROOT/'runs/online-ch2-b4-finite-identity-20261011'
TMP=ROOT/'tmp'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_bytes())
def need(b,s):
    if not b: raise ValueError(s)
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT)
need(git('rev-parse','HEAD').decode().strip()==HEAD,'source HEAD')
need(not git('status','--porcelain=v1','-z'),'clean source required')
gates=TMP/'online-ch2-b4-finite-identity-gates-20261011'
review=TMP/'online-ch2-b4-finite-identity-final-review-20261011'
final=load(review/'final-review-v1.json')
need(not final.get('blockers',['missing blockers']),'independent final blockers')
need('accepted' in str(final.get('verdict','')).lower(),'explicit final acceptance')
inventory=load(gates/'full-harness-v1/pre-source-inputs.json')
for row in inventory:
    p=ROOT/row['path']; need(sha(p)==row['raw_sha256'] and p.stat().st_size==row['bytes'],'gated input changed '+row['path'])
jobs=[]
def tree(src,dest):
    need(src.is_dir(),'missing original '+str(src))
    for p in sorted(src.rglob('*')):
        if p.is_file(): jobs.append((p,RUN/dest/p.relative_to(src)))
def files(src,dest):
    for p in sorted(src.iterdir()):
        if p.is_file(): jobs.append((p,RUN/dest/p.name))
tree(gates,'actual-gates')
reader=TMP/'online-ch2-b4-finite-identity-reader-qa-20261011'
files(reader,'actual-reader/preparation')
tree(reader/'actual-v3','actual-reader/capture-v3')
tree(TMP/'online-ch2-b4-finite-identity-structural-qa-20261011','structural-qa')
tree(review,'independent-final')
tree(TMP/'online-ch2-b4-finite-identity-integrated-candidate-commit-20261011','integration-commit-evidence')
jobs.append((Path(__file__).resolve(),RUN/'delivery-prepared/port-evidence-v1.py'))
need(len({str(b) for a,b in jobs})==len(jobs),'duplicate destinations')
for src,dest in jobs: need(not dest.exists(),'create-only destination '+str(dest))
rows=[]
for src,dest in jobs:
    dest.parent.mkdir(parents=True,exist_ok=True); data=src.read_bytes(); dest.write_bytes(data)
    need(dest.read_bytes()==data,'exact port')
    rows.append({'original':str(src.relative_to(ROOT)).replace('\\','/'),'canonical':str(dest.relative_to(ROOT)).replace('\\','/'),'sha256':sha(dest),'bytes':len(data)})
for name in ['actual-gates','actual-reader','structural-qa','independent-final','integration-commit-evidence','delivery-prepared']:
    p=RUN/name/'.gitattributes';need(not p.exists(),'attrs create-only');p.write_bytes(b'* -text\n* whitespace=cr-at-eol\n*.raw -diff\n*.zip -diff\n*.png -diff\n')
for row in inventory: need(sha(ROOT/row['path'])==row['raw_sha256'],'active source changed after port')
record={'status':'exact append-only evidence port','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'gated_source_HEAD':HEAD,'delivery_commit':'not yet committed','rows':rows,'file_count':len(rows),'active_gated_RAW_rows_unchanged':len(inventory),'independent_final_original_sha256':sha(review/'final-review-v1.json'),'browser_profile_not_exported':str(reader/'edge-profile-v3'),'isolated_generated_site_retained':str(TMP/'online-ch2-b4-finite-identity-site-20261011-v1'),'boundary':'Only historical RUN evidence appended. No active source/input or frozen prior record was changed; gate HEAD remains distinct from later delivery HEAD. Whole B4 and 7+6 remain OPEN; C2partial/GoalACTIVE; unmerged/unpublished.'}
p=RUN/'exact-final-evidence-port-v1.json';need(not p.exists(),'port manifest create-only');p.write_bytes((json.dumps(record,ensure_ascii=False,indent=2)+'\n').encode())
print(json.dumps({'manifest':str(p),'sha256':sha(p),'files':len(rows),'active_RAW_unchanged':len(inventory)}))
