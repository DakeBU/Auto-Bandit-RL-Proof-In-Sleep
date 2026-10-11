import hashlib,json,pathlib,subprocess
from datetime import datetime,timezone
ROOT=pathlib.Path(__file__).resolve().parents[2]
SRC=pathlib.Path(__file__).resolve().parent
RUN=ROOT/'runs/online-main-reconciliation-20261011/secondary-mobile-status-repair'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=ROOT)
def write(p,o):
    p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(o,f,indent=2);f.write('\n')
head=git('rev-parse','HEAD').decode().strip()
assert head=='cb7ea30f3f74db0bc459e9629be092665023718f' and not git('status','--porcelain=v1','-z')
css=ROOT/'website/static/site.css';candidate=SRC/'candidate-site-v2.css'
assert sha(css)=='775a3b696a1112188fb0eef587a16fa38b1c6188090313a781e1e0dcacc47791'
assert sha(candidate)=='5b126bf7c0739879b941dfddba81fef3ae3ba9819c06d24cac6b805c5c29698c'
review=SRC/'independent-status-CSS-review-v1.json'
assert sha(review)=='4e78d2364214becbc8a66eb86cbe4220fb105e876078d8008ca02fcd2c7ecf03'
assert json.loads(review.read_bytes())['verdict']=='accepted-bounded-CSS-application-eligibility'
native=SRC/'native-contribution-manifest-draft-v1.json'
assert sha(native)=='d1ef9334f6801b2e3831fbc26b96325835e488a827d4f80526a7a14e8d9b237f'
native_dest=ROOT/'research-wiki/contribution-contracts/ONLINE-MAIN-MOBILE-STATUS-20261011.json'
assert not native_dest.exists() and not RUN.exists()
paths=[SRC/name for name in ['original-site.css','candidate-site-v2.css','site-v2.css.diff','status-fix-plan-v1.json',
    'independent-status-CSS-review-v1.json','native-contribution-manifest-draft-v1.json','prepare-native-manifest-v1.py',
    'simulated-reader-preview-v5.cjs','simulated-preview-v5-summary.json','preview-receipt-v5.json',
    'preview-v5-argv.json','preview-v10-to-simulation-v5.diff','preview-v5.stdout.raw','preview-v5.stderr.raw']]
paths.extend([ROOT/'tmp/online-main-reconciliation-reader-qa-20261011'/name for name in [
    'capture-reconciliation-reader-v9.cjs','capture-reconciliation-reader-v10.cjs','reader-v9-to-v10.diff','reader-v10-author-self-audit-v1.json']])
paths.extend([ROOT/'tmp/online-main-reconciliation-helper-independent-review-20261011'/name for name in [
    'independent-helper-review-v5.json','independent-helper-review-v5.md']])
paths.extend(sorted((SRC/'preview-v5').rglob('*')))
paths=[p for p in paths if p.is_file()]+[pathlib.Path(__file__).resolve()]
rows=[]
for p in paths:
    rel=p.relative_to(ROOT);dest=RUN/'archive'/rel
    rows.append(dict(source=rel.as_posix(),destination=dest.relative_to(ROOT).as_posix(),sha256=sha(p),bytes=p.stat().st_size))
assert len({r['destination'].casefold() for r in rows})==len(rows)
for row in rows:
    source=ROOT/row['source'];dest=ROOT/row['destination'];dest.parent.mkdir(parents=True,exist_ok=True)
    with dest.open('xb') as f:f.write(source.read_bytes())
    assert sha(dest)==row['sha256']
with native_dest.open('xb') as f:f.write(native.read_bytes())
css.write_bytes(candidate.read_bytes())
receipt=RUN/'application-receipt-v1.json'
write(receipt,dict(status='REVIEWED_CSS_APPLIED_READER_ACCEPTANCE_PENDING',source_head=head,baseline_gate_source_head='4034f9d3c63acbb3a1b62a2683ed35c204923246',
    archived_rows=rows,production_css_RAW_sha256=sha(css),native_sha256=sha(native_dest),
    simulation_only=True,simulated_exit=0,actual_source_reader_accepted=False,maintenance_accepted=False,
    mathematical_sources_changed=False,reader_pending=True,Goal='ACTIVE',utc=datetime.now(timezone.utc).isoformat(),
    pending='Fresh combined proof/root/Tests/harness/axiom/site/actual reader/semantic/purification/PR gates. Prior reader failures and complete historical resource ports remain local and must be retained in delivery archive.'))
owned=[r['destination'] for r in rows]+[native_dest.relative_to(ROOT).as_posix(),css.relative_to(ROOT).as_posix(),receipt.relative_to(ROOT).as_posix()]
for start in range(0,len(owned),35):git('-c','core.longpaths=true','add','--',*owned[start:start+35])
staged=git('diff','--cached','--name-only','-z').decode().split('\0')[:-1];assert set(staged)==set(owned)
git('diff','--cached','--check')
for row in rows:
    blob=git('show',':'+row['destination']);assert hashlib.sha256(blob).hexdigest()==row['sha256']
production_blob=git('show',':website/static/site.css');assert production_blob==candidate.read_bytes().replace(b'\r\n',b'\n')
git('commit','-m','Wrap online source-card statuses and long prose on narrow screens')
newhead=git('rev-parse','HEAD').decode().strip();assert git('rev-parse','HEAD^').decode().strip()==head
assert not git('status','--porcelain=v1','-z')
out=dict(head=newhead,parent=head,clean=True,owned_paths=len(staged),production_CSS_RAW_sha256=sha(css),
    production_CSS_index_LF_sha256=hashlib.sha256(production_blob).hexdigest(),archived_RAW_equals_index=True,
    mathematics_unchanged=True,actual_new_source_gates_rerun=False,actual_reader_accepted=False,maintenance_accepted=False)
write(SRC/'CSS-commit-receipt-v1.json',out)
print(json.dumps(out))
