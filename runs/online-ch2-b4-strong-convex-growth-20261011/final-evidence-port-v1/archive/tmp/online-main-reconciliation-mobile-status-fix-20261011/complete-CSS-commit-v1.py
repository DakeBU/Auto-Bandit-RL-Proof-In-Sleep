import hashlib,json,pathlib,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2];SRC=pathlib.Path(__file__).resolve().parent
def git(*a):return subprocess.check_output(['git',*a],cwd=ROOT)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipt=ROOT/'runs/online-main-reconciliation-20261011/secondary-mobile-status-repair/application-receipt-v1.json'
r=json.loads(receipt.read_bytes());head=git('rev-parse','HEAD').decode().strip();assert head==r['source_head']
css=ROOT/'website/static/site.css';candidate=SRC/'candidate-site-v2.css'
native=ROOT/'research-wiki/contribution-contracts/ONLINE-MAIN-MOBILE-STATUS-20261011.json'
assert sha(css)==r['production_css_RAW_sha256'] and sha(native)==r['native_sha256']
owned=[row['destination'] for row in r['archived_rows']]+[native.relative_to(ROOT).as_posix(),css.relative_to(ROOT).as_posix(),receipt.relative_to(ROOT).as_posix()]
for row in r['archived_rows']:
    assert sha(ROOT/row['destination'])==row['sha256']
    assert (ROOT/row['destination']).read_bytes()==(ROOT/row['source']).read_bytes()
for start in range(0,len(owned),35):git('-c','core.longpaths=true','add','-f','--',*owned[start:start+35])
staged=git('diff','--cached','--name-only','-z').decode().split('\0')[:-1];assert set(staged)==set(owned)
git('diff','--cached','--check')
for row in r['archived_rows']:assert hashlib.sha256(git('show',':'+row['destination'])).hexdigest()==row['sha256']
blob=git('show',':website/static/site.css');assert blob==candidate.read_bytes().replace(b'\r\n',b'\n')
git('commit','-m','Wrap online source-card statuses and long prose on narrow screens')
newhead=git('rev-parse','HEAD').decode().strip();assert git('rev-parse','HEAD^').decode().strip()==head
assert not git('status','--porcelain=v1','-z')
out=dict(head=newhead,parent=head,clean=True,owned_paths=len(staged),production_CSS_RAW_sha256=sha(css),
    production_CSS_index_LF_sha256=hashlib.sha256(blob).hexdigest(),archived_RAW_equals_index=True,
    mathematics_unchanged=True,actual_new_source_gates_rerun=False,actual_reader_accepted=False,maintenance_accepted=False,
    preparation_failure=dict(tool_chunk='e5f6d0',actual_exit=1,reason='Parent initial staging omitted -f for deliberately archived tmp paths. No mathematical edits. All copied bytes retained; exact owned-path force-stage used on resume.'))
target=SRC/'CSS-commit-receipt-v1.json'
with target.open('x',encoding='utf-8',newline='\n') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(out))
