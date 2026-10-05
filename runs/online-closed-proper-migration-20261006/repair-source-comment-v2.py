"""Repair a lexical comment hit without weakening the actual placeholder gate."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-CLOSED-PROPER-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
 p=Path(p);assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
assert load(run/'full-harness-v1-01-exit.json')['exit_code']==1
assert 'forbidden placeholder scan failed' in (run/'full-harness-v1-01.log').read_text(encoding='utf-8')
p=Path('BanditRLProof/OnlineClosedProper.lean');before=p.read_bytes();original=(run/'original-OnlineClosedProper.lean.txt').read_bytes()
assert before.endswith(original);needle=b'all eleven named axiom checks';assert before.count(needle)==1
snapshot=run/'leaves/pre-integration-comment-repair-OnlineClosedProper.lean.txt';assert not snapshot.exists();snapshot.write_bytes(before)
after=before.replace(needle,b'all eleven named kernel dependency checks');p.write_bytes(after)
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert after.endswith(original) and tokens(after.decode('utf-8'))==tokens(original.decode('utf-8'))
freeze=load(run/'draft-freeze-v1.json')
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(p,n).encode()).hexdigest()==h,n
for f,h in dict(freeze['canary'],**freeze['root_Tests']).items():assert sha(f)==h,f
assert not re.search(r'\b(sorry|admit|axiom|postulate)\b',after.decode('utf-8'))
write(run/'public-comment-qualification-v2.json',dict(path=p.as_posix(),original_sha256=sha(run/'original-OnlineClosedProper.lean.txt'),pre_repair_sha256=hashlib.sha256(before).hexdigest(),qualified_sha256=sha(p),exact_pre_repair_snapshot=snapshot.as_posix(),snapshot_sha256=sha(snapshot),delta='Only ordinary source comment: axiom checks -> kernel dependency checks; same11actual named #print axioms audit retained.',exact_original_bytes_retained_as_suffix=True,all_mathematical_tokens_headers_canary_root_Tests_fixed=True,previous_comment_metadata_superseded_additively='public-comment-qualification-v1.json',scan_rule='Actual tools/bandit.py:30002 regex scans comment text too; forbidden declaration rules unchanged.',failed_gate='full-harness-v1-01',full_gate_retry_pending=True))
ob=load(run/'proof-obligations-candidate-v1.json');ob['stage']='repair';ob['repair']='Lexical source comment hit only, no terminal/header/math/canary/test change; full v1 rawlog preserved/fullv2 pending.'
write(run/'proof-obligations-repair-v1.json',ob)
subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'repair-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','repair','--payload-json',json.dumps(dict(run_id=run.name,failed_gate='full-harness-v1-01',source_comment_only=True,mathematical_changes=False,frozen_headers=freeze['headers'],whole_canary_root_Tests_fixed=True,chapter_complete=False,goal_complete=False))],check=True)
print('Only source-comment lexical hit repaired, original raw suffix/math/fences/canary preserved; full retry pending.')
