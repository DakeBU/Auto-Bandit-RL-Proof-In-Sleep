"""Repair import placement parsing only, preserving every mathematical token."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-GUESSING-MIGRATION-20261006'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert load(run/'focused-v1-01-exit.json')['exit_code']!=0
assert "invalid 'import' command" in (run/'focused-v1-01.log').read_text(encoding='utf-8')
gate('import-comment-repair-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','repair','--payload-json',json.dumps(dict(run_id=run.name,failed_build='focused-v1-01',reason='Module doc comment before imports was a command; replace only newly inserted leading doc marker by ordinary ignored block comment.',mathematical_target_changed=False,proof_tokens_changed=False)))
rows=[]
for p in ['BanditRLProof/OnlineGuessingOGD.lean','BanditRLProof/OnlineGuessingLower.lean','BanditRLProof/OnlineGuessingComparison.lean']:
 path=Path(p);raw=path.read_bytes();assert raw.startswith(b'/-!')
 snap=run/'leaves'/('import-comment-before-repair-'+path.name+'.txt');assert not snap.exists();snap.write_bytes(raw)
 path.write_bytes(b'/-'+raw[3:])
 assert tokens(raw.decode('utf-8'))==tokens(path.read_text(encoding='utf-8'))
 rows.append(dict(path=p,snapshot=snap.as_posix(),raw_sha256=sha(snap),corrected_sha256=sha(path),delta='Only new leading /-! marker -> /-, before imports; all mathematical tokens unchanged'))
freeze=load(run/'draft-freeze-v2.json');headers=load('docs/contracts/online-guessing-migration-v1/headers-native-v2.json')
for n,row in headers.items():assert hashlib.sha256(lean_declaration_header(Path(row['file']),n).encode()).hexdigest()==freeze['headers'][n]
for p,h in freeze['canary'].items():assert sha(p)==h
write('import-comment-repair-v2.json',dict(status='format-only-parser-repair',rows=rows,actual_failed_log='focused-v1-01.log',all12frozen_headers_unchanged=True,all_proof_tokens_unchanged=True,old_unitInterval_and_canaries_unchanged=True,mathematical_repairs=[],fresh_focused_gate_pending=True))
gate('import-comment-proving-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','proving','--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=freeze['headers'],repair='import-comment-repair-v2.json',terminal='guessing_vs_mean_unbounded unchanged',route='same single lower',public_gate_pending=True,chapter_complete=False,goal_complete=False)))
print('Exact failed bytes retained; newly inserted leading doc markers repaired only;12headers/all proof tokens fixed.')
