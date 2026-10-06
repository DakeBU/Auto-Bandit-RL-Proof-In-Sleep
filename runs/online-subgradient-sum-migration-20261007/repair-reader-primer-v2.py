"""Keep all reviewed notation semantics within the actual three-entry reader schema."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;route='online-subgradient-sum';task='ONLINE-SUBGRADIENT-SUM-MIGRATION-20261007'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert load(run/'site-check-v1-01-exit.json')['exit_code']==1
assert 'needs exactly three notation-primer entries' in (run/'site-check-v1-01.log').read_text(encoding='utf-8')
public='BanditRLProof/OnlineSubgradientSum.lean';h=sha(public);assert h==load(run/'public-comment-qualification-v1.json')['qualified_sha256']
p=Path('website/content/readings.json');old=p.read_bytes();snapshot=run/'leaves/reader-before-primer-repair-v2.txt';assert not snapshot.exists();snapshot.write_bytes(old)
d=load(p);x=next(a for a in d['readings'] if a['slug']==route);original=[dict(a) for a in x['notation']];routes=list(x['teaching_route']);assert len(original)==4
before=x['notation'][0]['meaning'];scope=x['notation'][3]['meaning']
x['notation'][0]['meaning']=before+' '+scope
x['notation']=x['notation'][:3]
assert len(x['notation'])==3 and x['teaching_route']==routes and len(routes)==4
prev=json.loads(old.decode('utf-8'));assert [a for a in prev['readings'] if a['slug']!=route]==[a for a in d['readings'] if a['slug']!=route]
for key in prev:
 if key!='readings':assert prev[key]==d[key]
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
assert sha(public)==h
o=run/'reader-primer-repair-v2.json';assert not o.exists();o.write_bytes((json.dumps(dict(status='reader-only repair',failure='site-check-v1-01 requires exactlythree notation primers',before_snapshot=snapshot.as_posix(),before_sha256=hashlib.sha256(old).hexdigest(),after_sha256=sha(p),old_notation=original,new_notation=x['notation'],all_four_meanings_preserved=True,original_four_routes_retained=routes,all_other_Book_subtrees_unchanged=True,public_module_sha256=h,mathematics_changed=False,generator_checker_changed=False,new_current_metadata_gates_pending=True),indent=2)+'\n').encode())
gate('site-primer-repair-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','repair','--payload-json',json.dumps(dict(run_id=run.name,failed_gate='site-check-v1-01',repair='merge space primer into existing M primer; all semantics unchanged',math_changed=False,frozen_terminal_unchanged=True,source_package_accepted=False,chapter_complete=False,goal_complete=False)))
gate('site-primer-repair-candidate-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,reader_only_repair=True,math_gates_still_apply_to_same_public_SHA=h,current_metadata_gates_pending=True,source_package_accepted=False,chapter_complete=False,goal_complete=False)))
print('Actual site-check failure retained; all four meanings merged into three primers. Current metadata gates pending; mathematics fixed.')
